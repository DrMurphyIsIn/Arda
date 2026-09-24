"""Extrapolate measured kernel costs to the full h280000 capstone and the 1e6 target.

Measured inputs (this session, M3 Ultra 32 cores / 96 GB, Lean v4.32.0, decide +kernel):
  * certified single-point evaluator: 227-256 us per Dirichlet term (flat in t; 297 at t=100 where
    the slow-path log/sqrt for small n dominate); peak RSS 1.8 GB per process (500-term chunks,
    40 chunks per module), assembly module 3.1 GB.
  * rotor cost proxy (shared partial sums over a uniform grid of G points in a band):
    254 us per n + 67 us per (n, grid point).
Workload model:
  * H1 (hLine): per band, G = N_zeros + 1 sign evaluations of Z on the line (all points of a band
    use the EM cut N of the band top).
  * H2 edges + caps: per distinct edge height, G_edge off-line evaluations (sigma in [0,1] after
    the functional-equation reflection, so cost <= the on-line cost at the same height).
  * generic families (H2b, H2d, H2f, H3): O(1) per band or a one-off net -> negligible.
EM cut N(t, eps):
  * order 3 (the island's em_zeta_critical_line3_enclosure): |s(s+1)(s+2)| / (180 N^{5/2}) <= eps.
  * order k = 2K+1 (general EM, NOT formalized): 2 zeta(k)/(2 pi)^k |(s)_k| N^{-(k-1/2)}/(k-1/2) <= eps,
    optimized over K <= 40.
  * Riemann-Siegel (NOT formalized): floor(sqrt(t / 2 pi)) terms.
conjecture1_proved = False.
"""
import json
import math
import sys

C_TERM = 230e-6        # s per term, certified single-point (measured 227-256)
ROT_N = 254e-6         # s per n, rotor (measured)
ROT_PT = 67e-6         # s per (n, point), rotor (measured)
CORES = 32
EFF = 0.9              # parallel efficiency (independent chunks; measured 4-lane runs ~0.9)


def pabs(t, sigma, k):
    """|s (s+1) ... (s+k-1)| for s = sigma + i t"""
    p = 1.0
    for j in range(k):
        p *= math.hypot(sigma + j, t)
    return p


def N_order3(t, eps):
    A = pabs(t, 0.5, 3) / 180.0
    return max(2, math.ceil((A / eps) ** 0.4))


_ZI = {}


def zeta_int(k):
    if k not in _ZI:
        _ZI[k] = sum(1.0 / n ** k for n in range(1, 200))
    return _ZI[k]


_NK = {}


def N_highorder(t, eps, Kmax=40):
    key = (round(t, 2), eps)
    if key in _NK:
        return _NK[key]
    best = None
    for K in range(1, Kmax + 1):
        k = 2 * K + 1
        # N^{k-1/2} >= coef/eps  (log domain: pabs(t,0.5,k) overflows for large k at large t)
        lg = math.log(2 * zeta_int(k)) - k * math.log(2 * math.pi) + sum(math.log(math.hypot(0.5 + j, t)) for j in range(k)) - math.log(k - 0.5)
        N = math.exp((lg - math.log(eps)) / (k - 0.5))
        N = max(int(N) + 1, 2)
        if best is None or N < best[0]:
            best = (N, K)
    _NK[key] = best
    return best


def N_rs(t):
    return int(math.sqrt(t / (2 * math.pi))) + 1


def zeros_up_to(T):
    if T < 14:
        return 0.0
    x = T / (2 * math.pi)
    return x * math.log(x) - x + 7.0 / 8


def synth_bands(T0, T1, per_band=42.0):
    """synthetic bands above the emitted ladder: ~42 zeros per band (the campaign's policy)."""
    out = []
    T = T0
    while T < T1:
        dens = math.log(T / (2 * math.pi)) / (2 * math.pi)
        w = min(40.0, per_band / dens)
        b = min(T + w, T1)
        out.append((T, b, int(round(zeros_up_to(b) - zeros_up_to(T)))))
        T = b
    return out


def cost(bands, edges, eps, method, G_edge):
    on = 0.0
    ed = 0.0
    terms = 0.0
    for (a, b, nz) in bands:
        G = nz + 1
        if method == "em3":
            N = N_order3(b, eps)
        elif method == "emK":
            N = N_highorder(b, eps)[0]
        else:
            N = N_rs(b)
        terms += G * N
        on += G * N * C_TERM
    for T in edges:
        if method == "em3":
            N = N_order3(T, eps)
        elif method == "emK":
            N = N_highorder(T, eps)[0]
        else:
            N = N_rs(T)
        ed += G_edge * N * C_TERM
    return on, ed, terms


def cost_rotor(bands, eps, method):
    on = 0.0
    for (a, b, nz) in bands:
        G = nz + 1
        N = N_order3(b, eps) if method == "em3" else (N_highorder(b, eps)[0] if method == "emK" else N_rs(b))
        on += N * (ROT_N + G * ROT_PT)
    return on


def fmt(sec):
    ch = sec / 3600.0
    wall_days = sec / (CORES * EFF) / 86400.0
    return "%.3g core-h (%.3g core-years), %.3g days on %d cores" % (ch, ch / 8766.0, wall_days, CORES)


def main():
    data = json.load(open("bands_h280000.json"))
    bands = [tuple(x) for x in data["bands"]]
    edges = data["edges"]
    b6 = bands + synth_bands(280000.0, 1.0e6)
    e6 = sorted(set(edges) | {x[0] for x in b6} | {x[1] for x in b6})
    res = {}
    print("bands h280000:", len(bands), "zeros", sum(x[2] for x in bands), "edges", len(edges))
    print("bands 1e6:", len(b6), "zeros", sum(x[2] for x in b6), "edges", len(e6))
    for t in (100, 1000, 1e4, 3e4, 1e5, 2.8e5, 1e6):
        print("t=%g: N3(1e-2)=%d N3(1e-3)=%d NK(1e-2)=%s NK(1e-3)=%s NRS=%d" % (
            t, N_order3(t, 1e-2), N_order3(t, 1e-3), N_highorder(t, 1e-2), N_highorder(t, 1e-3), N_rs(t)))
    for tgt, B, E in (("h280000", bands, edges), ("1e6", b6, e6)):
        for eps in (1e-2, 1e-3):
            for method in ("em3", "emK", "rs"):
                for Ge in (60, 100):
                    on, ed, terms = cost(B, E, eps, method, Ge)
                    rot = cost_rotor(B, eps, method)
                    key = "%s eps=%g %s Gedge=%d" % (tgt, eps, method, Ge)
                    res[key] = dict(online_s=on, edges_s=ed, rotor_online_s=rot, online_terms=terms)
                    print(key)
                    print("   on-line single-point : " + fmt(on) + "   [%.3g terms]" % terms)
                    print("   on-line rotor(proxy) : " + fmt(rot))
                    print("   edges+caps           : " + fmt(ed))
                    print("   TOTAL single-point   : " + fmt(on + ed))
                    print("   TOTAL rotor + edges  : " + fmt(rot + ed))
    json.dump(res, open("extrapolation.json", "w"), indent=1)


if __name__ == "__main__":
    main()
