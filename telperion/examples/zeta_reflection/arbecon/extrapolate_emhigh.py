"""Updated extrapolation (lane emhigh): kernel cost of ALL 445,947 on-line sign evaluations of the
h280000 capstone with the order-(2K+1) Euler-Maclaurin evaluator.

What changed against the economics seat's extrapolate.py (memo section 3.2/3.3):
  * the remainder is the PROVED odd-saw bound `EMZetaHigh.em_line_remainder_odd_le` as certified by
    `EMZetaHighCheck.remOdd` (general K; pi replaced by 3.141592 < pi < 3.141593):
        E_K(t, N) = 2 (1 + (pi^2/6 - 1)/2^(2K-1)) / (2 pi)^(2K+1) * Q / (N^(2K) r) / (2K + 1/2),
        Q >= |(1/2+it)_(2K+1)|,  r = isqrt N
    (the even-saw form `em_line_remainder_le`, |B_2K|/(2K)! * Q' / (N^(2K-1) r) / (2K - 1/2), needs about
    7 percent more terms; the seat used the unformalized 2 zeta(2K+1)/(2 pi)^(2K+1) constant);
  * K <= 6 (the lane's cap; B_2 .. B_12 are proved exactly in EMZetaHigh);
  * c_term is MEASURED on the order-13 instances (tuned config lnbig = sqbig = 256, odd certificate):
        t = 10000 (N = 3212): 224 us, t = 30000 (N = 10059): 222 us, t = 280000 (N = 102641): 231 us;
  * the per-evaluation assembly is ONE `decide +kernel` of EMZetaHighCheck.checkK: 8.1 - 9.4 ms measured
    (the norm_num assembly measured 110 ms kernel + about 3 s of tactic elaboration + 1.3 MB olean);
  * olean bytes per evaluation (kernel format, measured): about 50 KB + 11.5 KB per 500-term chunk.

Workload: bands_h280000.json (arbecon/extract_bands.py over AllZeros_h1000..h280000): 10,379 bands,
G = N_zeros + 1 sign evaluations per band (445,947 in total), every point of a band evaluated at the
band-top height (valid: the remainder bound is monotone in t).  Off-line (edge/cap) work is NOT in this
count (the evaluator is critical-line only; memo H2a/H2c/H2e need a general-sigma amplitude).

usage: extrapolate_emhigh.py [bands_h280000.json] [out.json]
conjecture1_proved = False.
"""
import json
import math
import sys
from fractions import Fraction

BERN = {2: Fraction(1, 6), 4: Fraction(-1, 30), 6: Fraction(1, 42), 8: Fraction(-1, 30), 10: Fraction(5, 66),
        12: Fraction(-691, 2730)}
C_TERM = 226e-6          # s per Dirichlet term (mean of 224 / 222 / 231 us measured, order 13)
C_TERM_RANGE = (218e-6, 232e-6)   # all order-13 measurements (even and odd certificates)
C_CHECK = 9.4e-3         # s kernel per evaluation for the checkK decide (max measured)
C_TERM_EM3 = 230e-6      # order-3 baseline c_term (economics seat)
CHUNK = 500
BYTES_FIXED = 50e3       # kernel-format olean bytes per evaluation, fixed part (measured 46-62 KB)
BYTES_CHUNK = 11.5e3     # per 500-term chunk: state def (~8.6 KB) + chunk thm (~1.6 KB) + inv thm (~1.2 KB)
CORES, EFF = 32, 0.9


def log_E_even(K, t, N):
    """ln of the proved even-saw bound (em_line_remainder_le), Q = exact norm, r = isqrt N."""
    lq = 0.5 * sum(math.log((0.5 + j) ** 2 + t * t) for j in range(2 * K))
    return (math.log(abs(float(BERN[2 * K]))) - math.lgamma(2 * K + 1) + lq
            - (2 * K - 1) * math.log(N) - math.log(math.isqrt(N)) - math.log(2 * K - 0.5))


def log_E_odd(K, t, N):
    """ln of the certified odd-saw bound (remOdd: pi -> 3.141592 / 3.141593), Q exact, r = isqrt N."""
    lq = 0.5 * sum(math.log((0.5 + j) ** 2 + t * t) for j in range(2 * K + 1))
    c = 2 * (1 + (3.141593 ** 2 / 6 - 1) / 2 ** (2 * K - 1)) / 6.283184 ** (2 * K + 1)
    return (math.log(c) + lq - (2 * K) * math.log(N) - math.log(math.isqrt(N)) - math.log(2 * K + 0.5))


def N_K(K, t, eps, odd=True):
    """minimal N with E_K(t, N) <= eps (float, 1e-9 relative safety)."""
    f = log_E_odd if odd else log_E_even
    target = math.log(eps) - 1e-9
    m = 2 * K + 0.5 if odd else 2 * K - 0.5
    N = max(2, int(math.exp((f(K, t, 1) - math.log(eps)) / m)))
    while f(K, t, N) > target:
        N += 1
    while N > 2 and f(K, t, N - 1) <= target:
        N -= 1
    return N


def N_em3(t, eps):
    p = 1.0
    for j in range(3):
        p *= math.hypot(0.5 + j, t)
    return max(2, math.ceil((p / (180.0 * eps)) ** 0.4))


def fmt_s(sec):
    return "%.3g core-h = %.3g core-days = %.3g days wall on %d cores (eff %.1f)" % (
        sec / 3600, sec / 86400, sec / (CORES * EFF) / 86400, CORES, EFF)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "bands_h280000.json"
    out = sys.argv[2] if len(sys.argv) > 2 else "extrapolation_emhigh.json"
    data = json.load(open(path))
    bands = [tuple(x) for x in data["bands"]]
    G_total = sum(nz + 1 for (_, _, nz) in bands)
    res = dict(bands=len(bands), evaluations=G_total)
    print("h280000: %d bands, %d on-line sign evaluations" % (len(bands), G_total))
    # spot-check the float N_K against the exact rational bound of gen_emhigh.remainder
    try:
        sys.path.insert(0, ".")
        import gen_emhigh_k as g
        for (t, eps) in ((10000, 1e-3), (30000, 1e-3), (280000, 1e-3), (100000, 1e-2)):
            for odd in (True, False):
                Nf, Ne = N_K(6, t, eps, odd), g.minimal_N(6, t, eps, odd)
                assert Ne <= Nf <= Ne + 1, (t, eps, odd, Nf, Ne)
        res["N_formula_checked"] = True
    except ImportError:
        res["N_formula_checked"] = False
    print("per-height N (K = 6, proved odd-saw certificate; even-saw in brackets):")
    for t in (1000, 10000, 30000, 100000, 280000):
        print("   t = %-7d N(1e-2) = %-7d N(1e-3) = %-7d [%d] N(1e-4) = %-7d | order-3 N(1e-3) = %d" % (
            t, N_K(6, t, 1e-2), N_K(6, t, 1e-3), N_K(6, t, 1e-3, False), N_K(6, t, 1e-4), N_em3(t, 1e-3)))
    for eps in (1e-2, 1e-3, 1e-4):
        terms = 0
        chunks = 0
        terms3 = 0
        byK = {K: 0 for K in range(3, 7)}
        terms_even = 0
        for (a, b, nz) in bands:
            G = nz + 1
            N = N_K(6, b, eps)
            terms += G * N
            chunks += G * math.ceil(N / CHUNK)
            terms3 += G * N_em3(b, eps)
            terms_even += G * N_K(6, b, eps, False)
            for K in byK:
                byK[K] += G * N_K(K, b, eps)
        kern = terms * C_TERM + G_total * C_CHECK
        lo = terms * C_TERM_RANGE[0] + G_total * C_CHECK
        hi = terms * C_TERM_RANGE[1] + G_total * C_CHECK
        kern3 = terms3 * C_TERM_EM3
        disk = G_total * BYTES_FIXED + chunks * BYTES_CHUNK
        key = "eps=%g" % eps
        res[key] = dict(terms=terms, chunks=chunks, kernel_s=kern, kernel_s_range=[lo, hi],
                        kernel_s_em3=kern3, speedup_vs_em3=kern3 / kern, olean_bytes=disk,
                        mean_N=terms / G_total, terms_by_K={str(k): v for k, v in byK.items()},
                        terms_even_saw=terms_even)
        print("eps = %g:" % eps)
        print("   order 13 (K = 6): %.4g terms, mean N %.0f, %.4g chunks" % (terms, terms / G_total, chunks))
        print("      kernel: " + fmt_s(kern) + "   [c_term range: %.3g - %.3g core-days]" % (lo / 86400, hi / 86400))
        print("      of which checkK assemblies: %.3g core-h" % (G_total * C_CHECK / 3600))
        print("      olean (kernel format, 500-term chunks): %.3g TB" % (disk / 1e12))
        print("   order 3 (baseline):  %.4g terms -> " % terms3 + fmt_s(kern3) + "  (x%.0f)" % (kern3 / kern))
        print("   K sensitivity (terms): " + ", ".join("K=%d: %.3g" % (k, v) for k, v in byK.items())
              + "; even-saw K=6: %.3g" % terms_even)
    json.dump(res, open(out, "w"), indent=1)


if __name__ == "__main__":
    main()
