"""WALL-2 / F1: Arb-certified Rouche recurrences of EP5 on the FULL circle (not a grid).  conjecture1_proved = False.

Pattern after Telperion examples/bagchi_recurrence (acb.zeta enclosures, outward rationals), but with ball
arithmetic over arcs so that the certificate covers the continuous circle:
  circle C = {|s - rho0| = r},  rho0 = 0.937666906700 + 29.983395235156 i,  r = 0.04
  EP5(s) = zeta(s) L(s,chi_-20) + L(s,chi_-4) L(s,chi_5)   (= lattice sum of m^2 + 5 n^2, a(1) = 2)
  L(s,chi) = q^{-s} sum_{a=1}^{q} chi(a) zeta(s, a/q)       (Hurwitz, acb.zeta(s, a))
C is covered by K arcs; arc j lies in the complex ball B_j (centre r e^{i phi_j} + rho0, radius r * dphi / 2,
enclosed in a square box).  We certify
  m_lo  := min_j  lower|EP5(B_j)|                > 0
  D_up  := max_j  upper|EP5(B_j + i tau) - EP5(B_j)|
and, ARC BY ARC, upper|EP5(B_j + i tau) - EP5(B_j)| < lower|EP5(B_j)| (pointwise Rouche; the global numbers
m_lo, D_up are reported too).  Then |EP5(s+i tau) - EP5(s)| < |EP5(s)| on all of C, and Rouche gives EP5 a zero in the disc
|s - rho0 - i tau| < r (as many as inside |s - rho0| < r, which is 1 by the argument principle in WALL-1 B).
Arcs failing the inequality are bisected (up to a depth limit).  Trust class: ARB (acb enclosures; no Lean).
The shift tau is a rational chosen by a float local search near WALL-1 B's hits (the certificate is for that tau).
"""
import os, sys
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"
from fractions import Fraction
import numpy as np
import mpmath as mp
from flint import acb, arb, ctx

ctx.prec = 128
RHO_RE, RHO_IM = "0.937666906700", "29.983395235156"
R = 0.04
CH = {
    "m20": (20, [0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1]),
    "m4": (4, [0, 1, 0, -1]),
    "p5": (5, [0, 1, -1, -1, 1]),
}


def L_acb(s, name):
    q, c = CH[name]
    tot = acb(0)
    for a in range(1, q):
        if c[a]:
            tot += c[a] * s.zeta(acb(a) / q)
    return acb(q) ** (-s) * tot


def ep5_acb(s):
    return s.zeta() * L_acb(s, "m20") + L_acb(s, "m4") * L_acb(s, "p5")


def ball(phi_mid, half):
    """square acb box containing the arc {rho0 + r e^{i phi} : |phi - phi_mid| <= half}."""
    rad = R * half * 1.0001 + 1e-15
    cre = float(RHO_RE) + R * np.cos(phi_mid)
    cim = float(RHO_IM) + R * np.sin(phi_mid)
    return acb(arb(cre, rad), arb(cim, rad))


def upper(z):
    return float(z.abs_upper())


def lower(z):
    return float(z.abs_lower())


def certify(tau, K0=256, depth=6):
    """Return (ok, m_lo, D_up, arcs) for the shift tau (an exact rational)."""
    itau = acb(0, arb(tau.numerator) / tau.denominator)
    stack = [(2 * np.pi * (j + 0.5) / K0, np.pi / K0, 0) for j in range(K0)]
    m_lo, D_up, narcs = np.inf, 0.0, 0
    worst = []
    while stack:
        phi, half, d = stack.pop()
        B = ball(phi, half)
        f0 = ep5_acb(B)
        f1 = ep5_acb(B + itau)
        lo = lower(f0)
        du = upper(f1 - f0)
        # local test: if du < lo on this arc we still need the global min; accept arc if du < (global target) later.
        if (du >= lo or not np.isfinite(du)) and d < depth:
            stack += [(phi - half / 2, half / 2, d + 1), (phi + half / 2, half / 2, d + 1)]
            continue
        m_lo = min(m_lo, lo)
        D_up = max(D_up, du)
        narcs += 1
        if du >= lo:
            worst.append((phi, du, lo))
    return len(worst) == 0, m_lo, D_up, narcs, worst


def point(phi, shift=0.0):
    return acb(arb(RHO_RE) + R * arb(np.cos(phi)), arb(RHO_IM) + R * arb(np.sin(phi)) + shift)


def winding(shift_tau=None, K=512):
    """ARB argument principle for EP5 on C (or on C + i tau): each arc's image box must exclude 0 (then its arg span
    is < pi, so the principal arg of f(end)/f(start) is the true increment).  Returns (certified integer or None,
    enclosure of total/2pi).  NB endpoints use the same float phi as the arc boxes, so arcs abut exactly."""
    itau = acb(0) if shift_tau is None else acb(0, arb(shift_tau.numerator) / shift_tau.denominator)
    total = arb(0)
    for j in range(K):
        p0, p1 = 2 * np.pi * j / K, 2 * np.pi * (j + 1) / K
        B = ball(0.5 * (p0 + p1), 0.5 * (p1 - p0)) + itau
        fb = ep5_acb(B)
        if fb.real.contains(0) and fb.imag.contains(0):
            return None, None
        if fb.real.contains(0) or fb.imag.contains(0):
            # box meets an axis but not the origin: still in an open half-plane? check both coordinates' signs
            pass
        a0 = ep5_acb(point(p0) + itau)
        a1 = ep5_acb(point(p1) + itau)
        total += (a1 / a0).arg()
    w = total / (2 * arb.pi())
    n = int(round(float(w.mid())))
    return (n if (w - n).abs_upper() < 0.5 and float(w.rad()) < 0.25 else None), w


def ep5_mp(s):
    q20, c20 = CH["m20"]; q4, c4 = CH["m4"]; q5, c5 = CH["p5"]
    return mp.zeta(s) * mp.dirichlet(s, c20) + mp.dirichlet(s, c4) * mp.dirichlet(s, c5)


def best_tau(t0, width=0.05, n=101, M=64):
    rho0 = mp.mpc(RHO_RE, RHO_IM)
    pts = [rho0 + R * mp.exp(2j * mp.pi * k / M) for k in range(M)]
    base = [ep5_mp(s) for s in pts]
    best = None
    for tau in np.linspace(t0 - width, t0 + width, n):
        sup = max(abs(ep5_mp(s + 1j * tau) - b) for s, b in zip(pts, base))
        if best is None or sup < best[1]:
            best = (tau, float(sup))
    eps0 = float(min(abs(b) for b in base))
    return best[0], best[1], eps0


if __name__ == "__main__":
    mp.mp.dps = 20
    lines = ["Arb Rouche certificates, EP5, circle |s - rho0| = 0.04 (full continuous circle via arc balls; ARB)",
             "tau (rational)      float 64-pt sup   eps0(64pt)   certified D_up   certified m_lo   all arcs ok   arcs"]
    print(lines[0]); print(lines[1], flush=True)
    wn, wenc = winding()
    lines.append(f"ARB winding of EP5 on the base circle: {wn}  (enclosure {wenc})")
    print(lines[-1], flush=True)
    for t0 in (-14.32, 140.14, 340.27, 371.42):
        tau_f, sup_f, eps0 = best_tau(t0)
        tau = Fraction(round(tau_f * 10000), 10000)
        ok, mlo, dup, narcs, worst = certify(tau)
        lines.append(f"{str(tau):>14s}  {sup_f:12.5f}   {eps0:10.5f}   {dup:12.5f}   {mlo:12.5f}    {ok!s:5s}    {narcs}"
                     + ("" if ok else f"  (arcs with du>=lo: {len(worst)})"))
        print(lines[-1], flush=True)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "out", "f1_arb_rouche.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
