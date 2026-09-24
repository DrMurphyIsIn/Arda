"""Arb (python-flint) certification of the off-line zeros used by the negative-control seat.

conjecture1_proved = False.  Trust class: Arb ball arithmetic with segment-certified winding
numbers (arb_winding.py, a self-contained copy of the crux_dynamics-ergodic tool), NOT the Lean
kernel.  Single process, no pools.

What is certified here (each "winding 1" box lies strictly inside Re s > 1/2, so its zero is OFF the
critical line):
  (1) NEW.  Epstein zeta of x^2 + 5y^2, E_Q(s) = sum'_{(x,y) != 0} (x^2+5y^2)^{-s}
      = zeta L(chi_-20) + L(chi_-4) L(chi_5) (genus identity; coefficient r_Q(n), r_Q(1) = 2),
      has a SECOND off-line zero near 0.9376669067 + 29.9833952352 i.  The seat found it numerically;
      the corpus (Build C) had certified only the zero near 0.9330 + 15.6682 i.
  (2) NEW.  W2's finite factor E_a(s) = 1 + a (101^{1/2-s} + 10007^{1/2-s}) + (101*10007)^{1/2-s},
      a = 1 + 10^-4, has off-line zeros near heights 162.690, 164.053, 165.416 (so W2 = zeta E_a does).
  (3) NEW.  E_a has NO off-line zero with 0.1 < Im s < 150: the certified winding number of the box
      [-1/2, 3/2] x [1/10, 150] equals the number of certified sign changes of the real function
      f(t) = cos(t (L1+L2)/2) + a cos(t (L2-L1)/2) on (1/10, 150), where E_a(1/2+it) = 2 e^{-it(L1+L2)/2} f(t).
      (No zero of E_a has |Re s - 1/2| >= 1: |E_a| >= 1 - a/101 - a/10007 - 1/1010707 there.)
      So a finite window of real zeros (here: all 300+ zeros below height 150) does not certify
      Lee-Yang; the Lean file proves LY2 a is Lee-Yang iff |a| <= 1.
  (4) Positive controls of the tool: the corpus' certified Epstein zero near 15.668 and the
      Davenport-Heilbronn zero near 0.8085 + 85.6993 i are re-certified; control boxes give 0.
Output: out/certify_offline_zeros.json (and stdout).
"""
from __future__ import annotations

import json
import time
from fractions import Fraction as Fr

from flint import acb, arb, ctx

from arb_winding import winding_number

ctx.prec = 200


# ---------------- evaluators (Arb) ----------------

def _chi_m4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def _chi_5(n):
    r = n % 5
    return 0 if r == 0 else (1 if r in (1, 4) else -1)


def _chi_m20(n):
    return _chi_m4(n) * _chi_5(n)


def dirichlet_L(s: acb, chi, q: int) -> acb:
    tot = acb(0)
    for a in range(1, q + 1):
        c = chi(a)
        if c:
            tot += c * s.zeta(acb(a) / q)
    return acb(q) ** (-s) * tot


def epstein_x2_5y2(s: acb) -> acb:
    """sum'_{(x,y) != 0} (x^2+5y^2)^{-s} = zeta(s) L(s,chi_-20) + L(s,chi_-4) L(s,chi_5) (genus theory,
    h = 2, two units: zeta_K = (Z_Q1 + Z_Q2)/2 and L(chi_-4) L(chi_5) = (Z_Q1 - Z_Q2)/2)."""
    return s.zeta() * dirichlet_L(s, _chi_m20, 20) + dirichlet_L(s, _chi_m4, 4) * dirichlet_L(s, _chi_5, 5)


_sq5 = arb(5).sqrt()
DH_KAPPA = ((arb(10) - 2 * _sq5).sqrt() - 2) / (_sq5 - 1)


def dh(s: acb) -> acb:
    return acb(5) ** (-s) * (s.zeta(acb(1) / 5) + DH_KAPPA * s.zeta(acb(2) / 5)
                             - DH_KAPPA * s.zeta(acb(3) / 5) - s.zeta(acb(4) / 5))


P1, P2 = 101, 10007
A_W2 = arb(10001) / 10000          # a = 1 + 10^-4, exactly
HALF = arb(1) / 2


def Ea(s: acb) -> acb:
    return (1 + A_W2 * (acb(P1) ** (HALF - s) + acb(P2) ** (HALF - s))
            + acb(P1 * P2) ** (HALF - s))


def f_line(t: arb) -> arb:
    """E_a(1/2 + it) = 2 e^{-it(L1+L2)/2} f(t)."""
    L1, L2 = arb(P1).log(), arb(P2).log()
    return (t * (L1 + L2) / 2).cos() + A_W2 * (t * (L2 - L1) / 2).cos()


def newton(f, s, steps=30):
    h = acb("1e-30")
    for _ in range(steps):
        v = f(s)
        d = (f(s + h) - v) / h
        s = s - v / d
        s = acb(s.real.mid(), s.imag.mid())
    return s


def certified_sign_changes(f, t0: Fr, t1: Fr, n: int):
    """Number of sign changes of f on the rational grid t0 + (t1-t0) k/n, each sign certified by Arb.
    Returns (count, uncertified_points)."""
    prev = None
    count = 0
    bad = 0
    for k in range(n + 1):
        t = t0 + (t1 - t0) * Fr(k, n)
        v = f(arb(t.numerator) / arb(t.denominator))
        if v > 0:
            sg = 1
        elif v < 0:
            sg = -1
        else:
            bad += 1
            continue
        if prev is not None and sg != prev:
            count += 1
        prev = sg
    return count, bad


def main():
    out = {"trust_class": "Arb ball arithmetic (python-flint 0.6, prec 200), segment-certified winding "
                          "numbers; not a Lean kernel proof",
           "conjecture1_proved": False, "certificates": [], "checks": []}

    # sanity: genus identity vs direct lattice sum at s = 3 (non-rigorous lattice truncation)
    import mpmath as mp
    mp.mp.dps = 20
    lat = mp.mpf(0)
    M = 150
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            if x or y:
                lat += mp.mpf(x * x + 5 * y * y) ** (-3)
    out["checks"].append({"what": "E_Q(3): genus identity vs direct lattice sum over |x|,|y| <= 150 "
                                  "(non-rigorous truncation, tail ~1e-6)",
                          "genus": epstein_x2_5y2(acb(3)).real.str(15), "lattice": mp.nstr(lat, 15)})

    jobs = [
        ("NEW: Epstein x^2+5y^2, second off-line zero", epstein_x2_5y2, acb("0.9376669067", "29.98339523"),
         (Fr(90, 100), Fr(97, 100), Fr(2995, 100), Fr(3002, 100))),
        ("NEW: Epstein x^2+5y^2, right half-strip [0.52,2]x[20,30.85] contains exactly one zero",
         epstein_x2_5y2, None, (Fr(52, 100), Fr(2), Fr(20), Fr(3085, 100))),
        ("control: Epstein x^2+5y^2, box left of the second zero (no zero)", epstein_x2_5y2, None,
         (Fr(60, 100), Fr(66, 100), Fr(2995, 100), Fr(3002, 100))),
        ("positive control of the tool (corpus Build C): Epstein x^2+5y^2 first off-line zero",
         epstein_x2_5y2, acb("0.93297", "15.66825"), (Fr(90, 100), Fr(96, 100), Fr(1564, 100), Fr(1570, 100))),
        ("positive control of the tool (corpus): Davenport-Heilbronn off-line zero", dh,
         acb("0.8085", "85.6993"), (Fr(79, 100), Fr(83, 100), Fr(8568, 100), Fr(8572, 100))),
        ("NEW: W2 factor E_a, a=1+1e-4, off-line zero near 162.690", Ea, acb("0.501942745874", "162.69048446"),
         (Fr(5005, 10000), Fr(5040, 10000), Fr(16266, 100), Fr(16272, 100))),
        ("NEW: W2 factor E_a, its FE partner 1 - conj(rho) near 162.690", Ea, acb("0.498057254126", "162.69048446"),
         (Fr(4960, 10000), Fr(4995, 10000), Fr(16266, 100), Fr(16272, 100))),
        ("NEW: W2 factor E_a, off-line zero near 164.053", Ea, acb("0.502120898512", "164.053338136"),
         (Fr(5005, 10000), Fr(5040, 10000), Fr(16402, 100), Fr(16408, 100))),
        ("NEW: W2 factor E_a, off-line zero near 165.416", Ea, acb("0.50109304566", "165.416191812"),
         (Fr(5002, 10000), Fr(5030, 10000), Fr(16538, 100), Fr(16544, 100))),
    ]
    for lab, f, guess, box in jobs:
        t0 = time.time()
        rec = {"function": lab}
        if guess is not None:
            z = newton(f, guess)
            rec["located_zero"] = [z.real.mid().str(20), z.imag.mid().str(20)]
            rec["enclosure_of_f_at_located_point"] = str(f(z))
        rec["box"] = winding_number(f, *box, n_per_side=8, max_depth=22)
        rec["seconds"] = round(time.time() - t0, 1)
        out["certificates"].append(rec)
        print(json.dumps(rec), flush=True)

    # (3) all zeros of E_a with 0.1 < t < 150 are on the line
    t0 = time.time()
    box = winding_number(Ea, Fr(-1, 2), Fr(3, 2), Fr(1, 10), Fr(150), n_per_side=64, max_depth=22)
    sc, bad = certified_sign_changes(f_line, Fr(1, 10), Fr(150), 150000)
    rec = {"function": "W2 factor E_a on [-1/2,3/2] x [1/10,150]: winding vs certified on-line sign changes",
           "box": box, "certified_sign_changes_of_f_on_(1/10,150)_grid_1e-3": sc,
           "grid_points_with_uncertified_sign": bad,
           "conclusion": ("ALL zeros of E_a with 1/10 < Im s < 150 lie on Re s = 1/2 (count = sign changes)"
                          if box["winding"] == sc and bad == 0 else "INCONCLUSIVE"),
           "seconds": round(time.time() - t0, 1)}
    out["certificates"].append(rec)
    print(json.dumps(rec), flush=True)
    import os
    os.makedirs("out", exist_ok=True)
    with open("out/certify_offline_zeros.json", "w") as fh:
        json.dump(out, fh, indent=2)
    for c in out["checks"]:
        print(json.dumps(c))


if __name__ == "__main__":
    main()
