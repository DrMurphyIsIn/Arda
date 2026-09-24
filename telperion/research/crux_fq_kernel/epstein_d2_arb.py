"""Arb certification of off-line zeros of the d = 2 Epstein zeta of Q2 = 3m^2 + mn + 3n^2 (disc -35).

conjecture1_proved = False.  Trust class: Arb ball arithmetic (python-flint), NOT Lean kernel.
Single process (no multiprocessing), per the program's memory rule.

What is certified.  Z(s) = zeta(s) L(s, chi_{-35}) - L(s, chi_{-7}) L(s, chi_5) is the Epstein zeta
Sum'_{(m,n) != 0} Q2(m,n)^{-s} of the non-principal form of discriminant -35 (class number 2;
genus-character decomposition).  For each box below, the whole-segment-enclosure argument principle
of research/axiso_literature/arb_winding.py returns a winding number read from an Arb interval that
contains exactly one integer.  A box with winding 1 and left edge > 1/2 certifies an off-line zero.

Checks performed first (numerical, not interval): (i) the Conrey characters used equal the Kronecker
symbols (-7/.), (5/.), (-35/.) for n < 2000; (ii) the decomposition matches the direct lattice sum
at s = 3 (truncated, tail-corrected estimate reported); (iii) the completed FE
(sqrt35/(2 pi))^s Gamma(s) Z(s) = same at 1 - s at one point.
"""
from __future__ import annotations

import json
import os
import sys
import time

from flint import acb, arb, ctx, dirichlet_char

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "axiso_literature"))
from arb_winding import winding_number  # noqa: E402

CHI7 = dirichlet_char(7, 6)     # real character mod 7  = Kronecker (-7/.)
CHI5 = dirichlet_char(5, 4)     # real character mod 5  = Kronecker (5/.)
CHI35 = dirichlet_char(35, 34)  # real character mod 35 = Kronecker (-35/.)


def kronecker(D: int, n: int) -> int:
    def jacobi(a: int, m: int) -> int:
        a %= m
        r = 1
        while a:
            while a % 2 == 0:
                a //= 2
                if m % 8 in (3, 5):
                    r = -r
            a, m = m, a
            if a % 4 == 3 and m % 4 == 3:
                r = -r
            a %= m
        return r if m == 1 else 0
    res = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0:
            return 0
        if D % 8 in (3, 5):
            res = -res
    return res if n == 1 else res * jacobi(D, n)


def Z(s: acb) -> acb:
    return s.zeta() * acb.dirichlet_l(s, CHI35) - acb.dirichlet_l(s, CHI7) * acb.dirichlet_l(s, CHI5)


def check_characters(nmax: int = 2000) -> bool:
    for n in range(1, nmax):
        for c, D in ((CHI7, -7), (CHI5, 5), (CHI35, -35)):
            v = c(n)
            if abs(float(v.real.mid()) - kronecker(D, n)) > 1e-12 or abs(float(v.imag.mid())) > 1e-12:
                return False
    return True


def lattice_sum_s3(R: int = 300) -> float:
    tot = 0.0
    for m in range(-R, R + 1):
        for n in range(-R, R + 1):
            if m == 0 and n == 0:
                continue
            q = 3 * m * m + m * n + 3 * n * n
            tot += q ** -3.0
    return tot


def main() -> dict:
    ctx.prec = 128
    out: dict = {"conjecture1_proved": False,
                 "function": "Z(s) = zeta(s) L(s,chi_-35) - L(s,chi_-7) L(s,chi_5)  (Epstein zeta of 3m^2+mn+3n^2)",
                 "trust": "Arb ball arithmetic, whole-segment enclosures (arb_winding.py); NOT Lean kernel"}
    out["characters_match_kronecker_n_lt_2000"] = check_characters()
    t0 = time.time()
    ls = lattice_sum_s3(300)
    zs = Z(acb(3))
    out["lattice_sum_s3_R300"] = ls
    out["decomposition_s3"] = float(zs.real.mid())
    out["decomposition_minus_lattice_s3"] = float(zs.real.mid()) - ls
    s0 = acb("0.3", "7.1")
    lam = lambda s: (arb(35).sqrt() / (2 * arb.pi())) ** s * s.gamma() * Z(s)
    out["completed_FE_defect_at_0.3+7.1i"] = str(abs(lam(s0) - lam(1 - s0)))
    boxes = [
        ("rho1", "0.76", "0.80", "19.30", "19.35"),
        ("rho1_partner", "0.20", "0.24", "19.30", "19.35"),
        ("rho2", "0.63", "0.67", "55.87", "55.92"),
        ("rho3", "0.61", "0.645", "78.63", "78.67"),
        ("rho4", "0.81", "0.845", "92.40", "92.45"),
        ("rho5", "0.56", "0.59", "101.11", "101.16"),
    ]
    res = []
    for name, a, b, c, d in boxes:
        t = time.time()
        try:
            w = winding_number(Z, a, b, c, d, n_per_side=16, max_depth=14, prec=128)
            w["name"] = name
            w["off_line"] = float(a) > 0.5 or float(b) < 0.5
            w["seconds"] = round(time.time() - t, 1)
        except RuntimeError as e:
            w = {"name": name, "box": [a, b, c, d], "error": str(e)}
        res.append(w)
        print(name, w, flush=True)
    out["boxes"] = res
    out["total_seconds"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":
    result = main()
    path = os.path.join(HERE, "epstein_d2_arb.json")
    with open(path, "w") as fh:
        json.dump(result, fh, indent=2)
    print(json.dumps({k: v for k, v in result.items() if k != "boxes"}, indent=2))
