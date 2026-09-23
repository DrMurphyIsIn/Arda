"""Davenport-Heilbronn-type q = 5 mixture  F = a*zeta(s)(1 + sqrt5*5^{-s}) + b*L(s, chi_5).

conjecture1_proved = False.  Trust classes: Arb ball arithmetic (winding, FE samples) and
mpmath floating point (coefficient scans); neither is Lean kernel.

chi_5 is the real even character mod 5 (Legendre symbol, Arb Conrey label 4).  With
a + b = 1 the coefficients c(n) = a(1 + sqrt5 [5|n]) + b chi_5(n) are >= 0 iff a >= |b|
(kernel: `coefDH_nonneg`).  This script:

  1. checks the functional equation (5/pi)^{s/2} Gamma(s/2) F(s) = same at 1 - s at sample
     points (root number +1 of L(s, chi_5): classical, not formalized in Lean);
  2. scans the von Mangoldt coefficients Lambda(n) (solving Lambda * c = c . log) for
     n <= 3000 and several (a, b), reporting the first negative one and comparing with the
     kernel-checked closed forms Lambda(6) = 4ab log 6, Lambda(42) = -8ab(a-b) log 42,
     Lambda(546) = -2 log 546 at a = b;
  3. certifies by a whole-boundary Arb argument-principle count one zero OFF the critical
     line (in 1/2 < sigma < 1, at height ~61) for (a, b) = (1/2, 1/2) and (3/5, 2/5).
     The scout's claim of zeros in sigma > 1 (Bohr / Davenport-Heilbronn) is NOT certified
     here: such zeros need many prime phases aligned and sit far too high to compute;
  4. re-certifies, with whole-segment enclosures, the classical Davenport-Heilbronn crown
     off-line zero box [0.79, 0.83] x [85.68, 85.72] of telperion/docs/QC_DH_SCOUT.md section 4,
     whose original certificate (telperion.arb_dh.winding_number) encloses D only at the
     boundary nodes and so does not by itself exclude extra turning between nodes.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

import mpmath as mp
from flint import acb, arb, ctx, dirichlet_char

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from arb_winding import winding_number  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
CHI = dirichlet_char(5, 4)


def chi5(n: int) -> int:
    r = n % 5
    return 0 if r == 0 else (1 if r in (1, 4) else -1)


def F_arb(a: Fraction, b: Fraction):
    A = arb(a.numerator) / a.denominator
    B = arb(b.numerator) / b.denominator

    def f(s: acb) -> acb:
        return A * s.zeta() * (1 + arb(5).sqrt() * acb(5) ** (-s)) + B * s.dirichlet_l(CHI)
    return f


def Lambda_arb(f, s: acb) -> acb:
    return (acb(5) / arb.pi()) ** (s / 2) * (s / 2).gamma() * f(s)


def vonmangoldt_scan(a: float, b: float, N: int) -> dict:
    mp.mp.dps = 30
    a, b = mp.mpf(a), mp.mpf(b)
    s5 = mp.sqrt(5)
    c = [mp.mpf(0)] + [a * (1 + (s5 if n % 5 == 0 else 0)) + b * chi5(n) for n in range(1, N + 1)]
    divs = [[] for _ in range(N + 1)]
    for d in range(1, N + 1):
        for m in range(2 * d, N + 1, d):
            divs[m].append(d)
    lam = [mp.mpf(0)] * (N + 1)
    for n in range(2, N + 1):
        acc = c[n] * mp.log(n)
        for d in divs[n]:
            if d > 1:
                acc -= lam[d] * c[n // d]
        lam[n] = acc / c[1]
    neg = [n for n in range(2, N + 1) if lam[n] < -mp.mpf(10) ** -20]
    rec = {"a": float(a), "b": float(b), "N": N, "min_coeff": float(min(c[1:])),
           "first_negative_n": neg[0] if neg else None, "count_negative": len(neg),
           "Lambda_6": mp.nstr(lam[6], 20), "Lambda_42": mp.nstr(lam[42], 20),
           "Lambda_12": mp.nstr(lam[12], 20), "Lambda_36": mp.nstr(lam[36], 20),
           "Lambda_546": mp.nstr(lam[546], 20) if N >= 546 else None,
           "closed_form_12 (-4ab(a-b) log 12)": mp.nstr(-4 * a * b * (a - b) * mp.log(12), 20),
           "closed_form_36 (-4ab(1-3(a-b)^2) log 6)":
               mp.nstr(-4 * a * b * (1 - 3 * (a - b) ** 2) * mp.log(6), 20),
           "closed_form_6 (4ab log 6)": mp.nstr(4 * a * b * mp.log(6), 20),
           "closed_form_42 (-8ab(a-b) log 42)": mp.nstr(-8 * a * b * (a - b) * mp.log(42), 20)}
    if a == b:
        rec["closed_form_546 (-2 log 546)"] = mp.nstr(-2 * mp.log(546), 20)
    return rec


def main() -> None:
    ctx.prec = 160
    out = {"conjecture1_proved": False,
           "object": "a*zeta(s)*(1+sqrt5*5^{-s}) + b*L(s,chi_5), a+b=1"}

    # 1. functional equation samples
    fe = []
    for (a, b) in [(Fraction(1, 2), Fraction(1, 2)), (Fraction(3, 5), Fraction(2, 5))]:
        f = F_arb(a, b)
        for (x, y) in [("0.25", "3.0"), ("1.7", "-11.0"), ("0.8", "61.0")]:
            s = acb(arb(x), arb(y))
            d = Lambda_arb(f, 1 - s) - Lambda_arb(f, s)
            fe.append({"a": str(a), "b": str(b), "s": f"{x}+{y}i", "difference": str(d),
                       "contains_zero": bool(d.contains(0))})
    out["functional_equation_samples"] = fe

    # 2. coefficient scans
    out["vonmangoldt_scans"] = [vonmangoldt_scan(a, b, 3000)
                                for (a, b) in [(0.5, 0.5), (0.6, 0.4), (0.9, 0.1), (1.5, -0.5)]]

    # 3. certified off-line zeros
    cert = {}
    boxes = {
        "a=b=1/2": ((Fraction(1, 2), Fraction(1, 2)),
                    (Fraction(70, 100), Fraction(86, 100), Fraction(610, 10), Fraction(613, 10)),
                    "0.779557204771418 + 61.1685166940582i"),
        "a=3/5,b=2/5": ((Fraction(3, 5), Fraction(2, 5)),
                        (Fraction(72, 100), Fraction(88, 100), Fraction(6095, 100), Fraction(6125, 100)),
                        "0.804687966129026 + 61.0835488334575i"),
    }
    for name, ((a, b), (r0, r1, i0, i1), approx) in boxes.items():
        res = winding_number(F_arb(a, b), r0, r1, i0, i1, n_per_side=16, max_depth=16, prec=160)
        res["mpmath_root_inside"] = approx
        res["off_line"] = bool(r0 > Fraction(1, 2))
        cert[name] = res
        print(name, res["winding"], res["winding_interval"])
    out["certified_offline_zeros"] = cert

    # 4. classical DH crown zero, re-certified with whole-segment enclosures
    def dh(s: acb) -> acb:
        s5 = arb(5).sqrt()
        kap = ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)
        z = [s.zeta(acb(r) / 5) for r in (1, 2, 3, 4)]
        return acb(5) ** (-s) * (z[0] + kap * z[1] - kap * z[2] - z[3])
    crown = winding_number(dh, Fraction(79, 100), Fraction(83, 100), Fraction(8568, 100),
                           Fraction(8572, 100), n_per_side=8, max_depth=16, prec=200)
    ctrl = winding_number(dh, Fraction(60, 100), Fraction(70, 100), Fraction(8568, 100),
                          Fraction(8572, 100), n_per_side=8, max_depth=16, prec=200)
    out["classical_DH_crown_recertified"] = {"crown_box": crown, "empty_control_box": ctrl,
                                             "published_zero": "0.8085171825 + 85.6993484854i"}
    print("DH crown:", crown["winding"], "control:", ctrl["winding"])

    with open(os.path.join(HERE, "dh_mixture_check.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    for r in out["vonmangoldt_scans"]:
        print({k: r[k] for k in ("a", "b", "first_negative_n", "count_negative", "Lambda_6",
                                 "Lambda_12", "Lambda_36", "Lambda_42")})
    print("FE contains zero:", [r["contains_zero"] for r in fe])


if __name__ == "__main__":
    main()
