"""E8 normalization witness G(s) = zeta(s/2 + 7/4) zeta(s/2 - 5/4): Arb certificates.

conjecture1_proved = False.  Trust class: Arb ball arithmetic (python-flint 0.6), not kernel.

What is certified here (complements the kernel-checked Lean theorems in
examples/li_positivity/lean/Crux/Crux_axiso_literature.lean, section C):

  1. zeta has a zero rho_1 = 1/2 + i*gamma_1 with gamma_1 in an Arb ball of radius < 1e-30
     (acb.zeta_zero(1), Arb's certified zero isolation), and independently a sign change of
     the real function Lambda_zeta(1/2 + it) on [14.1347, 14.1348].
     Lean `GE8_zero_of_zeta_zero` then gives G(2 rho_1 + 5/2) = 0 with Re = 7/2.
  2. A whole-boundary argument-principle count: exactly one zero of G in the box
     [3.3, 3.7] x [28.1, 28.4] (Re s = 3.5 != 1/2), exactly one in the mirror box
     [-2.7, -2.3] x [-28.4, -28.1], and none in the box [0.3, 0.7] x [28.1, 28.4] that
     straddles the critical line at the same height.
  3. The functional equation Lambda_G(1 - s) = Lambda_G(s), Lambda_G = Gamma_C(s/2+7/4) G(s),
     at sample points (the enclosure of the difference contains 0).  Lean proves it for all s.
  4. P2 for G (integer-frequency form): the von Mangoldt coefficients of
     zeta(w) zeta(w-3) = sum sigma_3(n) n^{-w} are exactly Lambda(n)(1 + n^3) >= 0 for n <= N,
     computed in exact arithmetic (logs as integer vectors over the primes).
     In the Beurling variable s (frequencies sqrt n) the log-coefficient at the g-prime power
     p^{k/2} is (p^{-7k/4} + p^{5k/4})/k > 0; positivity does not depend on the rescaling.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

from flint import acb, arb, ctx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from arb_winding import winding_number  # noqa: E402

ctx.prec = 160
HERE = os.path.dirname(os.path.abspath(__file__))


def G(s: acb) -> acb:
    return (s / 2 + acb(7) / 4).zeta() * (s / 2 - acb(5) / 4).zeta()


def gamma_C(w: acb) -> acb:
    two_pi = 2 * arb.pi()
    return 2 * acb(two_pi) ** (-w) * w.gamma()


def Lambda_G(s: acb) -> acb:
    return gamma_C(s / 2 + acb(7) / 4) * G(s)


def lambda_zeta_on_line(t: str) -> acb:
    s = acb(arb(1) / 2, arb(t))
    return acb(arb.pi()) ** (-s / 2) * (s / 2).gamma() * s.zeta()


def exact_vonmangoldt_sigma3(N: int) -> dict:
    """Solve L * sigma_3 = log . sigma_3 exactly; logs are integer vectors over primes."""
    import math
    sig3 = [0] * (N + 1)
    for d in range(1, N + 1):
        for m in range(d, N + 1, d):
            sig3[m] += d ** 3
    spf = list(range(N + 1))
    for p in range(2, int(N ** 0.5) + 1):
        if spf[p] == p:
            for m in range(p * p, N + 1, p):
                if spf[m] == m:
                    spf[m] = p

    def logvec(n):
        v = {}
        while n > 1:
            p = spf[n]
            v[p] = v.get(p, 0) + 1
            n //= p
        return v

    def add(acc, vec, c):
        for p, e in vec.items():
            acc[p] = acc.get(p, 0) + c * e
            if acc[p] == 0:
                del acc[p]

    divs = [[] for _ in range(N + 1)]
    for d in range(1, N + 1):
        for m in range(2 * d, N + 1, d):
            divs[m].append(d)
    L = [dict() for _ in range(N + 1)]
    mismatches = []
    for n in range(2, N + 1):
        acc = {}
        add(acc, logvec(n), sig3[n])
        for d in divs[n]:
            if L[d]:
                add(acc, L[d], -sig3[n // d])
        L[n] = acc
        # expected: n = p^k -> {p: 1 + n^3}; else 0
        lv = logvec(n)
        if len(lv) == 1:
            p = next(iter(lv))
            expected = {p: 1 + n ** 3}
        else:
            expected = {}
        if acc != expected:
            mismatches.append(n)
    return {"N": N, "identity": "Lambda_{zeta(w)zeta(w-3)}(n) = Lambda(n) * (1 + n^3)",
            "mismatches": mismatches, "all_nonnegative": not mismatches}


def main() -> None:
    out = {"conjecture1_proved": False,
           "object": "G(s) = zeta(s/2 + 7/4) * zeta(s/2 - 5/4)"}

    # 1. certified first zeta zero, and an independent sign change of Lambda_zeta on the line
    z1 = acb.zeta_zero(1)
    out["zeta_zero_1"] = {"enclosure": str(z1),
                          "method": "acb.zeta_zero(1) (Arb certified isolation)"}
    lo, hi = lambda_zeta_on_line("14.1347"), lambda_zeta_on_line("14.1348")
    out["lambda_zeta_sign_change"] = {
        "Lambda(1/2+14.1347i)": str(lo), "Lambda(1/2+14.1348i)": str(hi),
        "opposite_signs": bool((lo.real > 0 and hi.real < 0) or (lo.real < 0 and hi.real > 0)),
        "note": "Lambda_zeta(1/2+it) is real (FE + Schwarz reflection); sign change => zero"}
    s_star = 2 * z1 + acb(5) / 2
    out["G_zero_from_rho1"] = {
        "point_2rho1_plus_5_2": str(s_star),
        "G_enclosure_there": str(G(s_star)),
        "re": "7/2 exactly (Re rho_1 = 1/2), so off the critical line"}

    # 2. whole-boundary zero counts
    boxes = {
        "offline_zero_box": (Fraction(33, 10), Fraction(37, 10), Fraction(281, 10), Fraction(284, 10)),
        "mirror_zero_box": (Fraction(-27, 10), Fraction(-23, 10), Fraction(-284, 10), Fraction(-281, 10)),
        "critical_line_control_box": (Fraction(3, 10), Fraction(7, 10), Fraction(281, 10), Fraction(284, 10)),
    }
    out["winding"] = {}
    for name, (a, b, c, d) in boxes.items():
        res = winding_number(G, a, b, c, d, n_per_side=16, max_depth=16, prec=160)
        out["winding"][name] = res
        print(name, res["winding"], res["winding_interval"])

    # 3. functional equation at sample points
    fe = []
    for (x, y) in [("0.3", "5.0"), ("2.0", "-7.5"), ("-1.1", "13.25"), ("0.5", "28.0")]:
        s = acb(arb(x), arb(y))
        diff = Lambda_G(1 - s) - Lambda_G(s)
        fe.append({"s": f"{x}+{y}i", "Lambda_G(s)": str(Lambda_G(s)),
                   "Lambda_G(1-s)-Lambda_G(s)": str(diff), "contains_zero": bool(diff.contains(0))})
    out["functional_equation_samples"] = fe

    # 4. P2 for G in exact arithmetic
    out["P2_integer_frequency_form"] = exact_vonmangoldt_sigma3(2000)
    beur = []
    for p in (2, 3, 5, 7):
        for k in (1, 2, 3):
            val = (arb(p) ** (arb(-7 * k) / 4) + arb(p) ** (arb(5 * k) / 4)) / k
            beur.append({"g_prime_power": f"({p}^(1/2))^{k}", "log_coefficient": str(val),
                         "positive": bool(val > 0)})
    out["P2_beurling_form_samples"] = beur

    with open(os.path.join(HERE, "e8_arb_certificate.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps({k: out[k] for k in ("zeta_zero_1", "lambda_zeta_sign_change")}, indent=2))
    print("P2 exact mismatches:", out["P2_integer_frequency_form"]["mismatches"][:10])
    print("FE contains zero:", [r["contains_zero"] for r in fe])


if __name__ == "__main__":
    main()
