"""FLATNESS-FAMILY DOMINATION CLOSED: r(q) = best_template(181+11q)/pi_star(cfg(q)) > 23/20
for ALL q >= 1 -- the asymmetric-tail sliver of the R7 interpolation lemma, as pure algebra.

The 2026-08-18 session left this genuinely open ("could not soundly derive closed-form growth
rates"; the unimodality of r was sampled, not proved). The pfinite_probe_w2 backbone (order-1
P-finite ratios for pi_star and the template families) turns it into three exact facts. The
key simplification: DOMINATION never needed unimodality or the argmax identity -- best_template
is a max, so ANY member family is a free lower bound. Family D works at EVERY q >= 1.

THEOREM. For all integers q >= 1, with n = 181 + 11q, a(q) = pi_star(cfg(q)),
cfg(q) = (2,1,0,0,(q,5,9)), and D(q) the family-D template value
(c0=0, nleaf=0, K=q+16, loads [6,6] + [5]*(K-2)):

    best_template(n) >= D(q) > (23/20) * a(q).

PROOF (verified exactly below):
  (V) VALIDITY: D(q) is in best_template's enumeration space for every q >= 1:
      rem = n - 1 = 180 + 11q = 11K + 4 with K = q + 16 exactly (176 = 11*16);
      t2 = rem - K = 10K + 4 is even; tot = 5K + 2 <= 8K; divmod(5K+2, K) = (5, 2) for
      K >= 17, reproducing loads [6,6] + [5]*(K-2); and K lies in the search window
      [rem//13, rem//9 + 1] since 13(q+16) >= 180+11q (i.e. 2q >= -28) and
      9(q+15) <= 180+11q (i.e. 0 <= 45 + 2q). Hence best_template(n) >= D(q) by
      definition of max.
  (B) BASE: D(1)/a(1) > 23/20, one exact rational comparison.
  (S) STEP: D(q+1)/a(q+1) >= D(q)/a(q) for all q >= 1, because with the symbolic order-1
      ratios (derived from the closed-form product formulas; verified exactly against the
      code in pfinite_probe_w2)
        a(q+1)/a(q) = 621(q+1)(88185461q+176596081) / [64(q+2)(88185461q+88410620)]
        D(q+1)/D(q) = 621(q+16)(117q+1985)         / [64(q+17)(117q+1868)]
      the difference (D-ratio)/(a-ratio) - 1 has numerator
        379085447 q^2 + 1927564431 q + 7857434164
      (ALL coefficients positive) over a positive denominator.
  (B)+(S) => D(q)/a(q) > 23/20 for all q >= 1 by induction. QED (modulo the Lean port of
  the ratio identities, which are ring algebra over the product formulas).

Lean-shaped obligations: (V) is integer arithmetic (omega/norm_num); (B) is one norm_num
rational fact; (S) is positivity of an explicit all-positive-coefficient quadratic plus ring
identities -- all existing Telperion emitter shapes. conjecture1_proved = False.
Self-verifying run_all().
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from verification.pfinite_probe_w2 import (
    a,
    a_ratio_symbolic,
    b_ratio_D_symbolic,
    best_template,
    family_D_value,
    n_of_q,
)

MARGIN = Fr(23, 20)
STEP_NUM_COEFFS = [379085447, 1927564431, 7857434164]


def verify_validity(qmax: int = 60) -> dict:
    """(V): D(q) is in the best_template enumeration space; symbolic + spot checks."""
    q = sp.symbols("q", positive=True)
    K = q + 16
    rem = 180 + 11 * q
    assert sp.expand(rem - (11 * K + 4)) == 0            # rem = 11K + 4 exactly
    assert sp.expand((rem - K) - (10 * K + 4)) == 0      # t2 = 10K + 4 (even)
    assert sp.expand(8 * K - (5 * K + 2)) == sp.expand(3 * K - 2)   # tot <= 8K for K >= 1
    # search window: 13K >= rem  and  9(K - 1) <= rem
    assert sp.expand(13 * K - rem) == sp.expand(2 * q + 28)         # >= 0 for q >= 1
    assert sp.expand(rem - 9 * (K - 1)) == sp.expand(2 * q + 45)    # >= 0 for q >= 1
    for qi in range(1, qmax + 1):
        Ki = qi + 16
        tot = 5 * Ki + 2
        assert divmod(tot, Ki) == (5, 2)                 # loads [6,6] + [5]*(K-2)
        assert best_template(n_of_q(qi)) >= family_D_value(qi)
    return {"validity": f"symbolic + exact best_template >= D on q=1..{qmax}"}


def verify_base() -> dict:
    """(B): D(1)/a(1) > 23/20, exact."""
    ratio = Fr(family_D_value(1)) / Fr(a(1))
    assert ratio > MARGIN, ratio
    return {"base_D1_over_a1": str(ratio), "float": float(ratio), "margin": str(MARGIN)}


def verify_step() -> dict:
    """(S): (D-ratio)/(a-ratio) - 1 has the all-positive-coefficient quadratic numerator."""
    q = sp.symbols("q", positive=True)
    ra = sp.Rational(621, 64) * (q + 1) * (88185461 * q + 176596081) \
        / ((q + 2) * (88185461 * q + 88410620))
    rD = sp.Rational(621, 64) * (q + 16) * (117 * q + 1985) \
        / ((q + 17) * (117 * q + 1868))
    for qi in range(1, 40):    # the symbolic forms ARE the probe's exact ratios
        assert sp.Rational(a_ratio_symbolic(qi)) == ra.subs(q, qi)
        assert sp.Rational(b_ratio_D_symbolic(qi)) == rD.subs(q, qi)
    num, den = sp.fraction(sp.together(sp.simplify(rD / ra - 1)))
    poly = sp.Poly(sp.expand(num), q)
    assert poly.all_coeffs() == STEP_NUM_COEFFS, poly.all_coeffs()
    dpoly = sp.Poly(sp.expand(den), q)
    assert all(c > 0 for c in dpoly.all_coeffs()), "denominator must be positive for q > 0"
    return {"step_numerator": str(poly.as_expr()), "all_coeffs_positive": True}


def verify_induction_matches(qmax: int = 60) -> dict:
    """Cross-check the induction conclusion against exact values (belt and suspenders)."""
    worst = None
    for qi in range(1, qmax + 1):
        ratio = Fr(family_D_value(qi)) / Fr(a(qi))
        assert ratio > MARGIN, (qi, ratio)
        worst = ratio if worst is None else min(worst, ratio)
    return {"exact_min_D_over_a": float(worst), "range": f"q=1..{qmax}"}


def run_all() -> dict:
    out = {
        "V": verify_validity(),
        "B": verify_base(),
        "S": verify_step(),
        "cross_check": verify_induction_matches(),
        "theorem": {
            "statement": "best_template(181+11q) > (23/20) * pi_star(cfg(q)) for ALL q >= 1",
            "mechanism": "member lower bound (V) + exact base (B) + all-positive-coefficient "
                         "quadratic step (S) => induction; unimodality never needed",
            "rigor": "exact rational + symbolic ring identities; ratio identities verified "
                     "against code in pfinite_probe_w2 (Lean port = ring algebra)",
            "conjecture1_proved": False,
        },
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
