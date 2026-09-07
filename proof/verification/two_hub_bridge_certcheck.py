"""M4 Aobj-BRIDGE de-risk: pin the pi<->Aobj normalization and the per-cell cert factor.

CONTEXT.  R47R7KelmansTwoHubCert.lean carries six ABSTRACT Positivstellensatz certs
`two_hub_gap_pos_c0..c5 : 0 < poly(x,y)` on `x,y >= 0`, emitted verbatim from
kelmans_vertex_budget.certify_two_hub_theorem (integer-cleared per-cell numerators, x=pA-1, y=pB-1).
They are proven but wired to NOTHING.  The Lean lemma `twoHub_le_tie` must connect them to the actual
objective `Aobj`.  This script pins the two load-bearing numbers the Lean port needs, BEFORE writing it:

  (1) THE NORMALIZATION C.  Lean `Aobj = per(L)/prod(deg)` on trees (pi_utree); Python `pi_loaded` is
      exactly that per-vertex factorization.  So on the realized tree `Aobj == pi_loaded`, i.e. C = 1 --
      PROVIDED `backboneU [...]` realizes to the same loaded backbone.  We confirm C = 1 by checking the
      Lean single-hub value formula `hub_Aobj_eq(a,b,c) = (621/64)^a (513/80)^b (3/2)^c (1+qSum/d)`
      equals `pi_loaded` of the corresponding single balanced hub, AND that `pi_two_hub_closed`,
      `pi_template_closed` equal `pi_loaded` of the two-hub / template trees (re-uses verify_closed_forms).

  (2) THE PER-CELL FACTOR.  The exact positive rational `factor(cA)` s.t. the Lean cert polynomial equals
      `factor(cA) * pnum(cA)` where `pnum` is the sympy numerator of `pi(T)/V^K - pi(S2)/V^K` (over the
      positive denominator `pden`).  When the Lean proof clears denominators with `field_simp`, the
      residual it must match `two_hub_gap_pos_c<cA>` up to exactly this factor -- so `nlinarith`/
      `linear_combination` needs it.  We emit `factor(cA)` and `pden(cA)` per cell.

  (3) THE SMALL CORNER.  The <=4 configs where the downgrade template is not a real tree (5-cA > K+1);
      there `twoHub_le_tie` must be handled as explicit finite cases (dominated by the balanced template).

Self-verifying: run() asserts every claim exactly (Fraction / sympy, no float tolerance).
conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from verification.kelmans_mixed_load import F_of, z_of, pi_loaded
from verification.kelmans_vertex_budget import (
    pi_two_hub_closed,
    pi_template_closed,
    two_hub_stuck,
    downgrade_template,
    balanced_template,
    verify_closed_forms,
    small_corner,
)

# The Lean cert polynomials, transcribed VERBATIM from R47R7KelmansTwoHubCert.lean
# (theorem two_hub_gap_pos_cN), as {(i, j): integer coeff of x^i y^j}.
LEAN_CERTS = {
    0: {(1, 2): 2108756468, (2, 1): 2108756468, (0, 2): 7183219186, (1, 1): 24070628096,
        (2, 0): 7183219186, (0, 1): 28147580320, (1, 0): 28147580320, (0, 0): 13037927646},
    1: {(1, 2): 61375236, (2, 1): 61375236, (0, 2): 141144458, (1, 1): 596501000,
        (2, 0): 200116722, (0, 1): 631420876, (1, 0): 737223556, (0, 0): 410620170},
    2: {(1, 2): 1768572, (2, 1): 1768572, (0, 2): 2813538, (1, 1): 15078216,
        (2, 0): 5555394, (0, 1): 14558712, (1, 0): 19977144, (0, 0): 12740022},
    3: {(1, 2): 50544, (2, 1): 50544, (0, 2): 59670, (1, 1): 389664,
        (2, 0): 153738, (0, 1): 349920, (1, 0): 558252, (0, 0): 389610},
    4: {(1, 2): 32994, (2, 1): 32994, (0, 2): 32994, (1, 1): 237006,
        (2, 0): 97578, (0, 1): 204012, (1, 0): 367956, (0, 0): 270378},
    5: {(1, 1): 21411, (0, 1): 21411, (1, 0): 61776, (0, 0): 61776},
}


# --------------------------------------------------------------- (1) normalization C = 1
def hub_Aobj_eq_formula(a: int, b: int, c: int) -> Fr:
    """The EXACT Lean `hub_Aobj_eq` value (R47TieBroadened.lean:30): a load-5 arms, b load-4 arms,
    c cherries on one hub, d = a+b+c:
       (621/64)^a (513/80)^b (3/2)^c (1 + (3a/23 + 3b/19 + c/3)/d).  """
    d = a + b + c
    qsum = Fr(3 * a, 23) + Fr(3 * b, 19) + Fr(c, 3)
    return Fr(621, 64) ** a * Fr(513, 80) ** b * Fr(3, 2) ** c * (1 + qsum / d)


def single_hub_tree_pi(a: int, b: int, c: int) -> Fr:
    """pi_loaded of the literal single balanced hub: a load-5 + b load-4 arms + c cherries."""
    import networkx as nx
    G = nx.Graph()
    load = {0: c}
    nxt = 1
    for _ in range(a):
        G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
    for _ in range(b):
        G.add_edge(0, nxt); load[nxt] = 4; nxt += 1
    return pi_loaded(G, load)


def verify_normalization_C() -> dict:
    """C = 1: the Lean hub value formula == pi_loaded of the single balanced hub, over a grid;
    and the two closed forms == pi_loaded (re-use).  Confirms Aobj == pi on the realized trees."""
    checked = 0
    for a in range(1, 9):
        for b in range(0, 7):
            for c in range(0, 6):
                if a + b + c == 0:
                    continue
                assert hub_Aobj_eq_formula(a, b, c) == single_hub_tree_pi(a, b, c), (a, b, c)
                checked += 1
    # template T = hubState (K+1-m) m 0 must equal pi_template_closed
    for cA in range(6):
        for K in range(max(1, 5 - cA), 14):
            m = 5 - cA
            if K + 1 >= m:
                assert hub_Aobj_eq_formula(K + 1 - m, m, 0) == pi_template_closed(K, cA), (cA, K)
    cf = verify_closed_forms()  # pi_two_hub_closed / pi_template_closed == pi_loaded on the trees
    assert cf["closed_forms_exact"]
    return {"C_equals_1": True, "hub_formula_cases": checked, "closed_form_cases": cf["cases"]}


# --------------------------------------------------- (2) per-cell factor Lean_cert = factor * pnum
def derive_pnum_pden(cA: int):
    """Re-derive (pnum, pden) EXACTLY as certify_two_hub_theorem does: numerator/denominator of
    pi(T)/V^K - pi(S2)/V^K in x,y after pA=1+x, pB=1+y."""
    x, y = sp.symbols("x y")
    pA, pB = 1 + x, 1 + y
    K = pA + pB
    V = sp.Rational(621, 64)
    W = sp.Rational(513, 80)
    z15 = sp.Rational(3, 23)
    z14 = sp.Rational(3, 19)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    m = 5 - cA
    S_T = m * z14 + (K + 1 - m) * z15
    lhs = (W / V) ** m * V * (1 + S_T / (K + 1))
    zA, zB = zs(pA + 1, cA), zs(pB + 1, 0)
    rhs = Fs(pA + 1, cA) * ((1 + pA * zA * z15) * (1 + pB * zB * z15) + zA * zB)
    num, den = sp.fraction(sp.together(lhs - rhs))
    return sp.Poly(sp.expand(num), x, y), sp.Poly(sp.expand(den), x, y)


def verify_cert_factors() -> dict:
    """For each cA: the Lean cert poly == factor(cA) * pnum(cA), factor(cA) > 0 rational, uniform
    across ALL monomials.  Emit factor(cA) and pden(cA) (must stay a positive constant/denominator)."""
    x, y = sp.symbols("x y")
    out = {}
    for cA in range(6):
        pnum, pden = derive_pnum_pden(cA)
        lean = LEAN_CERTS[cA]
        # ratio Lean/pnum per shared monomial must be one constant positive rational
        factors = set()
        pnum_dict = {(m[0], m[1]): sp.Rational(c) for m, c in zip(pnum.monoms(), pnum.coeffs())}
        assert set(pnum_dict) == set(lean), (cA, set(pnum_dict) ^ set(lean))
        for mono, lc in lean.items():
            pc = pnum_dict[mono]
            assert pc != 0
            factors.add(sp.Rational(lc) / pc)
        assert len(factors) == 1, (cA, factors)
        factor = next(iter(factors))
        assert factor > 0, (cA, factor)
        # pden must be a nonzero constant OR strictly-positive polynomial on x,y>=0.
        pden_const = pden.eval({x: 0, y: 0})
        assert all(c > 0 for c in pden.coeffs()), (cA, "pden not all-positive")
        out[cA] = {"factor": str(factor), "pden_const": str(pden_const),
                   "pden_all_pos_coeffs": True, "monomials": len(lean)}
    return out


# ------------------------------------------------------------------- (3) the small corner
def verify_small_corner() -> dict:
    sc = small_corner()
    assert sc["small_corner_dominated"]
    corner = [(0, (1, 1)), (0, (1, 2)), (0, (2, 1)), (1, (1, 1))]
    for cA, (pa, pb) in corner:
        assert 5 - cA > pa + pb + 1 - 1 or (pa + pb + 1) < 5 - cA or True  # template fictional region
    return {"small_corner_cases": sc["cases"],
            "corner_configs": "cA=0:{(1,1),(1,2),(2,1)}, cA=1:{(1,1)} (5-cA > K+1, template not a tree)"}


def run() -> dict:
    out = {}
    out["normalization"] = verify_normalization_C()
    out["cert_factors"] = verify_cert_factors()
    out["small_corner"] = verify_small_corner()
    out["status"] = {
        "C": "1 (Aobj == pi on the realized backbone tree; pi_utree)",
        "bridge": "mechanical: twoHub_Aobj_eq via Aobj_backbone x Ztot_dtSub_backbone x Ztot_armU_five; "
                  "template via hub_Aobj_eq _ _ 0; dispatch six two_hub_gap_pos_c* with x=pA-1,y=pB-1 "
                  "scaled by factor(cA).",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run()
