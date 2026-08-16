"""The Pell / continued-fraction structure of the E2 chain region -- a new arithmetic handle on the last
non-symbolic piece of Phi<=1.

CONTEXT.  Phi<=1-as-a-theorem was reduced (lemma_proofs.py) to E0/E1/E3/DEC (proven) + E2-supremum (proven)
+ the E2 SUB-MAXIMAL non-near-star-child chains, which were called a "1D value-function coupling" because a
chain (0,[(0,[(0,[...])])]) accumulates increments delta(nu)=-L+log(1+nu/2) along cavities converging to the
fixed point nu*=sqrt(2)-1, and a CONSTANT bound fails the recursion there (delta>0 for nu>0.459).  Every
SMOOTH certificate dies on this accumulation (it is the 1D shadow of the main integrality obstruction).

THE NEW IDEA (arithmetic, not smooth).  The chain map f(nu)=1/(2+nu) is the continued fraction [0;2,2,2,...],
so the chain cavities are consecutive ratios of PELL-companion numbers
        1, 1/3, 3/7, 7/17, 17/41, 41/99, ...      b: 1,3,7,17,41,99,239,...   b_{k+1}=2 b_k + b_{k-1}.
Because 1 + nu_k/2 = (2 b_k + a_k)/(2 b_k) = b_{k+1}/(2 b_k), the log-amplitude TELESCOPES EXACTLY through the
Pell denominators:
        sum_{j<k} delta(nu_j) = log(b_k) - log(b_0) - k*(L + log 2).
So a chain of depth k over a base of cavity a_0/b_0 has
        log Phi(chain) = log Phi(base) + [ log b_k - log b_0 - k (L + log 2) ].

TWO EXACT CONSEQUENCES (replacing the "coupling").
  (1) DECAY is a single exact inequality.  b_k ~ (1+sqrt2)^k while e^{L+log2} = 2 rho_B, and
        (2 rho_B)^11 = 2^11 * 621/64 = 19872  >  (1+sqrt2)^11 = 8119 + 5741 sqrt2  ( = 16238 ),
      equivalently 11753 > 5741 sqrt2, i.e. 11753^2 > 2*5741^2 (138133009 > 65918642).  Hence
      2 rho_B > 1+sqrt2, so log b_k - k(L+log2) -> -infinity: EVERY chain decays, at exact rate
      log((1+sqrt2)/(2 rho_B)) = delta(sqrt2 - 1) per step.  No smooth certificate needed -- it is the same
      "cleared 11th root, exact integer inequality" mechanism as the near-star proof.
  (2) The depth profile is UNIMODAL.  G_k := log b_k - k(L+log2) rises then STRICTLY decreases (argmax at a
      finite k*, k*=1 for the bareleaf base) -- the exact analogue of the near-star R(s) unimodality.  So the
      chain amplitude is maximised at BOUNDED depth: the infinite-accumulation-at-sqrt2-1 worry is gone, and
      the E2 residual is reduced to FINITE depth times the finite base bound.

STATUS (honest).  This PROVES the depth direction of the E2 chain problem (exact Pell decay + unimodality),
converting the "1D value-function coupling / infinite accumulation" into an exact arithmetic fact.  It does
NOT by itself close E2: the base amplitude log Phi(base) over NON-near-star bases still needs its value bound
(the near-star bases give the proven binding -0.072573).  But the shape of the residual is now much smaller
and arithmetic, not analytic -- a genuine new foothold, in the same idiom (Pell/23-adic integrality) that
proved every other piece.

Requires sympy (exact surd inequality) and mpmath.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 40
_L = mp.log(mp.mpf(621) / 64) / 11


def chain_cavities(depth, base_cav=Fr(1, 1)):
    """Cavities nu_0=base, nu_{k+1}=1/(2+nu_k). Returns the list [nu_0,...,nu_depth] as Fractions."""
    out = [base_cav]
    for _ in range(depth):
        out.append(Fr(1, 2 + out[-1]))
    return out


def pell_denominators_satisfy_recursion(depth=10):
    cavs = chain_cavities(depth)
    b = [c.denominator for c in cavs]
    return all(b[k + 1] == 2 * b[k] + b[k - 1] for k in range(1, len(b) - 1)), b


def telescoping_is_exact(depth=8):
    """sum_{j<k} delta(nu_j) == log(b_k) - log(b_0) - k(L+log2), to full precision, for all k."""
    cavs = chain_cavities(depth)

    def delta(nu):
        return -_L + mp.log(1 + mp.mpf(nu.numerator) / nu.denominator / 2)
    ok = True
    for k in range(1, depth + 1):
        lhs = mp.fsum(delta(cavs[j]) for j in range(k))
        rhs = mp.log(cavs[k].denominator) - mp.log(cavs[0].denominator) - k * (_L + mp.log(2))
        ok = ok and abs(lhs - rhs) < mp.mpf(10) ** -30
    return ok


def decay_inequality_exact():
    """The exact surd inequality that makes EVERY chain decay: (2 rho_B)^11 = 19872 > (1+sqrt2)^11."""
    import sympy as sp
    lhs = Fr(2) ** 11 * Fr(621, 64)                     # (2 rho_B)^11, exact rational
    rhs = sp.expand((1 + sp.sqrt(2)) ** 11)             # 8119 + 5741 sqrt2
    # reduce to an integer inequality: 19872 > 8119 + 5741 sqrt2  <=>  11753 > 5741 sqrt2  <=>  11753^2 > 2*5741^2
    a = int(lhs) - 8119                                  # 11753
    b = 5741
    integer_form_holds = a > 0 and a * a > 2 * b * b
    surd_holds = bool(sp.simplify(sp.Rational(int(lhs)) - rhs) > 0)
    return {"two_rhoB_pow11": int(lhs), "one_plus_sqrt2_pow11": str(rhs),
            "integer_inequality": f"{a}^2 > 2*{b}^2  ({a*a} > {2*b*b})",
            "integer_form_holds": integer_form_holds, "surd_holds": surd_holds,
            "chain_decays": integer_form_holds and surd_holds,
            "per_step_rate": float(mp.log((1 + mp.sqrt(2)) / (2 * mp.e ** _L)))}   # = delta(sqrt2-1)


def depth_profile_unimodal(depth=12, base_cav=Fr(1, 1)):
    """G_k = log b_k - k(L+log2) rises then STRICTLY decreases (argmax finite): the Pell analogue of the
    near-star R(s) unimodality. The chain amplitude is maximised at BOUNDED depth."""
    cavs = chain_cavities(depth, base_cav)
    G = [mp.log(cavs[k].denominator) - k * (_L + mp.log(2)) for k in range(len(cavs))]
    kstar = max(range(len(G)), key=lambda k: G[k])
    strictly_decreasing_after = all(G[k] < G[k - 1] for k in range(kstar + 1, len(G)))
    return {"argmax_kstar": kstar, "strictly_decreasing_after_kstar": strictly_decreasing_after,
            "G": [float(g) for g in G]}


def certify():
    rec_ok, b = pell_denominators_satisfy_recursion(10)
    tel = telescoping_is_exact(8)
    dec = decay_inequality_exact()
    uni = depth_profile_unimodal(12)
    return {
        "chain_cavities_are_pell_ratios": rec_ok,        # b_{k+1}=2 b_k + b_{k-1}
        "pell_denominators": b[:8],
        "log_amplitude_telescopes_through_pell": tel,     # sum delta = log(b_k/b_0) - k(L+log2), exact
        "decay_is_exact_integer_inequality": dec["integer_form_holds"] and dec["surd_holds"],
        "decay_inequality": dec["integer_inequality"],    # 11753^2 > 2*5741^2
        "two_rhoB_pow11_gt_one_plus_sqrt2_pow11": f'{dec["two_rhoB_pow11"]} > {dec["one_plus_sqrt2_pow11"]}',
        "per_step_decay_rate": dec["per_step_rate"],       # = delta(sqrt2-1) ~ -0.0184
        "depth_profile_unimodal": uni["strictly_decreasing_after_kstar"],
        "argmax_depth": uni["argmax_kstar"],
        "reframes_E2_coupling": bool(rec_ok and tel and dec["integer_form_holds"]
                                     and uni["strictly_decreasing_after_kstar"]),
        "note": "PROVES the depth direction of E2 (exact Pell decay + unimodality); the infinite-accumulation "
                "'1D coupling' is now an exact arithmetic fact. Does NOT close E2 alone -- the non-near-star "
                "BASE amplitude still needs its bound (near-star bases give the proven -0.072573 binding).",
        "Phi_le_1_is_theorem": False,
    }


if __name__ == "__main__":
    for k, v in certify().items():
        print(f"  {k}: {v}")
