"""Arithmetic attack on the BUSH BOUND -- piece (ii) of the Phi<=1 depth-collapse factorisation.

TARGET.  The depth-2 cherry-bush maximiser
    B(c,k,t) = a root with c cherries and k children, each child a t-cherry LEAF (t,[]),
and the bush bound  logPhi(B(c,k,t)) <= 0  for all integers c>=0, k>=1, t>=0
(BushBound.lean proves this only CONDITIONALLY, given the per-node hypothesis eroot <= -k*gVal(t)).
Cleared to the 11th power (rho_B^11 = 621/64 = 3^3*23/2^6) this is the exact integer inequality BUSH-STAR
(bush_star_probe.py, verified equivalent to logPhi<=0):
    3^(11P) 2^(6Q) N^11 <= 2^(11P) 3^(3Q) 23^Q D^11,
    P=kt+c, Q=1+2c+k+2kt, N=(4t+3)^(k-1)((3k+3+4c)(4t+3)+9k), D=3^(k+1)(t+1)^k(k+1+c).

This module follows the near_star_arithmetic_proof.py template (reduce -> clear the 11th root -> exact
rational monotonicity).  It gets GENUINELY NEW rigorous ground (R0-R3 below) but leaves three residual
boxes open, and originally mis-diagnosed them as "the same marginal-tie obstruction".

*** SUPERSEDED / RECONCILED (2026-08-11): the bush bound IS NOW CLOSED. ***
The residual is NOT a marginal tie -- the whole bush family has a UNIFORM positive gap (max logPhi =
omega < 0 at the ARM B(0,1,0); the Phi=1 tie lives only on the near-star ARM family N(c,k), c+k=5, a
DIFFERENT depth-2 object).  A strict gap closes by crude bound + geometric escape + finite core, with NO
sharp 23-adic single-crossing.  The three residual boxes are all proven:
  - Q1 (k=1 slice)          -> bush_k1_slice_proof.py   (bs1 = K rho^(c+t) (D/N)^11, D/N>9/16, escape s>=22)
  - Q2 (c=0 star) & the full bush bound -> bush_bound_closed.py   (bush_bound_proved = True)
  - the corrected piece (ii) (mixed leaf cherry-counts) -> mixed_bush_bound_closed.py
Those modules REUSE R2 (easy-region monotonicity) and R3 (confinement) from here.  This module is kept
as the reduction + the R0-R3 lemmas; its own bush_bound_proved flag stays False (it does not itself close
the residual -- bush_bound_closed.py does).  See SESSION_REPORT_laplacian_20260811.md.
Every claim below is checked in exact rational arithmetic (fractions.Fraction).

============================================================================================
WHAT IS RIGOROUSLY PROVEN (exact, for ALL integers c,k>=1,t>=0 -- not merely a finite scan)
============================================================================================

(R0) EXACT REDUCTION.  With the cavity telescoping (cavity_potential.py) a t-cherry-leaf child has
     cavity 3/(4t+3) and matching value gVal(t) = g(t) = the NEAR-STAR value at s=t.  Hence
        logPhi(B(c,k,t)) = c*log(3/2) - (1+2c)*L + log(arg) + k*g(t),   L = log(621/64)/11,
        arg = 1 + c/(3d) + 3k/(d(4t+3)),   d = k+1+c.
     In particular g(t) <= 0 for ALL t (near_star_arithmetic_proof.py, equality iff t=5): cleared,
        e^{11 g(t)} = LN(t)/RN(t) = 3^(5t-14) 2^(t+6) (4t+3)^11 / (23^(2t+1) (t+1)^11) <= 1.

(R1) EXACT k-INCREMENT.  Delta_k := logPhi(B(c,k+1,t)) - logPhi(B(c,k,t)) satisfies
        e^{11 Delta_k} = e^{11 g(t)} * ((A(k+1)+B)/(Ak+B))^11 * ((k+1+c)/(k+2+c))^11,
        A = 12t+18 = 6(2t+3),   B = (4t+3)(4c+3).
     (Verified EXACTLY: e^{11 Delta_k} = bs_val(c,k,t)/bs_val(c,k+1,t).)

(R2) EASY-REGION k-MONOTONICITY (the new lemma).  Whenever  4ct - 6c - 9 >= 0  (equivalently
     A(1+c) <= B), the middle two factors of (R1) multiply to <= 1, so
        Delta_k <= g(t) <= 0     for EVERY k.
     Proof: A(1+c) <= B  <=>  A/(Ak+B) <= 1/(k+1+c) for all k  <=>  (1+A/(Ak+B))(k+1+c)/(k+2+c) <= 1.
     Hence in the easy region logPhi(B(c,k,t)) is non-increasing in k and <= logPhi(B(c,1,t)).

(R3) CONFINEMENT.  For c>=1 and t>=4,  4ct-6c-9 >= 10c-9 >= 1 > 0, so (R2) applies.  Therefore the
     ONLY place the c>=1 family can fail to be k-monotone is the finite strip  t in {0,1,2,3}.

============================================================================================
THE THREE RESIDUAL BOXES -- now CLOSED (see bush_bound_closed.py / bush_k1_slice_proof.py)
============================================================================================

(Q1) k=1 SLICE:      logPhi(B(c,1,t)) <= 0   for all c,t>=0.
(Q2) c=0 STAR:       logPhi(B(0,k,t)) <= 0   for all k>=1,t>=0.
(Q3) c>=1, t in {0,1,2,3}:  Delta_k <= 0 (hence logPhi(B(c,k,t)) <= logPhi(B(c,1,t)), i.e. (Q1)).

These were reduced here and originally left open under a WRONG diagnosis ("same marginal-tie
obstruction; needs a multivariate integer argument").  The correct picture: the bush family has a
UNIFORM positive gap (max logPhi = omega < 0 at the ARM), so a crude bound + geometric escape closes
each box -- e.g. Q1 factors as bs1 = K rho^(c+t) (D/N)^11 with the exact identity 16D-9N = 72t+36c+45>0
(=> D/N > 9/16), and rho^(c+t) escapes for c+t >= 22 (bush_k1_slice_proof.py).  The three natural
single-variable reductions still fail (arg maxes at t=0 where g is most-negative -> K1UP(0)=+0.199>0;
t=5 does not max logPhi over t; the crude f(1)-bound drops (k+1+c)/(k+2+c)) -- but they are NOT the only
route: the escape argument sidesteps them entirely.  bush_bound is PROVEN in bush_bound_closed.py.
This module's own bush_bound_proved flag stays False (it supplies R0-R3, not the closure).
conjecture1_proved = False.

Requires only the standard library (fractions).
"""
from __future__ import annotations

from fractions import Fraction as Fr

TIE_T = 5  # g(t) = 0 exactly at t = 5 (the marginal tie)


def A(t: int) -> int:
    """A = 12t + 18 = 6(2t+3)."""
    return 12 * t + 18


def B(c: int, t: int) -> int:
    """B = (4t+3)(4c+3)."""
    return (4 * t + 3) * (4 * c + 3)


def LN(t: int) -> Fr:
    """LN(t) = 3^(5t-14) 2^(t+6) (4t+3)^11  (= LHS of the near-star cleared inequality)."""
    return Fr(3) ** (5 * t - 14) * Fr(2) ** (t + 6) * Fr(4 * t + 3) ** 11


def RN(t: int) -> Fr:
    """RN(t) = 23^(2t+1) (t+1)^11  (= RHS of the near-star cleared inequality)."""
    return Fr(23) ** (2 * t + 1) * Fr(t + 1) ** 11


def e11g(t: int) -> Fr:
    """e^{11 g(t)} = LN(t)/RN(t).  g(t) <= 0 (near-star) <=> e11g(t) <= 1, equality iff t = 5."""
    return LN(t) / RN(t)


def exp11_delta_k(c: int, k: int, t: int) -> Fr:
    """e^{11 Delta_k} of (R1).  Delta_k <= 0  <=>  exp11_delta_k <= 1."""
    a, b = A(t), B(c, t)
    return e11g(t) * Fr(a * (k + 1) + b, a * k + b) ** 11 * Fr(k + 1 + c, k + 2 + c) ** 11


def bs_val(c: int, k: int, t: int) -> Fr:
    """e^{-11 logPhi(B(c,k,t))} = (RHS/LHS) of BUSH-STAR.  logPhi <= 0  <=>  bs_val >= 1."""
    P = k * t + c
    Q = 1 + 2 * c + k + 2 * k * t
    N = (4 * t + 3) ** (k - 1) * ((3 * k + 3 + 4 * c) * (4 * t + 3) + 9 * k)
    D = 3 ** (k + 1) * (t + 1) ** k * (k + 1 + c)
    return Fr(2 ** (11 * P) * 3 ** (3 * Q) * 23 ** Q * D ** 11,
              3 ** (11 * P) * 2 ** (6 * Q) * N ** 11)


def bush_le0(c: int, k: int, t: int) -> bool:
    """The bush bound at (c,k,t):  logPhi(B(c,k,t)) <= 0."""
    return bs_val(c, k, t) >= 1


def easy(c: int, t: int) -> bool:
    """Easy region A(1+c) <= B (k-independent)."""
    return A(t) * (1 + c) <= B(c, t)


def verify(box: int = 60) -> dict:
    """Exactly verify every rigorous claim (R0)-(R3) and the three residual boxes (Q1)-(Q3)."""
    # (R1) the k-increment formula is EXACT: e^{11 Delta_k} = bs_val(k)/bs_val(k+1).
    incr_exact = all(exp11_delta_k(c, k, t) == bs_val(c, k, t) / bs_val(c, k + 1, t)
                     for c in range(8) for k in range(1, 8) for t in range(8))
    # (R0) g(t) <= 0 for all t (e11g <= 1), equality iff t = 5.
    g_nonpos = all(e11g(t) <= 1 for t in range(4 * box)) and e11g(TIE_T) == 1 and \
        all(e11g(t) < 1 for t in range(4 * box) if t != TIE_T)
    # (R2) easy-region identity + monotonicity lemma.
    easy_identity = all(easy(c, t) == (4 * c * t - 6 * c - 9 >= 0)
                        for c in range(3 * box) for t in range(3 * box))
    easy_lemma = all(exp11_delta_k(c, k, t) <= e11g(t)              # Delta_k <= g(t) <= 0
                     for c in range(box) for t in range(box) for k in range(1, box)
                     if 4 * c * t - 6 * c - 9 >= 0)
    # (R3) confinement: c>=1, t>=4 => easy (4ct-6c-9 >= 1).
    confinement = all(4 * c * t - 6 * c - 9 >= 1 for c in range(1, 3 * box) for t in range(4, 3 * box))
    # (Q1)-(Q3) residual near-tie boxes: verified EXACTLY on the finite ranges (NOT a proof for all).
    q1_k1_slice = all(bush_le0(c, 1, t) for c in range(2 * box) for t in range(2 * box))
    q2_c0_star = all(bush_le0(0, k, t) for k in range(1, 2 * box) for t in range(2 * box))
    q3_c1_tle3 = all(bush_le0(c, k, t) for c in range(1, box) for k in range(1, box) for t in range(4))
    proven = incr_exact and g_nonpos and easy_identity and easy_lemma and confinement
    residual_ok = q1_k1_slice and q2_c0_star and q3_c1_tle3
    return {
        # ---- RIGOROUS (all values) ----
        "R1_k_increment_formula_exact": incr_exact,
        "R0_g_nonpos_tie_at_5": g_nonpos,
        "R2a_easy_region_identity": easy_identity,
        "R2b_easy_region_monotonicity_lemma": easy_lemma,
        "R3_confinement_c1_t_ge4_is_easy": confinement,
        "structural_reduction_proven": proven,
        # ---- RESIDUAL near-tie boxes (finite exact verification only) ----
        "Q1_k1_slice_box_ok": q1_k1_slice,
        "Q2_c0_star_box_ok": q2_c0_star,
        "Q3_c1_tle3_box_ok": q3_c1_tle3,
        "residual_boxes_verified_on_finite_range": residual_ok,
        # ---- HONEST STATUS ----
        "bush_bound_proved": False,
        "conjecture1_proved": False,
        "statement": ("PROVEN (R0-R3, all values): the exact reduction + k-increment; the easy-region "
                      "k-monotonicity 4ct-6c-9>=0 => Delta_k<=g(t)<=0 (R2); confinement of the c>=1 "
                      "residual to t in {0,1,2,3} (R3); g(t)<=0 tie only at t=5 (R0). The three residual "
                      "boxes (Q1 k=1 slice, Q2 c=0 star, Q3 c>=1 & t<=3) are NOW CLOSED in "
                      "bush_bound_closed.py / bush_k1_slice_proof.py (uniform gap => geometric escape, NOT "
                      "a marginal tie -- the original 'same obstruction' diagnosis here was wrong). This "
                      "module supplies R0-R3; bush_bound_proved lives in bush_bound_closed.py."),
    }


if __name__ == "__main__":
    for key, val in verify().items():
        print(f"{key}: {val}")
