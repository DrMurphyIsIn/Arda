"""RIGOROUS closure of Q1 -- the k=1 slice of the BUSH BOUND (piece (ii) of Phi<=1).

CONTEXT.  bush_bound_arithmetic_proof.py reduced the bush bound logPhi(B(c,k,t))<=0 (for the depth-2
cherry-bush B(c,k,t) = root with c cherries + k children each a t-cherry leaf) to three residual
near-tie boxes, of which the k=1 slice was the first:

    (Q1)   logPhi(B(c,1,t)) <= 0   for all integers c,t >= 0.

That module verified Q1 only on a finite scan and flagged every single-variable reduction as refuted by
the near-tie structure.  THIS MODULE PROVES Q1 outright, in exact rational arithmetic, for ALL c,t >= 0.

WHY IT CLOSES (where prior attempts stalled).  The obstruction to the *general* conjecture is a MARGINAL
tie (Phi=1 exactly, achieved on the near-star arm family N(c,k), c+k=5).  The k=1 bush slice does NOT
contain that tie: its minimum of -logPhi is +omega = log(621/64... )/... = 0.007707 > 0, attained only at
the ARM B(0,1,0), and -logPhi -> +infinity in every direction.  So Q1 is a STRICT inequality with a
uniform positive gap -- and a gap can be closed by a crude bound plus geometric escape, WITHOUT the sharp
23-adic single-crossing the marginal tie forces.  Concretely:

(P0) EXACT REDUCTION (k=1).  bush_le0(c,1,t)  <=>  bs1(c,t) >= 1, where the cleared-11th-power value
        bs1(c,t) = K * rho^(c+t) * (D/N)^11,
        K = 529*729/4096,   rho = 529/486 > 1,   D = 9(t+1)(c+2),   N = 16ct+24t+12c+27.
     (rho = 23^2/(2*3^5) is exactly the near-star ratio base; the k=1 slice inherits it with s=c+t.)

(P1) CRUDE UNIFORM BOUND (exact integer identity).  16D - 9N = 72t + 36c + 45 > 0, hence
        D/N > 9/16   for all c,t >= 0.

(P2) GEOMETRIC ESCAPE.  g(s) := K * rho^s * (9/16)^11 is strictly increasing in s (rho>1) and
        g(22) >= 1  (checked exactly), so g(s) >= 1 for every integer s >= 22.
     Therefore for c+t >= 22:  bs1(c,t) > K*rho^(c+t)*(9/16)^11 = g(c+t) >= 1.

(P3) FINITE CORE.  For the finitely many (c,t) with c+t < 22, bs1(c,t) >= 1 is checked exactly.

(P0)&(P1)&(P2)&(P3)  =>  bs1(c,t) >= 1 for ALL integers c,t >= 0.  QED (Q1).

q1_proved = True.  Requires only the standard library (fractions).
"""
from __future__ import annotations

from fractions import Fraction as Fr

K = Fr(529 * 729, 4096)     # 23^2 * 3^6 / 2^12
RHO = Fr(529, 486)          # 23^2 / (2 * 3^5) > 1
NINE_SIXTEENTHS_11 = Fr(9, 16) ** 11
S0 = 22                     # escape threshold


def Dfun(c: int, t: int) -> int:
    """D = 9(t+1)(c+2)."""
    return 9 * (t + 1) * (c + 2)


def Nfun(c: int, t: int) -> int:
    """N = 16ct + 24t + 12c + 27."""
    return 16 * c * t + 24 * t + 12 * c + 27


def bs1(c: int, t: int) -> Fr:
    """Cleared value of the k=1 bush bound: logPhi(B(c,1,t)) <= 0  <=>  bs1(c,t) >= 1."""
    return K * RHO ** (c + t) * Fr(Dfun(c, t), Nfun(c, t)) ** 11


def bs_val_k1_reference(c: int, t: int) -> Fr:
    """The general BUSH-STAR value bs_val(c,k,t) specialised to k=1 (independent re-derivation,
    to confirm bs1 == bush_bound_arithmetic_proof.bs_val on the k=1 slice)."""
    P = 1 * t + c
    Q = 1 + 2 * c + 1 + 2 * 1 * t
    N = (4 * t + 3) ** (1 - 1) * ((3 * 1 + 3 + 4 * c) * (4 * t + 3) + 9 * 1)
    D = 3 ** (1 + 1) * (t + 1) ** 1 * (1 + 1 + c)
    return Fr(2 ** (11 * P) * 3 ** (3 * Q) * 23 ** Q * D ** 11,
              3 ** (11 * P) * 2 ** (6 * Q) * N ** 11)


def q1_holds(c: int, t: int) -> bool:
    """logPhi(B(c,1,t)) <= 0."""
    return bs1(c, t) >= 1


def verify(scan: int = 80) -> dict:
    """Exactly verify every step (P0)-(P3) of the Q1 closure."""
    # (P0) reduction: bs1 == the general BUSH-STAR value at k=1 (exact, on a grid).
    p0_reduction = all(bs1(c, t) == bs_val_k1_reference(c, t)
                       for c in range(scan) for t in range(scan))
    # (P1) crude uniform bound as an EXACT integer identity  16D - 9N = 72t+36c+45 (>0 => D/N>9/16).
    p1_identity = all(16 * Dfun(c, t) - 9 * Nfun(c, t) == 72 * t + 36 * c + 45
                      for c in range(2 * scan) for t in range(2 * scan))
    p1_positive = all(72 * t + 36 * c + 45 > 0 for c in range(2 * scan) for t in range(2 * scan))
    # (P2) geometric escape: g increasing (rho>1) and g(S0)>=1, g(S0-1)<1 (so S0 is the exact threshold).
    def g(s: int) -> Fr:
        return K * RHO ** s * NINE_SIXTEENTHS_11
    p2_threshold = (g(S0) >= 1) and (g(S0 - 1) < 1)
    p2_monotone = all(g(s + 1) > g(s) for s in range(4 * scan))  # rho>1 => strictly increasing
    # (P3) finite core: c+t < S0 all satisfy bs1>=1 (exact).
    p3_core = all(q1_holds(c, t) for c in range(S0 + 1) for t in range(S0 + 1) if c + t < S0)
    proved = p0_reduction and p1_identity and p1_positive and p2_threshold and p2_monotone and p3_core
    # independent sanity: bs1>=1 across the whole scan box (redundant with P1+P2+P3 but a direct check).
    direct_scan = all(q1_holds(c, t) for c in range(scan) for t in range(scan))
    return {
        "P0_reduction_bs1_eq_bushstar_k1": p0_reduction,
        "P1_crude_identity_16D_9N": p1_identity,
        "P1_crude_positive_DN_gt_9_16": p1_positive,
        "P2_escape_threshold_S0_exact": p2_threshold,
        "P2_escape_g_monotone_increasing": p2_monotone,
        "P3_finite_core_ct_lt_S0": p3_core,
        "direct_scan_consistency": direct_scan,
        "S0": S0,
        "q1_proved": bool(proved),
        "statement": ("PROVEN for ALL integers c,t>=0: logPhi(B(c,1,t)) <= 0 (the k=1 bush slice, Q1). "
                      "bs1(c,t)=K*rho^(c+t)*(D/N)^11 with the exact integer identity 16D-9N=72t+36c+45>0 "
                      "(=> D/N>9/16) and geometric escape g(s)=K*rho^s*(9/16)^11>=1 for s>=22, finite core "
                      "c+t<22 checked exactly. The k=1 slice has a UNIFORM positive gap (min -logPhi=omega "
                      "at the ARM), so no marginal-tie obstruction here. q1_proved = True."),
    }


if __name__ == "__main__":
    for key, val in verify().items():
        print(f"{key}: {val}")
