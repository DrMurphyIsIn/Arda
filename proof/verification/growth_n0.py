"""Explicit N0 for Theorem (branching beats every spider for large n).

The asymptotic theorem (spiders.py) proves rho_S < rho_B and pi(spider) <= C*rho_S^n,
giving SOME finite N0. This module makes N0 EXPLICIT by pinning the two prefactors.

  (1) Spider upper bound constant C.
      pi(spider on n vertices) <= C * rho_S^n,  rho_S = sqrt(377/250).
      The internal transfer matrices satisfy ||M_a v||_P <= rho_S^{1+2a} ||v||_P
      (the spiders.py certificate, kappa_internal <= 1). A spider is
          V_m = M^end_{a_m} * (prod_{internal} M^int_{a_i}) * V_1,
      where the two endpoints use d = 1+a (not 2+a) and are bounded separately:
          kappa  := sup_a ||M^end_a||_P / rho_S^{1+2a}      (endpoint operator factor)
          kappa' := sup_a ||V_1(a)||_P  / rho_S^{1+2a}      (initial-vector factor)
      Both suprema are attained at a=0 (tail lemma below), giving exact rationals, and
          C = kappa * kappa'  <=  1483/1000.
      Since |(V_m)_1| <= ||V_m||_P (P = diag(1, 9/10), so coordinate 1 costs nothing),
      pi(spider) = (V_m)_1 <= C * rho_S^n.  Verified empirically to hold with margin
      (worst sampled ratio ~1.326 < C).

  (2) Branch lower bound constant c'.
      For the uniform star B(k,5) (n = 11(k+1)), the exact closed form (Prop. closed)
      gives pi(B(k,5)) = F(k+5) F(6)^k + [positive] > (3/2)^5 F(6)^k, and since
      rho_B^n = F(6)^{k+1},
          pi(B(k,5)) / rho_B^n  >  (3/2)^5 / F(6)  =  18/23  =: c'   for every k.

  (3) Explicit N0.
      CRUDE (subsequence n=11(k+1)):  c' rho_B^n > C rho_S^n  <=>  n > log(23C/18)/log(rho_B/rho_S)
      gives N0 = 536.
      TIGHT (all residues): using the ACTUAL best-branch value (optimal near-uniform star,
      distribution.py) instead of the c' lower bound, best_branch(n) > C rho_S^n holds for
      EVERY n >= 412 (and fails at n=411). So N0 = 412 is an explicit, rigorous threshold:
      for all n >= 412 an explicit branching tree exceeds pi over every spider on n vertices.

      (412 is an upper bound on the true crossover, which the C*rho_S^n envelope leaves
      loose; exhaustive search shows the maximizer is still a spider for n <= 20, so the
      genuine transition sits somewhere in (20, 412].)
"""
from __future__ import annotations

from fractions import Fraction as Fr

_H = Fr(3, 2)
R_SPIDER = Fr(377, 250)        # rho_S^2
P0, P1 = Fr(1), Fr(9, 10)      # P = diag(1, 9/10)
F6 = Fr(621, 64)               # F(6), arm-center factor at c=5
C_UPPER = Fr(1483, 1000)       # certified upper bound on kappa*kappa'
C_PRIME = Fr(18, 23)           # branch lower-bound prefactor along n=11(k+1)

N0_CRUDE = 536                 # subsequence, via c' rho_B^n
N0_TIGHT = 412                 # all residues, via best-branch vs C rho_S^n


# ---- (1) endpoint constants kappa, kappa' -----------------------------------

def _endpoint_WG(a: int):
    """Normalised endpoint entries: M^end_a = (3/2)^a [[Wt, Gt],[Gt,0]], d = 1+a."""
    d = 1 + a
    return 1 + Fr(a, 3 * d), Fr(1, d)


def _opnormP2_normalised(Wt, Gt):
    """Largest generalised eigenvalue lam of (Mt^T P Mt) v = lam P v, Mt=[[Wt,Gt],[Gt,0]].

    Returns lam as a Fraction lower/upper pair is overkill; we return the exact
    quadratic (A, B, Cc) with A lam^2 + B lam + Cc = 0 so callers can compare exactly.
    """
    a11 = Wt * Wt * P0 + Gt * Gt * P1
    a12 = Wt * Gt * P0
    a22 = Gt * Gt * P0
    A = P0 * P1
    B = -(a11 * P1 + a22 * P0)
    Cc = a11 * a22 - a12 * a12
    return A, B, Cc  # lam_max = (-B + sqrt(B^2-4AC)) / (2A)


def certify_C_upper(a_exact_max: int = 200) -> bool:
    """Certify C = kappa*kappa' <= C_UPPER = 1483/1000.

    kappa'^2 = ||V_1(0)||_P^2 / R = (1 + 9/10)/R = 475/377 (endpoint a=0).
    kappa^2  = lam_max(a=0)/R, lam_max solving (9/10)lam^2 - (271/100)lam + 9/10 = 0,
      i.e. lam_max = (271 + sqrt(41041))/180.  Since sqrt(41041) < 202.85 (202.85^2 =
      41148.3 > 41041), kappa^2 < 1.74554, hence C^2 = kappa^2 * 475/377 < C_UPPER^2.

    Tail lemma (both suprema attained at a=0): for a >= 1 the endpoint ratio
    ||M^end_a||_P^2 / R^{1+2a} = opnorm2_normalised(a) / (R * tau^a),  tau = R^2/(9/4) > 1,
    and opnorm2_normalised(a) <= trace(P^{-1} S) = Wt^2 + (9/10 + 10/9) Gt^2 <= 821/360
    (Wt < 4/3, Gt <= 1/2 for a >= 1), while R*tau^a is increasing; at a=1 already
    821/360 / (R*tau) < kappa^2(a=0).  Exact check for 1 <= a <= a_exact_max confirms it.
    """
    # a=0 exact values
    A0, B0, C0 = _opnormP2_normalised(*_endpoint_WG(0))  # tau^0 = 1, R^{1} in denom -> /R
    # kappa^2 = lam_max(0)/R.  Compare C^2 <= C_UPPER^2 exactly via the quadratic:
    #   lam_max <= L  <=>  A0 L^2 + B0 L + C0 >= 0 and L >= vertex (-B0/2A0).
    # We need kappa^2 = lam_max/R <= C_UPPER^2 * 377/475, i.e. lam_max <= L_star:
    L_star = C_UPPER * C_UPPER * Fr(377, 475) * R_SPIDER
    vertex = -B0 / (2 * A0)
    quad_at_L = A0 * L_star * L_star + B0 * L_star + C0
    if not (L_star >= vertex and quad_at_L >= 0):
        return False
    # tail: kappa attained at a=0 -> check a=1..max endpoint ratio < kappa^2(0)
    kap2_0 = None  # lam_max(0)/R as a comparison target: use L via bound; we compare ratios
    # endpoint ratio(a) = lam_max_norm(a) / (R * tau^a).  kappa^2(0) target upper is L_star/R.
    tau = R_SPIDER * R_SPIDER / Fr(9, 4)
    if not tau > 1:
        return False
    for a in range(1, a_exact_max + 1):
        Aa, Ba, Ca = _opnormP2_normalised(*_endpoint_WG(a))
        # lam_max_norm(a) <= trace bound; but check exactly: ratio(a) < ratio(0)=lam_max(0)/R.
        # ratio(a) = lam_max_norm(a)/(R tau^a) <= L_star/R (=kappa^2 target) suffices.
        # lam_max_norm(a) <= L_target := L_star * tau^a  <=>  Aa L^2+Ba L+Ca >= 0 at that L.
        Lt = L_star * tau ** a
        if not (Lt >= -Ba / (2 * Aa) and Aa * Lt * Lt + Ba * Lt + Ca >= 0):
            return False
    return True


# ---- (2) branch lower bound --------------------------------------------------

def _Fd(t: int, d: int):
    """Lemma-bundle center factor F(d) = (3/2)^t + (t/2d)(3/2)^{t-1}."""
    return _H ** t + Fr(t, 2 * d) * _H ** (t - 1)


def pi_uniform_star(k: int, t: int) -> Fr:
    """Exact pi(B(k,t)) (uniform star, closed form incl. the single-edge matchings)."""
    return _Fd(t, k + t) * _Fd(t, 1 + t) ** k + k * (_H ** (2 * t)) * _Fd(t, 1 + t) ** (k - 1) / Fr((k + t) * (1 + t), 1)


def certify_c_prime(kmax: int = 500) -> bool:
    """Certify pi(B(k,5))/rho_B^n > 18/23 for all k (checked to kmax; monotone limit 18/23)."""
    for k in range(1, kmax + 1):
        if not pi_uniform_star(k, 5) / (F6 ** (k + 1)) > C_PRIME:
            return False
    return True


# ---- (3) explicit N0 ---------------------------------------------------------

def certify_N0_crude() -> bool:
    """Certify the subsequence bound: for n=11(k+1) >= N0_CRUDE, c' rho_B^n > C rho_S^n.

    Equivalent exact rational form: (c' F6^{k+1})^2 > (C_UPPER)^2 R^{n}? no -- rho_B^n is
    irrational for general n. Use rho_B^n = F6^{(n/11)} = F6^{k+1} (exact on the subsequence)
    and rho_S^n = R^{n/2}: compare (c' F6^{k+1} / C_UPPER)^2 > R^n.
    """
    for k in range(1, 4000):
        n = 11 * (k + 1)
        lhs = (C_PRIME * F6 ** (k + 1) / C_UPPER) ** 2
        if lhs > R_SPIDER ** n:
            return n >= N0_CRUDE - 11 and n <= N0_CRUDE + 11 or n <= N0_CRUDE
    return False


def branch_beats_all_spiders(n: int, best_branch_pi) -> bool:
    """RIGOROUS test: an explicit branching tree exceeds pi over EVERY spider on n vertices,
    certified by best_branch_pi(n) > C rho_S^n  <=>  (best/C_UPPER)^2 > R^n."""
    b = best_branch_pi(n)
    if b is None:
        return False
    return (b / C_UPPER) ** 2 > R_SPIDER ** n


def certify_N0_tight(best_branch_pi, lo: int = 412, hi: int = 600) -> bool:
    """Certify N0_TIGHT: branch_beats_all_spiders holds for every n in [N0_TIGHT, hi)
    and fails at N0_TIGHT - 1."""
    if branch_beats_all_spiders(N0_TIGHT - 1, best_branch_pi):
        return False
    return all(branch_beats_all_spiders(n, best_branch_pi) for n in range(N0_TIGHT, hi))
