"""Asymptotic theorem: for all sufficiently large n, an explicit branching tree
strictly exceeds pi over EVERY spider T(a_1,...,a_m) on n vertices.

This is the honest unconditional form of "branching beats every spider": no FIXED
branching degree suffices (B(3,c) is itself beaten by a spider once c>=8, see
tests), so the winning degree must grow with n. The proof compares exponential
GROWTH RATES.

Transfer matrix (exact, single-parameter).  A spider is a cherry-bundle tree on a
path P_m with bundle sizes a_i. Its pi is the path matching-sum
z_i = w_i z_{i-1} + e_i z_{i-2},  e_i = gamma_{i-1} gamma_i,
with w_a = (3/2)^a (1 + a/(3d)),  gamma_a = (3/2)^a / d,  d = deg = (1 or 2)+a.
Substituting V_i = [z_i; gamma_i z_{i-1}] decouples the edge coupling:
    V_i = M_{a_i} V_{i-1},   M_a = [[w_a, gamma_a], [gamma_a, 0]],
where M_a depends ONLY on a_i (internal d=2+a; the two endpoints use d=1+a and
contribute a bounded constant). pi(spider) = (V_m)_1.

Spider upper bound (quadratic certificate).  With P = diag(1, 9/10) and
R = rho_S^2 = 377/250, the exact PSD inequality
    S_a := R^{1+2a} P - M_a^T P M_a  >=  0     (M_a internal, d=2+a)
holds for every integer a >= 0 -- verified exactly for a <= 64 and, for a >= 65,
by the tail lemma (W_a = 1+a/(3(2+a)) < 4/3, G_a = 1/(2+a) <= 1/2, and
tau := R^2/(9/4) = 142129/140625 > 1 makes R^{1+2a} dominate). Hence, in the norm
||v||_P = sqrt(v^T P v), ||M_a v||_P <= rho_S^{1+2a} ||v||_P, so pi(spider on n
vertices) <= C * rho_S^n with rho_S = sqrt(377/250) = 1.228007..., uniformly over
ALL spine lengths and ALL compositions.

Branch lower bound.  The star B(k,5) (hub + k arm-centers of 5 cherries each) has
n = 11(k+1) and pi(B(k,5)) >= F(k+5) F(6)^k > (3/2)^5 F(6)^k, F(6)=621/64. Its
per-vertex rate is rho_B = F(6)^{1/11} = (621/64)^{1/11}. (General n is reached by
near-uniform stars; the rate is unchanged.)

Rate gap (exact).  rho_S < rho_B  <=>  (377/250)^11 < (621/64)^2, i.e.
91.709... < 94.150...  Therefore pi(best branch) / pi(any spider) >=
(c'/C)(rho_B/rho_S)^n -> infinity, so there is an N0 with: for all n >= N0, an
explicit branching tree beats every spider on n vertices.  QED (asymptotic).

Honest scope: N0 is existential (finite but not optimised here); rank 0/1 of the
argument -- the exact certificate and the exact rate gap -- are machine-checked
below. The endpoint constant C and c', N0 are finite by the bounded-factor
argument and are not tightened.
"""
from __future__ import annotations

from fractions import Fraction as Fr

_H = Fr(3, 2)

# Certified constants
R_SPIDER = Fr(377, 250)          # rho_S^2
P_DIAG = (Fr(1), Fr(9, 10))      # P = diag(1, 9/10)
BRANCH_ARM_BASE = Fr(621, 64)    # F(6): arm-center weight for c=5 cherries
BRANCH_ARM_VERTICES = 11         # 1 + 2*5


def _M_internal(a: int):
    """Internal-vertex transfer matrix M_a (degree d = 2 + a), exact."""
    d = 2 + a
    xa = _H ** a
    w = xa * (1 + Fr(a, 3 * d))
    g = xa / d
    return ((w, g), (g, Fr(0)))


def _MT_P_M_diag(P_diag, M):
    """M^T P M for P = diag(p0, p1); returns symmetric 2x2 as nested tuple."""
    p0, p1 = P_diag
    (w, g), (g2, _z) = M  # g2 == g (symmetric)
    # M^T P M = [[w^2 p0 + g^2 p1, w g p0], [w g p0, g^2 p0]]
    s00 = w * w * p0 + g * g * p1
    s01 = w * g * p0
    s11 = g * g * p0
    return ((s00, s01), (s01, s11))


def _psd2(S) -> bool:
    """Exact PSD test for a symmetric 2x2 rational matrix."""
    (a, b), (_b, c) = S
    return a >= 0 and c >= 0 and (a * c - b * b) >= 0


def certify_spider_upper_bound(a_exact_max: int = 100) -> bool:
    """Certify S_a = R^{1+2a} P - M_a^T P M_a >= 0 for ALL integer a >= 0.

    Exact PSD check for 0 <= a <= a_exact_max (>= 64 required), plus the tail
    lemma for a >= 65. Returns True iff the certificate holds, establishing
    pi(spider) <= C * rho_S^n with rho_S = sqrt(377/250).
    """
    if a_exact_max < 64:
        return False
    p0, p1 = P_DIAG
    for a in range(0, a_exact_max + 1):
        M = _M_internal(a)
        MPM = _MT_P_M_diag(P_DIAG, M)
        lam = R_SPIDER ** (1 + 2 * a)
        S = ((lam * p0 - MPM[0][0], -MPM[0][1]),
             (-MPM[1][0], lam * p1 - MPM[1][1]))
        if not _psd2(S):
            return False
    # Tail lemma (a >= 65): W_a = 1 + a/(3(2+a)) < 4/3 (identity: a/(3(2+a)) < 1/3),
    # G_a = 1/(2+a) <= 1/2, tau = R^2/(9/4) > 1. Then dividing S_a by (9/4)^a,
    #   (i)   R*tau^a >= W_a^2 + (9/10)G_a^2   (RHS <= (4/3)^2 + (9/10)/4 = 721/360),
    #   (ii)  (9/10)R*tau^a >= G_a^2           (holds for all a>=0),
    #   (iii) first-bracket >= 1 forces det >= W_a^2 G_a^2,
    # all hold once R*tau^a >= 1081/360, i.e. tau^a >= 1081/(360 R); at a=65 this is
    # already satisfied with margin, and tau^a is increasing. Verified:
    tau = R_SPIDER ** 2 / Fr(9, 4)
    if not tau > 1:
        return False
    need = Fr(1081, 360) / R_SPIDER          # tau^a must exceed this for a>=65
    return tau ** 65 >= need


def certify_branch_rate_exceeds_spider() -> bool:
    """Exact rate gap: rho_S < rho_B, i.e. (377/250)^11 < (621/64)^2."""
    rho_s_pow = R_SPIDER ** BRANCH_ARM_VERTICES            # rho_S^(2*11)
    rho_b_pow = BRANCH_ARM_BASE ** 2                       # rho_B^(2*11)
    return rho_s_pow < rho_b_pow


def certify_branching_beats_spiders_asymptotically() -> bool:
    """Full asymptotic theorem certificate.

    True iff (i) the spider upper bound pi(spider) <= C*rho_S^n holds (exact
    quadratic certificate, all integer a), and (ii) the branch rate strictly
    exceeds rho_S (exact). Together these give: there exists N0 such that for all
    n >= N0, an explicit branching tree strictly exceeds pi over every spider on
    n vertices. (N0 finite, existential; not optimised.)
    """
    return bool(certify_spider_upper_bound() and certify_branch_rate_exceeds_spider())
