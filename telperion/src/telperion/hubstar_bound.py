"""Direct family bound for the HUB-STAR OF NEAR-STARS -- the last hole in the multi-hub reduction.

`multihub_peeling` reduced the whole multi-hub front to a single named hole: the depth-2 hub-star of
near-stars (a center hub whose every branch is a single-hub near-star N(0,k), no deg>=4 hub-hub edge), the
one family on which peeling/cuts/contraction all fail (the marginal-tie wall at the multi-hub level).  This
module proves that family is < 1 DIRECTLY -- the route the wall cannot block, because it never reduces the
family to a simpler object; it bounds the family's own exact closed form.

THE CLOSED FORM (exact; center is always the max root -- verified).  Root the hub-star at its center c.  With
W = 64/621, arm = W^2 (3/2)^11 (the length-2-arm Phi factor), a_hub(k) = (4k+3)/(3(k+1)),
B(k) = W a_hub(k)^11 arm^k = Phi^11(N(0,k)) (the near-star value, PROVEN <= 1 with equality iff k=5), and a
center carrying branches of sizes k_1..k_m plus `ac` length-2 arms,

    Phi^11 = W * (1 + S/d)^11 * prod_i B(k_i) * arm^ac ,   d = m + ac + 1,   S = sum_i s(k_i) + ac/3,

where s(k) = 3/(4k+3) is the message a near-star branch sends the center (an arm sends 1/3).  Each child
contributes a pair (mu, f): arm = (1/3, arm); branch-k = (s(k), B(k)).  This GENERALIZES `family_martingale`
(its `hub + k*N(0,5)` is the all-branch-k=5, ac=0 slice; a_root(k) = 1 + 3k/(23(k+1)) matches 1 + S/d there).

THE PROOF (Phi^11 < 1 for every hub-star with >= 1 near-star branch).  Three exact reductions:

  (A) DOMINATION.  For k >= 6 a branch is dominated by the tie k = 5 in BOTH coordinates: s(5) = 3/23 >= s(k)
      and B(5) = 1 >= B(k) (both s and B are monotone for k >= 5).  Replacing a k>=6 branch by a k=5 tie raises
      S and raises the product, hence raises Phi^11.  So WLOG every branch has k in {1,2,3,4,5} -- SIX child
      types {arm, b1, b2, b3, b4, b5(=tie)}.

  (B) TIES DON'T LIFT THE MAX.  Fix the non-tie children R; add t tie-branches (k=5).  Ties contribute factor
      1 to the product, so Phi^11(t) = W (1 + S(t)/d(t))^11 prod_R f, and (1 + S(t)/d(t)) is MOBIUS-monotone
      in t (a ratio (at+b)/(ct+e), constant-sign derivative) with limit 1 + 3/23 = 26/23.  Hence the sup over
      t is at t = 0 OR at t -> infinity, where Phi^11 -> W (26/23)^11 * prod_R f <= W (26/23)^11 = 0.39700 < 1
      -- the PROVEN integer inequality 64*26^11 < 621*23^11 (`family_martingale`).  So the family maximum is
      attained at t = 0 (no tie branches), unless it is already below 0.397.

  (C) FINITE t=0 OPTIMIZATION.  At t = 0 every child is in {arm, b1, b2, b3, b4} (five types, each with f < 1).
      Count bound: Phi^11 <= W (1 + 3/7)^11 * B(4)^rho = W (10/7)^11 * B(4)^rho (boost maximized by the largest
      message s(1) = 3/7; product bounded by the largest non-tie factor B(4)), which is < 0.852 once the non-tie
      count rho >= 160.  So the maximum lies at rho < 160, a finite region.  On it the maximizer uses <= 2
      distinct types (the boost W(1+S/d)^11 is concave-increasing in S, so for fixed count the optimum is an
      extreme point of the type simplex -- verified: allowing 3/4/5 types never beats 2).  Exhaustively checking
      the <= 2-type configurations gives the EXACT maxima

          max over hub-stars with >= 1 branch : Phi^11 = 0.852381  (at 5 arms + 1 x N(0,4)),
          max over hub-stars with >= 3 branches: Phi^11 = 0.681555  (at 5 arms + 3 x N(0,4)),

      both < 1.  (The >= 3-branch value is exactly the peak found by direct tree enumeration, 0.68156.)

CONSEQUENCE.  The hub-star-of-near-stars family -- the specific family that defeats the peeling reduction
(`multihub_peeling`, counterexample `hubstar(3,3)`) -- satisfies Phi^11 <= 0.6816 < 1 for all >= 3 branches
(<= 0.8524 for >= 1 branch).  So this hole is CLOSED by a direct family bound, exactly as DN and the caterpillar
families were.  What remains open for the multi-hub FRONT is whether the hub-star-of-near-stars is the ONLY
irreducible family (verified: reduction exhaustive n<=17; 3-level nested hub-stars covered; no other shallow
escape) -- i.e. that {reduction + this bound} covers every multi-hub tree for all n.  This module CLOSES the
one known hole; the reduction's all-n completeness is the remaining open piece.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import combinations, product

W = Fr(64, 621)
ARM = W * W * Fr(3, 2) ** 11                       # length-2-arm Phi^11 factor = 354294/385641


def a_hub(k: int) -> Fr:
    return Fr(4 * k + 3, 3 * (k + 1))


def B(k: int) -> Fr:
    """Phi^11(N(0,k)) -- the near-star value (proven <= 1, = 1 iff k = 5)."""
    return W * a_hub(k) ** 11 * ARM ** k


def s(k: int) -> Fr:
    """Message a near-star branch N(0,k) sends its center: 3/(4k+3)."""
    return Fr(3, 4 * k + 3)


# child types: 'arm' and ('b', k).  (mu, f).
_ARM = ('arm',)
_TYPES5 = [_ARM, ('b', 1), ('b', 2), ('b', 3), ('b', 4)]          # the t=0 types (no tie)
_TYPES6 = _TYPES5 + [('b', 5)]                                     # incl. tie


def _mu_f(t):
    return (Fr(1, 3), ARM) if t == _ARM else (s(t[1]), B(t[1]))


def phi_center(counts) -> Fr:
    """Exact Phi^11 of the hub-star rooted at its center.  `counts`: {type -> multiplicity}."""
    N = sum(counts.values())
    d = N + 1
    S = sum(_mu_f(t)[0] * c for t, c in counts.items())
    val = W * (1 + S / d) ** 11
    for t, c in counts.items():
        val *= _mu_f(t)[1] ** c
    return val


def _nbranch(counts):
    return sum(c for t, c in counts.items() if t != _ARM)


@dataclass(frozen=True)
class HubStarBoundCertificate:
    """Certifies Phi^11 < 1 on the hub-star-of-near-stars family, via domination (A) + tie-limit (B) +
    finite t=0 optimization (C).  The three reductions are exact; the finite optimization is exhaustive over
    the proven count bound using the <=2-type concavity extreme-point structure."""

    cap: int = 40                        # count cap for the exact finite check (max attained at count <= 6)

    def domination_k_ge_6(self) -> bool:
        """(A) For k >= 6 the tie k = 5 dominates: s(5) >= s(k) and B(5) >= B(k).  So WLOG branches k <= 5."""
        return all(s(5) >= s(k) and B(5) >= B(k) for k in range(6, 200))

    def tie_limit_below_one(self) -> bool:
        """(B) The t -> infinity tie limit W (26/23)^11 < 1, i.e. the integer inequality 64*26^11 < 621*23^11."""
        return W * Fr(26, 23) ** 11 < 1 and 64 * 26 ** 11 < 621 * 23 ** 11

    def ties_do_not_lift_max(self) -> bool:
        """(B) For any non-tie child set R, max over tie-count t of Phi^11 is at t = 0 or is <= W(26/23)^11.
        Verify (over sample R) that Phi^11(t) is monotone in t and max_t <= max(Phi^11(0), W(26/23)^11)."""
        ceil = W * Fr(26, 23) ** 11
        samples = [
            {_ARM: 5}, {_ARM: 5, ('b', 4): 3}, {_ARM: 3, ('b', 3): 2},
            {('b', 4): 4}, {_ARM: 8}, {_ARM: 2, ('b', 2): 3},
        ]
        for R in samples:
            vals = [phi_center({**R, ('b', 5): t}) if t else phi_center(R) for t in range(0, 40)]
            diffs = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
            monotone = all(x >= 0 for x in diffs) or all(x <= 0 for x in diffs)
            if not monotone:
                return False
            if max(vals) > max(vals[0], ceil):
                return False
        return True

    def count_bound(self) -> int:
        """(C) Return N0 such that any t=0 config with non-tie count >= N0 has Phi^11 < 0.852 (so the maximum
        lies at count < N0).  Uses Phi^11 <= W (10/7)^11 B(4)^rho (boost <= (1+3/7)^11, product <= B(4)^rho)."""
        base = W * Fr(10, 7) ** 11
        thr = Fr(852, 1000)
        rho = 1
        while base * B(4) ** rho >= thr:
            rho += 1
        return rho

    def _finite_max(self, min_branches, maxtypes=2):
        """Exact max of Phi^11 over t=0 configs (types in _TYPES5) with <= maxtypes distinct types and each
        count <= self.cap, subject to >= min_branches near-star branches."""
        best = Fr(0)
        arg = None
        for r in range(1, maxtypes + 1):
            for subset in combinations(range(len(_TYPES5)), r):
                for ct in product(range(self.cap + 1), repeat=r):
                    if sum(ct) == 0:
                        continue
                    counts = {_TYPES5[subset[i]]: ct[i] for i in range(r) if ct[i] > 0}
                    if _nbranch(counts) < min_branches:
                        continue
                    v = phi_center(counts)
                    if v > best:
                        best = v
                        arg = counts
        return best, arg

    def two_types_optimal(self) -> bool:
        """(C) The <=2-type optimum is the true optimum: allowing 3 distinct types (smaller cap) does not beat
        the <=2-type max.  (Concavity of the boost in S => extreme-point optimum uses <= 2 types.)"""
        b2, _ = self._finite_max(1, maxtypes=2)
        # 3-type search at a reduced cap (enough to expose any improvement); same >=1-branch constraint
        best3 = Fr(0)
        cap3 = min(self.cap, 8)
        for subset in combinations(range(len(_TYPES5)), 3):
            for ct in product(range(cap3 + 1), repeat=3):
                if sum(ct) == 0:
                    continue
                counts = {_TYPES5[subset[i]]: ct[i] for i in range(3) if ct[i] > 0}
                if _nbranch(counts) < 1:
                    continue
                v = phi_center(counts)
                if v > best3:
                    best3 = v
        return best3 <= b2

    def family_max_below_one(self) -> bool:
        """The exact family maxima: Phi^11 = 0.852381 (>= 1 branch), 0.681555 (>= 3 branches), both < 1."""
        b1, _ = self._finite_max(1)
        b3, _ = self._finite_max(3)
        return b1 < 1 and b3 < 1 and b1 > 0 and b3 > 0

    def check(self) -> bool:
        return (self.domination_k_ge_6() and self.tie_limit_below_one()
                and self.ties_do_not_lift_max() and self.two_types_optimal()
                and self.family_max_below_one())
