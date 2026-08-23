"""Child-cavity j-pivot: an exact generalization of the tie-children pivot (2026-08-22).

CONTEXT.  near_star_arithmetic_proof.py proved the 1-parameter near-star family (STAR,
s=c+k).  tie_children_extension.py proved the 2-parameter TIE-CHILDREN family (s cherry/arm
units + j EXACT-TIE children), whose j-direction is governed by the pivot 14s-9.  This module
generalizes that pivot to an ARBITRARY child cavity mu, giving one exact identity and one
exact-verified provable reduction lemma.

HONEST SCOPE.  This does NOT close the Brualdi-Goldwasser crux (conjecture1_proved = False).
It is a partial reduction: it disposes of the SMALL-CAVITY region (mu <= s/(3(s+1))) with
IDENTICAL children, reducing that region to the already-proven STAR base case.  The open hard
core -- the interior peak over NON-tie children with mu > s/(3(s+1)) -- is untouched (the
worst child sits slightly ABOVE the tie cavity; empirically the whole 3-parameter family
{s cherry/arm units + j copies of near-star N(0,r)} is <= 1 with a UNIQUE global max at the
tie (s,j)=(5,0), verified over r<=14, s<=59, j<=79, but its interior-peak bound is NOT proven).

================================================================================================
THE EXACT j-PIVOT IDENTITY (verified, all rational)
================================================================================================
Consider a node with s cherry/arm units (c=s cherries) and j IDENTICAL deep children, each of
cavity mu (rational, 0 < mu <= 1) and amplitude-factor A = Phi^11(child) in (0,1].  From the
exact cavity recursion its Phi^11 is (verified against the recursion to exact equality):

    Phi^11(s,j) = (3/2)^{11 s} (64/621)^{1+2s} (t(j)/d3(j))^11 A^j,
        t(j)  = 3j + 3 + 4s + 3 j mu,      d3(j) = 3 (j + 1 + s).

The one-step change of the rational factor t/d3 is controlled by the exact identity

    t(j) d3(j+1) - t(j+1) d3(j) = -3 (3 mu (s+1) - s)         (J-PIVOT)

which is INDEPENDENT of j.  So the sign of the pivot 3 mu (s+1) - s alone decides whether t/d3
rises or falls as a child is added.  At mu = 3/23 (the tie cavity) this specializes to
3 mu (s+1) - s = (9 - 14 s)/23, recovering the TIE-CHILDREN pivot 14 s - 9.

================================================================================================
THE PROVABLE REDUCTION LEMMA (exact-verified)
================================================================================================
LEMMA.  If mu <= s/(3(s+1)) and A <= 1, then Phi^11(s,j) <= Phi^11(s,0) for every j >= 0.

PROOF.  mu <= s/(3(s+1))  <=>  3 mu (s+1) - s <= 0  <=>  (J-PIVOT) >= 0  <=>
t(j) d3(j+1) >= t(j+1) d3(j)  <=>  t(j)/d3(j) >= t(j+1)/d3(j+1)  (all positive).  Hence t/d3 is
non-increasing in j, so (t/d3)^11 is non-increasing; A^j is non-increasing (A <= 1); their
product Phi^11(s,j) is non-increasing in j.  QED.

CONSEQUENCE.  On the small-cavity region the node's factor is maximized at j=0, i.e. at the
STAR family, which is Phi^11 <= 1 (near_star_arithmetic_proof, PROVEN).  So this region needs
no new envelope.  The complementary region mu > s/(3(s+1)) (which contains the tie itself,
mu=3/23 at s<5) is where the open master inequality lives.

Everything is exact rational (fractions.Fraction); no float at any decision point.
"""
from __future__ import annotations

import random
from fractions import Fraction as Fr

ARM = (0, [(0, [])])


def phi11_cav(T):
    """(cavity m, Phi^11) for rooted tree T=(cherries,[children]), exact rational."""
    c, kids = T
    ch = [phi11_cav(k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + c
    t = 3 * d + c + 3 * S
    fac = Fr(3, 2) ** (11 * c) * Fr(64, 621) ** (1 + 2 * c) * (Fr(t, 3 * d)) ** 11
    for _, p in ch:
        fac *= p
    return Fr(3, t), fac


def NS(r):
    """near-star N(0,r): a root with r arm children."""
    return (0, [ARM] * r)


def t_of(j, s, mu):
    return 3 * j + 3 + 4 * s + 3 * j * mu


def d3_of(j, s):
    return 3 * (j + 1 + s)


def phi11_closed(s, j, mu, A):
    """Closed form for a node with s cherries + j identical (mu,A) children."""
    return (Fr(3, 2) ** (11 * s) * Fr(64, 621) ** (1 + 2 * s)
            * (Fr(t_of(j, s, mu), d3_of(j, s))) ** 11 * A ** j)


# ---------------------------------------------------------------- verifications ----

def verify_closed_form_matches_recursion(trials=400, seed=1):
    """The closed form equals the exact cavity recursion, for near-star children."""
    rng = random.Random(seed)
    fails = 0
    for _ in range(trials):
        s = rng.randint(0, 12)
        j = rng.randint(0, 12)
        r = rng.randint(0, 12)
        mu = Fr(3, 4 * r + 3)
        A = phi11_cav(NS(r))[1]
        rec = phi11_cav((s, [NS(r)] * j))[1]
        if phi11_closed(s, j, mu, A) != rec:
            fails += 1
    return fails == 0


def verify_jpivot_identity(trials=50000, seed=7):
    """(J-PIVOT): t(j)d3(j+1) - t(j+1)d3(j) = -3(3 mu (s+1) - s), for all rational mu."""
    rng = random.Random(seed)
    fails = 0
    for _ in range(trials):
        s = rng.randint(0, 40)
        j = rng.randint(0, 40)
        mu = Fr(rng.randint(1, 60), rng.randint(1, 60))
        lhs = t_of(j, s, mu) * d3_of(j + 1, s) - t_of(j + 1, s, mu) * d3_of(j, s)
        if lhs != -3 * (3 * mu * (s + 1) - s):
            fails += 1
    return fails == 0


def verify_tie_pivot_specialization():
    """At mu=3/23 the pivot 3 mu (s+1) - s = (9 - 14 s)/23 (recovers TIE-CHILDREN 14s-9)."""
    mu = Fr(3, 23)
    return all(3 * mu * (s + 1) - s == Fr(9 - 14 * s, 23) for s in range(0, 200))


def verify_reduction_lemma(trials=200000, seed=11):
    """LEMMA: mu <= s/(3(s+1)) and A <= 1 => Phi^11(s,j) <= Phi^11(s,0), for all rational mu,A."""
    rng = random.Random(seed)
    fails = 0
    tested = 0
    for _ in range(trials):
        s = rng.randint(1, 40)
        cap = Fr(s, 3 * (s + 1))
        mu = Fr(rng.randint(0, cap.numerator * 5), cap.denominator * 5)
        if mu <= 0 or mu > cap:
            continue
        A = Fr(rng.randint(1, 1000), 1000)
        j = rng.randint(1, 30)
        tested += 1
        if phi11_closed(s, j, mu, A) > phi11_closed(s, 0, mu, A):
            fails += 1
    return fails == 0 and tested > 1000


def verify_family_validated(rmax=14, smax=60, jmax=80):
    """VALIDATION (not a proof): the 3-parameter family {s cherry/arm units + j copies of N(0,r)}
    has Phi^11 <= 1 on the box, with equality ONLY at the global tie (s,j)=(5,0) (any r)."""
    worst = Fr(0)
    eqs = []
    for r in range(0, rmax + 1):
        mu = Fr(3, 4 * r + 3)
        A = phi11_cav(NS(r))[1]
        for s in range(0, smax):
            for j in range(0, jmax):
                v = phi11_closed(s, j, mu, A)
                if v > worst:
                    worst = v
                if v == 1:
                    eqs.append((s, j, r))
    only_tie = all(s == 5 and j == 0 for (s, j, r) in eqs)
    return worst <= 1 and only_tie


def certify():
    return {
        "closed_form_matches_recursion": verify_closed_form_matches_recursion(),
        "jpivot_identity_exact": verify_jpivot_identity(),
        "tie_pivot_specialization_14s_minus_9": verify_tie_pivot_specialization(),
        "reduction_lemma_small_cavity_verified": verify_reduction_lemma(),
        "family_validated_le_1_unique_tie": verify_family_validated(),
        # HONEST boundary: the interior peak (mu > s/(3(s+1)), the worst-child-above-tie regime)
        # is NOT proven.  This module closes only the small-cavity reduction.
        "full_arbitrary_children_crux_closed": False,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2))
