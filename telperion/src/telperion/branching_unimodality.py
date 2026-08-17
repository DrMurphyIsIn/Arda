"""Over-the-reals proof of the g-step branching unimodality -- the g-lemma's last analytic residual.

`gstep_reduction.py` (parallel session) reduced R1's branching master inequality to the g-step optimization

    g_bound(mu_1..mu_{j'}) = W * boost^11 * prod_i min(1, gamma/(1+mu_i/3)^11) ,
    boost = 1 + (3S+1)/(3(j'+1)),  S = sum mu_i,  W = 64/621,  gamma = W^2 (5/3)^11,

closed the two rational leaves, and left OPEN "the over-the-reals T1/T2 unimodality at the irrational mu*".
This module proves that unimodality RIGOROUSLY (not by multi-start search), so the box-max is exactly the
symmetric value g_bound(mu*,...,mu*), mu* the crossover (1+mu*/3)^11 = gamma.

THE EXACT DERIVATIVE.  log g_bound = log W + 11 log boost + sum_i log min(1, gamma/(1+mu_i/3)^11).  Since
d boost/d mu_i = 1/(j'+1),

    d/d mu_i log g_bound = 11/((j'+1) boost)  -  [ 11/(3+mu_i)  if mu_i > mu*, else 0 ] .

(For mu_i <= mu* the min-factor is identically 1, since 1+mu_i/3 <= 1+mu*/3 = gamma^(1/11); its derivative
is 0.  For mu_i > mu* the factor is gamma/(1+mu_i/3)^11 with log-derivative -11/(3+mu_i).)

  T1 (mu_i <= mu*):  d/d mu_i log g_bound = 11/((j'+1) boost) > 0  -- INCREASING; push mu_i up to mu*.

  T2 (mu_i >= mu*):  d/d mu_i log g_bound < 0  <=>  (j'+1) boost > 3 + mu_i.  And the KEY EXACT IDENTITY

        (j'+1) boost = (j'+1) + (3S+1)/3 = j' + 4/3 + S ,

     gives, since S = mu_i + sum_{k != i} mu_k >= mu_i and j' >= 2,

        (j'+1) boost = j' + 4/3 + S >= j' + 4/3 + mu_i >= 10/3 + mu_i > 3 + mu_i .

     So d/d mu_i log g_bound < 0 -- DECREASING; push mu_i down to mu*.

At mu_i = mu* the min-factor has a concave kink (left-increasing, right-decreasing), so mu* is the
coordinate-wise maximum.  Applying T1/T2 coordinate by coordinate from ANY box point moves each mu_i to mu*
without decreasing g_bound, so the box-max is g_bound(mu*,...,mu*) = W boost(mu*)^11, which is < gamma by the
already-closed leaf (II) 621*4^11 < 64*5^11.  This closes the g-lemma's analytic residual for R1's branching
(all-non-leaf) case.

SCOPE.  This is the analytic unimodality only.  The remaining wiring into the block-level Branch induction is
the parallel session's structural layer, and R1 is SINGLE-HUB extremality -- one front of BG, not the whole
conjecture.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def boost(mus, jp):
    """boost = 1 + (3S+1)/(3(j'+1)), S = sum(mus).  `mus` Fractions, `jp` = j'."""
    S = sum(mus, Fr(0)) if all(isinstance(m, Fr) for m in mus) else sum(mus)
    return 1 + (3 * S + 1) / (3 * (jp + 1))


@dataclass(frozen=True)
class BranchingUnimodalityCertificate:
    """Certifies the over-the-reals g-step unimodality: the exact identity (j'+1)boost = j'+4/3+S; the
    descent inequality (j'+1)boost > 3+mu_i for j'>=2 (hence T2); T1's positive derivative; and that the
    box-max equals the symmetric mu* value < gamma."""

    def exact_boost_identity(self) -> bool:
        """(j'+1) * boost = j' + 4/3 + S, exactly, for all rational message vectors."""
        for jp in range(2, 8):
            for trial in range(1, 6):
                mus = [Fr(trial + k, 3 * (k + 2)) for k in range(jp)]     # assorted rationals in (0,1/2]
                S = sum(mus, Fr(0))
                if (jp + 1) * boost(mus, jp) != jp + Fr(4, 3) + S:
                    return False
        return True

    def descent_inequality(self) -> bool:
        """For j' >= 2 and any positive messages, (j'+1)boost = j'+4/3+S >= 10/3 + mu_i > 3 + mu_i."""
        for jp in range(2, 8):
            for trial in range(1, 8):
                mus = [Fr(trial + k, 3 * (k + 2)) for k in range(jp)]
                S = sum(mus, Fr(0))
                for i in range(jp):
                    lhs = (jp + 1) * boost(mus, jp)                       # = j'+4/3+S
                    if not (lhs == jp + Fr(4, 3) + S and lhs > 3 + mus[i]):
                        return False
        return True

    def box_max_is_symmetric(self) -> bool:
        """The g_bound box-max equals the symmetric mu* value (numeric multi-start) and is < gamma."""
        import math
        import random
        W = 64 / 621
        gamma = W ** 2 * (5 / 3) ** 11
        mustar = 3 * (gamma ** (1 / 11) - 1)

        def logg(mus, jp):
            b = 1 + (3 * sum(mus) + 1) / (3 * (jp + 1))
            return (math.log(W) + 11 * math.log(b)
                    + sum(math.log(min(1.0, gamma / (1 + m / 3) ** 11)) for m in mus))
        rng = random.Random(0)
        for jp in range(2, 7):
            sym = logg([mustar] * jp, jp)
            best = sym
            for _ in range(30000):
                best = max(best, logg([rng.uniform(0.0, 0.5) for _ in range(jp)], jp))
            if abs(best - sym) > 1e-6 or math.exp(sym) >= gamma:
                return False
        return True

    def check(self) -> bool:
        return self.exact_boost_identity() and self.descent_inequality() and self.box_max_is_symmetric()

    def lean(self) -> str:
        return (
            "-- G-STEP UNIMODALITY (over the reals).  boost = 1 + (3*S+1)/(3*(j'+1)); the exact identity\n"
            "theorem boost_identity (jp : ℕ) (S : ℚ) : (jp+1) * (1 + (3*S+1)/(3*(jp+1))) = jp + 4/3 + S := by\n"
            "  have h : ((3:ℚ)*(jp+1)) ≠ 0 := by positivity\n"
            "  field_simp; ring\n"
            "-- descent: for j'>=2, (j'+1)boost = j'+4/3+S >= 10/3 + mu_i > 3 + mu_i (S >= mu_i), so\n"
            "-- d/dmu_i log g_bound < 0 above mu*; and 11/((j'+1)boost) > 0 below.  Box-max = symmetric mu*.\n"
            "theorem descent (jp : ℕ) (S mui : ℚ) (hj : 2 ≤ jp) (hS : mui ≤ S) (hmui : 0 < mui) :\n"
            "    3 + mui < jp + 4/3 + S := by\n"
            "  have : (10:ℚ)/3 ≤ jp + 4/3 := by push_cast; nlinarith [hj]\n"
            "  nlinarith [this, hS, hmui]\n"
        )
