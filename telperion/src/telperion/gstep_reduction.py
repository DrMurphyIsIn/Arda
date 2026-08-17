"""The g-step multi-variable optimization, reduced toward Lean-tight (the last residual of single-hub R1).

R1's single-hub arm-extremality rests on the g-lemma `g(C) <= gamma := W^2 (5/3)^11` for every non-leaf block
`C`.  Its strong-induction step, in the all-non-leaf (branching, root-degree `j' >= 2`) case, is a genuine
MULTI-VARIABLE optimization over the child messages `mu_1, ..., mu_{j'} in (0, 1/2]`:

    g_bound(mu_1..mu_{j'}) = W * [1 + (3*sum mu_i + 1)/(3j'+3)]^11 * prod_i min(1, gamma/(1+mu_i/3)^11)  <  gamma.

A crude separable bound blows past gamma (~8.9), so the two-regime product `min(1, gamma/(1+mu_i/3)^11)` is
load-bearing (collective cancellation).  This module records the REDUCTION of that optimization to a finite
rational certificate, validated in exact/tight arithmetic.

REDUCTION (matches the intended Schur -> symmetric-argmax -> finite-certificate path):

  1. SYMMETRIC ARGMAX.  The global max of `g_bound` over the box is at the symmetric point `mu_i = mu`
     (verified: the per-`j'` global maximizer is `(mu*, ..., mu*)`; the earlier fixed-sum "boundary beats
     center" is a heavy-regime artifact that the sum-optimization overrides).  Reduces to a single-variable
     `f_{j'}(mu) = W*[1+(3j'mu+1)/(3j'+3)]^11 * min(1, gamma/(1+mu/3)^11)^{j'}`.

  2. PER-j' MAX AT THE CROSSOVER mu*.  `f_{j'}` increases for `mu <= mu*` (product = 1, boost up) and
     decreases for `mu > mu*` (checked via `(j'+1)*boost > 3+mu` for `j' >= 2`), so the max is at `mu = mu*`
     where `min(...) = 1` exactly.  There `f_{j'}(mu*) = W * boost(mu*)^11`.

  3. TWO RATIONAL LEAVES.  Because `mu* < 1/3`, the symmetric-max boost is `< 4/3`:
        boost(mu*) = 1 + (3j'mu* + 1)/(3j'+3) < 1 + (j'+1)/(3j'+3) = 4/3      (uses 3*mu* < 1),
     hence `f_{j'>=2}(mu*) = W*boost(mu*)^11 < W*(4/3)^11 < gamma`.  The two facts are exact rationals:
        (I)  mu* < 1/3        <=>  gamma < (10/9)^11   <=>  64^2*5^11*9^11 < 621^2*3^11*10^11,
        (II) W*(4/3)^11 < gamma                        <=>  621*4^11 < 64*5^11.

  (j' = 1 is NOT part of this branching step -- a root-degree-1 block is chain-like and is bounded by the
  B(L,j') family of `arm_lean_certificates.py`; only j' >= 2 branching goes through the min-product optimization.)

STATUS.  Steps 1-2 are the analytic glue (a majorization / Schur-concavity reduction plus a per-`j'`
monotonicity), verified numerically here and stated as the residual; step 3's two rational leaves are pinned
exactly and emitted to Lean (`gamma_lt_ten_ninths_11`, `W_four_thirds_11_lt_gamma` in `G1.ArmExtremality`).
So the g-step's ARITHMETIC core is Lean-tight; the remaining Lean work is formalizing the symmetric-argmax
majorization + monotonicity and wiring both families into the block-level g-lemma (the Branch induction).
`conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

W = Fr(64, 621)
GAMMA = W ** 2 * Fr(5, 3) ** 11
_GF = float(GAMMA)
MU_STAR = 3.0 * (_GF ** (1.0 / 11.0) - 1.0)          # crossover: (1+mu*/3)^11 = gamma


def _m(mu: float) -> float:
    """The two-regime per-child factor `min(1, gamma/(1+mu/3)^11)`."""
    return min(1.0, _GF / (1.0 + mu / 3.0) ** 11)


def g_bound(mus) -> float:
    """`W * [1+(3*sum+1)/(3j'+3)]^11 * prod min(1, gamma/(1+mu_i/3)^11)`  (the relaxed g-step upper bound)."""
    jp = len(mus)
    S = sum(mus)
    boost = (1.0 + (3.0 * S + 1.0) / (3.0 * jp + 3.0)) ** 11
    prod = 1.0
    for mu in mus:
        prod *= _m(mu)
    return float(W) * boost * prod


def f_sym(jp: int, mu: float) -> float:
    """The symmetric single-variable reduction `f_{j'}(mu)`."""
    return g_bound([mu] * jp)


def leaf_mu_star_lt_third() -> bool:
    """(I) `mu* < 1/3`, as the exact rational `gamma < (10/9)^11`  (`64^2*5^11*9^11 < 621^2*3^11*10^11`)."""
    return GAMMA < Fr(10, 9) ** 11


def leaf_W_four_thirds_lt_gamma() -> bool:
    """(II) `W*(4/3)^11 < gamma`, as the exact rational `621*4^11 < 64*5^11`."""
    return W * Fr(4, 3) ** 11 < GAMMA


@dataclass(frozen=True)
class GStepReductionCertificate:
    """The branching (j' >= 2) g-step optimization, reduced to a finite rational certificate.  `check()`
    validates: the symmetric-argmax reduction (global max is symmetric), the per-j' crossover max (f up to
    mu*, down after), the two exact rational leaves (mu* < 1/3 and W(4/3)^11 < gamma), and that they bound the
    optimization below gamma (binding j'=2 value ~2.107 < W(4/3)^11 < gamma).  The symmetric-argmax
    majorization + monotonicity are validated numerically (the analytic residual); the two leaves are exact
    and Lean-emitted.  NOT the full g-lemma, NOT BG.  conjecture1_proved = False."""

    max_jp: int = 40
    grid: int = 24

    def symmetric_is_argmax(self) -> bool:
        """For each `j'` in `[2, 4]`, the global max of `g_bound` over a box grid equals the symmetric max (no
        asymmetric config beats the best symmetric one) -- exhaustive on the coarse grid, plus a finer random
        sweep for `j'` up to 6."""
        import itertools
        import random
        for jp in range(2, 5):
            g = [i / self.grid * 0.5 for i in range(1, self.grid + 1)]
            sym_best = max(f_sym(jp, mu) for mu in g)
            for combo in itertools.combinations_with_replacement(g, jp):
                if g_bound(list(combo)) > sym_best + 1e-9:
                    return False
        rng = random.Random(12345)
        for jp in range(2, 7):
            sym_best = max(f_sym(jp, i / 500 * 0.5) for i in range(1, 501))
            for _ in range(30000):
                combo = [rng.uniform(1e-4, 0.5) for _ in range(jp)]
                if g_bound(combo) > sym_best + 1e-9:
                    return False
        return True

    def per_jp_max_at_crossover(self) -> bool:
        """`f_{j'}` rises to `mu*` then falls (for `j' >= 2`): the argmax over a fine grid sits at `mu*`, and
        the descent condition `(j'+1)*boost > 3+mu` holds for every `mu > mu*`."""
        for jp in range(2, self.max_jp + 1):
            g = [i / 2000 * 0.5 for i in range(1, 2001)]
            arg = max(g, key=lambda mu: f_sym(jp, mu))
            if abs(arg - MU_STAR) > 0.01:
                return False
            for mi in range(1, 2001):
                mu = mi / 2000 * 0.5
                if mu > MU_STAR:
                    boost = 1.0 + (3.0 * jp * mu + 1.0) / (3.0 * jp + 3.0)
                    if not (jp + 1) * boost > 3.0 + mu:
                        return False
        return True

    def boost_below_four_thirds(self) -> bool:
        """At the symmetric crossover, `boost(mu*) < 4/3` for every `j' >= 2` (from `3*mu* < 1`)."""
        if not MU_STAR < 1.0 / 3.0:
            return False
        for jp in range(2, self.max_jp + 1):
            boost = 1.0 + (3.0 * jp * MU_STAR + 1.0) / (3.0 * jp + 3.0)
            if not boost < 4.0 / 3.0:
                return False
        return True

    def rational_leaves(self) -> bool:
        """The two exact rational leaves, and that they chain to `f_{j'>=2}(mu*) < gamma`."""
        if not (leaf_mu_star_lt_third() and leaf_W_four_thirds_lt_gamma()):
            return False
        # cross-multiplied integer forms
        if not (64 ** 2 * 5 ** 11 * 9 ** 11 < 621 ** 2 * 3 ** 11 * 10 ** 11):
            return False
        if not (621 * 4 ** 11 < 64 * 5 ** 11):
            return False
        # W*(4/3)^11 < gamma bounds the branching optimization (j'=2 binding, ~2.107)
        return float(W * Fr(4, 3) ** 11) < _GF and f_sym(2, MU_STAR) < float(W * Fr(4, 3) ** 11)

    def finding(self) -> str:
        return (
            "The branching (j'>=2) g-step optimization max < gamma is REDUCED to a finite rational "
            "certificate. Symmetric-argmax (global max is symmetric, verified) -> per-j' max at the crossover "
            "mu* (f up to mu*, down after via (j'+1)boost>3+mu) -> at mu* the boost < 4/3 (since 3 mu* < 1), so "
            "f_{j'>=2}(mu*) = W*boost^11 < W*(4/3)^11 < gamma. Two EXACT rational leaves: (I) mu*<1/3 <=> "
            "gamma<(10/9)^11 <=> 64^2*5^11*9^11 < 621^2*3^11*10^11; (II) W(4/3)^11<gamma <=> 621*4^11 < 64*5^11. "
            "(j'=1 is chain-absorbed by the B(L,j') family, not this step.) The two leaves are Lean-emitted "
            "(G1.ArmExtremality); the symmetric-argmax majorization + monotonicity + Branch-induction wiring "
            "are the remaining analytic glue for full Lean-lock of the g-lemma. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Validates the reduction (symmetric-argmax, crossover max, boost<4/3) and the two exact rational
        leaves -- the finite-certificate core of the branching g-step.  The majorization/monotonicity glue is
        the named residual.  NOT the full g-lemma."""
        return (
            self.symmetric_is_argmax()
            and self.per_jp_max_at_crossover()
            and self.boost_below_four_thirds()
            and self.rational_leaves()
        )
