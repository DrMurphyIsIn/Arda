"""BG asymptotic upper bound — the composed reduction skeleton (2026-08-31).

This module assembles the whole branch-induction upper-bound argument into ONE explicit, machine-checkable
reduction: the goal `F(T) = (1/|T|) log pi(T) <= F* = log(621/64)/11` (asymptotically) is discharged by a
chain of steps, each tagged GATED (a kernel-gated certificate that `.check()`s here), BASE (a finite exhaustive
verification), BOUNDARY (an O(1) boundary constant, documented), LEMMA (proven elsewhere), or HYPOTHESIS (the
single open analytic input).  It is the honest "one lemma away" ledger in code -- `conjecture1_proved = False`.

The chain (see `docs/BG_UPPER_BOUND_REDUCTION_20260831.md`):

  [0] boundary        1 <= pi(T)/branch_total(T,r) <= 4/3, so (1/n)log pi <= F* + O(1/n) -> F*  GIVEN ell(B)<=0.
  [1] branch ceiling  ell(B) <= 0 for all rooted branches B, by induction on |B|:
        [1a] base      |B| <= 11 exhaustively verified.
        [1b] step      ell(hub of children c_i) <= ell(B(k)) [mixed<=broom] <= 0 [broom optimum].
  [2] mixed <= B(k)   the hub bound, split by root degree k:
        [2a] k >= 16   slack bound slack_g(k) <= F*                         GATED: TieSlackCertificate.
        [2b] k <= 15   concavity tangent + per-child KKT V(c_i) <= V(cherry):
              - brooms B(2..8)          GATED: MixedHubKKTCertificate.
              - d_c >= 7                GATED: HighDegreeTailCertificate.
              - d_c <= 6 non-broom      HYPOTHESIS (b): ell(c) < ell(cherry) - lambda(k)/(6(k+1)).
  [3] broom optimum   ell(B(k)) <= 0, = 0 iff k=5 (the 23-adic tie)        GATED: BroomOptimumCertificate.

The ONLY open analytic input is HYPOTHESIS (b) (the small-degree non-broom refined ceiling; verified over all
branches <= size 14, generalized brooms to size 66, star-of-brooms rooted at low-degree vertices to size 101 --
its failure mode explicitly refuted, see `branch_ell_by_vertex` / the deficit view).  Everything else is a gated
certificate, a finite base check, or the O(1) boundary constant.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional

from .spider_broom import BroomOptimumCertificate
from .tie_regime import HighDegreeTailCertificate, MixedHubKKTCertificate, TieSlackCertificate

GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS = "GATED", "BASE", "BOUNDARY", "LEMMA", "HYPOTHESIS"


@dataclass(frozen=True)
class ReductionStep:
    """One step of the upper-bound reduction.  `kind` in {GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS}; `cert` is a
    callable returning a certificate with `.check()` for GATED steps (else `None`)."""

    tag: str
    statement: str
    kind: str
    cert: Optional[Callable[[], object]] = None

    def verify(self) -> Optional[bool]:
        """`True/False` for GATED steps (does the certificate check?); `None` for non-gated steps."""
        if self.kind != GATED or self.cert is None:
            return None
        return bool(self.cert().check())


@dataclass(frozen=True)
class UpperBoundReduction:
    """The composed BG asymptotic-upper-bound reduction.  `.steps` is the full chain; `.verify_gated()` checks
    every GATED certificate; `.open_hypotheses()` returns the open analytic inputs (exactly one: the small-degree
    refined ceiling (b)).  `conjecture_proved` is `False` iff any step is a HYPOTHESIS -- and it is."""

    steps: tuple = field(default_factory=tuple)

    @staticmethod
    def build() -> "UpperBoundReduction":
        return UpperBoundReduction(steps=(
            ReductionStep("0", "1 <= pi(T)/branch_total(T,r) <= 4/3  =>  (1/n)log pi <= F* + O(1/n)  [given ell<=0]",
                          BOUNDARY),
            ReductionStep("1a", "branch ceiling base: ell(B) <= 0 for |B| <= 11 (exhaustive)", BASE),
            ReductionStep("1b", "branch ceiling step: ell(hub of c_i) <= ell(B(k)) <= 0 (induction on |B|)", LEMMA),
            ReductionStep("2a", "mixed <= B(k), k >= 16: slack_g(k) <= F*", GATED, TieSlackCertificate),
            ReductionStep("2b-brooms", "mixed <= B(k), k <= 15: per-child V(B(j)) < V(cherry), B(2..8)",
                          GATED, MixedHubKKTCertificate),
            ReductionStep("2b-hi", "envelope tail, d_c >= 7: V(c) < V(cherry) via ceiling ell<=0",
                          GATED, HighDegreeTailCertificate),
            ReductionStep("2b-lo", "envelope tail, d_c <= 6 non-broom: ell(c) < ell(cherry) + (d_c-3)/(d_c(4k+3))",
                          HYPOTHESIS),
            ReductionStep("3", "broom optimum: ell(B(k)) <= 0, = 0 iff k=5 (23-adic tie)",
                          GATED, BroomOptimumCertificate),
        ))

    def verify_gated(self) -> dict:
        """`{tag: bool}` for every GATED step -- all must be `True` for the gated skeleton to hold."""
        return {s.tag: s.verify() for s in self.steps if s.kind == GATED}

    def gated_ok(self) -> bool:
        return all(self.verify_gated().values())

    def open_hypotheses(self) -> list:
        """The open analytic inputs (HYPOTHESIS steps).  Exactly one: the small-degree refined ceiling (b)."""
        return [s for s in self.steps if s.kind == HYPOTHESIS]

    @property
    def conjecture_proved(self) -> bool:
        """`False` while any HYPOTHESIS remains open (it does -- (b))."""
        return len(self.open_hypotheses()) == 0

    def status(self) -> str:
        from collections import Counter
        c = Counter(s.kind for s in self.steps)
        gated = self.verify_gated()
        return (f"gated={sum(gated.values())}/{len(gated)} pass; "
                f"steps: " + ", ".join(f"{k}={c[k]}" for k in (GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS) if c[k])
                + f"; open hypotheses={len(self.open_hypotheses())}; conjecture_proved={self.conjecture_proved}")


conjecture1_proved = False
