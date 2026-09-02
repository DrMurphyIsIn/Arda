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
              - d_c <= 6 non-broom      the M_d frontier bound, now split into:
                  * near-broom finite   GATED: MdGeometricTailCertificate (peak arithmetic < threshold).
                  * near-broom unimodal GATED: NearBroomUnimodalityCertificate (peaks at m*, strictly decreases).
                  * extremality         HYPOTHESIS (b): the near-broom is the argmax non-broom degree-d branch.
  [3] broom optimum   ell(B(k)) <= 0, = 0 iff k=5 (the 23-adic tie)        GATED: BroomOptimumCertificate.

The ONLY open analytic input is HYPOTHESIS (b), now SHARPENED (2026-09-01) to a single COMBINATORIAL statement:
the near-broom "(d-2) cherries + B(m)" is the argmax over ALL non-broom root-degree-d branches.  The earlier
"even-step contraction rho<=5/12" framing was WRONG: the near-broom family does not climb toward threshold via a
geometric tail -- it PEAKS at m* = max(1, d-3) (sizes 4,6,10,14,16 for d=2..6; margins +0.017..+0.040) and then
STRICTLY DECREASES (linearly, away from threshold).  This unimodality is now UNCONDITIONALLY gated
(NearBroomUnimodalityCertificate): Delta(d,m) < 0 <=> BIG(d,m)^11 < (621/64)^2 (pure rational, F* cleared), with a
degree-1 positive-coefficient Handelman certificate for the monotone tail (d=3..6) and BIG(2,m) < 3/2 (<=>
4m+3>0) for d=2.  So the frontier reduces to the extremality alone -- adversarially checked (two-broom /
deep-nested competitors sit >= +0.017 below the near-broom peak), a single-child combinatorial lemma, NOT a rate.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional

from .spider_broom import BroomOptimumCertificate
from .tie_regime import (
    BroomVsCherryCertificate, ExtremalityPriceMapCertificate, HighDegreeTailCertificate,
    LeafExchangeCertificate, MdGeometricTailCertificate, MixedHubKKTCertificate,
    NearBroomUnimodalityCertificate, TieSlackCertificate,
)

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
            ReductionStep("2b-lo-fin", "M_d finite arithmetic: near-broom peaks d=2..5 + d=6 boundary < threshold",
                          GATED, MdGeometricTailCertificate),
            ReductionStep("2b-lo-unimodal", "near-broom family (d-2)cherries+B(m) peaks at m*=max(1,d-3) & strictly "
                          "decreases after (BIG^11 < (621/64)^2 + Handelman monotone tail) -- UNCONDITIONAL, no rho",
                          GATED, NearBroomUnimodalityCertificate),
            ReductionStep("2b-lo-pricemap", "extremality #1 price-flow: the single-child lemma's joint size-induction "
                          "keeps prices in the invariant interval I=[456/3703,3/7] (concavity-tangent map)",
                          GATED, ExtremalityPriceMapCertificate),
            ReductionStep("2b-lo-tangent", "extremality #2 tangent step: V_mu(hub) <= V_mu(B(d-1)) from concavity of "
                          "L(s)=log(1+s/d)-F* (Real.log concave; the all-cherry point is the tangent, gap 0)", LEMMA),
            ReductionStep("2b-lo-broomcherry", "extremality #4: broom child never beats cherry on I, "
                          "V_mu(B(k)) <= V_mu(cherry) all k (finite head + broom-optimum tail)",
                          GATED, BroomVsCherryCertificate),
            ReductionStep("2b-lo-leafexchange", "extremality #5: leaf->cherry raises ell (d>=3), (5/6)^11 > "
                          "(2/3)^11(621/64) -- bare leaves never in the extremum",
                          GATED, LeafExchangeCertificate),
            ReductionStep("2b-lo-extremality", "extremality #3+assembly: the SCL joint size-induction composing the "
                          "gated pieces #1,#2,#4,#5,#6 => V_mu(c)<=V_mu(cherry) => near-broom argmax (structural "
                          "well-founded recursion on |c|; all analytic/rational leaves now gated)",
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
