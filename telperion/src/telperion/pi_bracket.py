"""Transcendental skill: rigorous rational bracket of Real.pi, in-kernel.

Third transcendental certificate (after exp_bracket, log_bound).  Unlike those it
needs no derivation -- Mathlib ships proven decimal bounds on pi.  This wraps the
6-digit pair into

    3.141592  <  Real.pi  <  3.141593

emitted with the SAME decimal literals Mathlib uses, so the proof is literally
`<Real.pi_gt_3141592, Real.pi_lt_3141593>` (no norm_num bridging, no
decimal-vs-fraction defeq risk).  pi is load-bearing in xi (the pi^{-s/2} factor)
and the archimedean Li terms.

`check()` cross-checks the bracket against mpmath's RIGOROUS interval iv.pi.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

# Mathlib's proven 6-digit bounds, verbatim decimal literals + lemma names.
_LO = "3.141592"
_HI = "3.141593"
_LEM_LO = "Real.pi_gt_3141592"
_LEM_HI = "Real.pi_lt_3141593"


@dataclass(frozen=True)
class PiBracketCertificate:
    """Rigorous bracket  3.141592 < Real.pi < 3.141593, backed verbatim by
    Mathlib's `Real.pi_gt_3141592` / `Real.pi_lt_3141593`."""

    name: str

    def bracket(self):
        return Fr(3141592, 1000000), Fr(3141593, 1000000)

    def check(self) -> bool:
        lo, hi = self.bracket()
        try:
            import mpmath as mp
            ivpi = mp.iv.pi                        # rigorous interval enclosure of pi
            return (lo < hi
                    and bool(mp.mpf(lo.numerator) / lo.denominator < ivpi.a)
                    and bool(ivpi.b < mp.mpf(hi.numerator) / hi.denominator))
        except Exception:
            import math
            return lo < hi and float(lo) < math.pi < float(hi)

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: pi bracket not verified -- refusing to emit")
        return (
            f"theorem {self.name} :\n"
            f"    ({_LO} : ℝ) < Real.pi ∧ Real.pi < ({_HI} : ℝ) :=\n"
            f"  ⟨{_LEM_LO}, {_LEM_HI}⟩\n"
        )
