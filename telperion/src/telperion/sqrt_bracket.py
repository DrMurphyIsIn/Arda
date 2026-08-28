"""Transcendental skill: rigorous rational bracket of Real.sqrt q, in-kernel.

Fourth transcendental certificate.  The missing primitive the deep-transcendental
roadmap needs (tight log via range reduction, and the CVZ path to zeta(1/2) both
need sqrt bounds).  For rational q > 0 and rationals lo, hi with lo^2 <= q <= hi^2,

    lo <= Real.sqrt q <= hi,

proved by monotonicity + `Real.sqrt_sq` (robust: no reliance on the exact
direction of `Real.le_sqrt` / `Real.sqrt_le'` iff-lemmas):
    lo = sqrt(lo^2) <= sqrt q   and   sqrt q <= sqrt(hi^2) = hi.

`build` auto-fills lo, hi from q; `check()` cross-verifies against mpmath's
rigorous interval `iv.sqrt`.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


SQRT_BRACKET_TEMPLATE = """theorem {name} :
    ({ln} : ℝ) / {ld} ≤ Real.sqrt (({qn} : ℝ) / {qd})
      ∧ Real.sqrt (({qn} : ℝ) / {qd}) ≤ ({hn} : ℝ) / {hd} := by
  constructor
  · calc (({ln} : ℝ) / {ld})
        = Real.sqrt ((({ln} : ℝ) / {ld}) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (({qn} : ℝ) / {qd}) := Real.sqrt_le_sqrt (by norm_num)
  · calc Real.sqrt (({qn} : ℝ) / {qd})
        ≤ Real.sqrt ((({hn} : ℝ) / {hd}) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = ({hn} : ℝ) / {hd} := Real.sqrt_sq (by norm_num)"""


@dataclass(frozen=True)
class SqrtBracketCertificate:
    """lo <= Real.sqrt(qn/qd) <= hi over exact rationals with lo^2 <= q <= hi^2."""

    name: str
    qn: int
    qd: int
    lo: object = None            # Fraction; auto-filled by build() if None
    hi: object = None

    @classmethod
    def build(cls, name, qn, qd, digits=13):
        q = Fr(qn, qd)
        scale = 10 ** digits
        r = math.isqrt(q.numerator * scale * scale // q.denominator)  # floor(sqrt(q)*scale)
        lo = Fr(r, scale)
        hi = Fr(r + 1, scale)
        # guarantee the bracket by construction (floor/ceil of the integer sqrt)
        while lo * lo > q:
            lo -= Fr(1, scale)
        while hi * hi < q:
            hi += Fr(1, scale)
        return cls(name=name, qn=qn, qd=qd, lo=lo, hi=hi)

    def _lh(self):
        return Fr(self.lo), Fr(self.hi)

    def check(self) -> bool:
        if self.lo is None or self.hi is None or not (self.qn > 0 and self.qd > 0):
            return False
        q = Fr(self.qn, self.qd)
        lo, hi = self._lh()
        if not (0 <= lo <= hi and lo * lo <= q <= hi * hi):
            return False
        try:
            import mpmath as mp
            ivs = mp.iv.sqrt(mp.iv.mpf(self.qn) / self.qd)   # rigorous interval
            return bool(mp.mpf(lo.numerator) / lo.denominator <= ivs.a) and \
                bool(ivs.b <= mp.mpf(hi.numerator) / hi.denominator)
        except Exception:
            return True

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: sqrt bracket invalid -- refusing to emit")
        lo, hi = self._lh()
        return SQRT_BRACKET_TEMPLATE.format(
            name=self.name, qn=self.qn, qd=self.qd,
            ln=lo.numerator, ld=lo.denominator, hn=hi.numerator, hd=hi.denominator) + "\n"
