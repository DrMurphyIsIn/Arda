"""Reusable rigorous rational bracket of a transcendental exp(-theta) -- the
generalization of the bespoke `examples/exp_bracket/` far-constant into a
certificate any exp-bracket site can instantiate (H2-Bridge layer: the exp(-theta)
constants in far-discharge / BridgeStep / rate bounds).

This is the DERIVE side of the enclosure story (distinct from
`TuranEnclosureCertificate`, which CONSUMES a given enclosure to prove a
product-vs-square inequality -- neither generalizes the other; see
`examples/turan_xi/BG_APPLICABILITY.md`).  The hard content here is bounding a
transcendental by a truncated Taylor series:

    upper:  exp(-theta) = 1/exp(theta) <= 1/Taylor_N(theta) <= hi
            (Taylor_N(theta) <= exp(theta) via Mathlib `Real.sum_le_exp_of_nonneg`;
             the rational heart `tfloor <= Taylor_N(theta)` and `1/tfloor <= hi`
             are exact-rational, `norm_num`-checked)
    lower:  1 - theta <= exp(-theta)         (convexity, `Real.add_one_le_exp`)

`tfloor` (a clean rational <= Taylor_N(theta)) and `hi` (a rational >= 1/tfloor)
are supplied explicitly so the emitted numerals are deterministic; `suggest`
computes sane defaults for a new theta.  The generator is untrusted -- the Lean
kernel is the arbiter; `.check()` catches errors in exact rationals first.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


def taylor_exp(x: Fr, nterms: int) -> Fr:
    """Sum_{k=0}^{nterms-1} x^k / k!  in exact rationals (= Taylor_N(x) with N terms)."""
    s, term = Fr(0), Fr(1)
    for k in range(nterms):
        s += term
        term = term * x / (k + 1)
    return s


def suggest(theta: Fr, nterms: int, digits: int = 5) -> tuple[Fr, Fr]:
    """Convenience: a valid (tfloor, hi) pair for exp(-theta) at `digits` decimals.
    tfloor = floor(Taylor_N * 10^d)/10^d (<= Taylor_N <= exp(theta));
    hi      = ceil((1/tfloor) * 10^d)/10^d (>= 1/tfloor >= exp(-theta))."""
    scale = 10 ** digits
    T = taylor_exp(theta, nterms)
    tfloor = Fr(math.floor(T * scale), scale)          # <= T
    hi = Fr(math.ceil((1 / tfloor) * scale), scale)    # >= 1/tfloor
    return tfloor, hi


# Verbatim from examples/exp_bracket/ (the proven, compile-gated shape).
EXP_BRACKET_TEMPLATE = """theorem {le_name} :
    Real.exp (-({tn} / {td} : ℝ)) ≤ {hn} / {hd} := by
  rw [Real.exp_neg, ← one_div]
  have hlow : ({fn} / {fd} : ℝ) ≤ Real.exp ({tn} / {td}) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) {n})
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < {fn} / {fd} := by norm_num
  calc 1 / Real.exp ({tn} / {td})
      ≤ 1 / ({fn} / {fd} : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ {hn} / {hd} := by norm_num

theorem {ge_name} :
    (1 - {tn} / {td} : ℝ) ≤ Real.exp (-({tn} / {td})) := by
  have h := Real.add_one_le_exp (-({tn} / {td} : ℝ))
  linarith"""


@dataclass(frozen=True)
class ExpBracketCertificate:
    """Rigorous rational bracket  1 - theta <= exp(-theta) <= hi,  emitted as two
    Mathlib-backed theorems.  `tfloor` is a clean rational <= Taylor_N(theta) and
    `hi` a rational >= 1/tfloor; use `ExpBracketCertificate.build(theta, nterms)`
    to auto-fill them via `suggest`."""

    theta: object            # Fraction-coercible
    nterms: int
    tfloor: object           # Fraction-coercible, <= Taylor_N(theta)
    hi: object               # Fraction-coercible, >= 1/tfloor
    le_name: str = "exp_neg_theta_le"
    ge_name: str = "exp_neg_theta_ge"

    @classmethod
    def build(cls, theta, nterms, digits=5, **kw):
        tfloor, hi = suggest(Fr(theta), nterms, digits)
        return cls(theta=Fr(theta), nterms=nterms, tfloor=tfloor, hi=hi, **kw)

    def _f(self):
        return Fr(self.theta), Fr(self.tfloor), Fr(self.hi)

    def lo(self) -> Fr:
        return 1 - Fr(self.theta)

    def check(self) -> bool:
        """Exact-rational self-check of the two rational inequalities the emitted
        Lean relies on, plus enclosure sanity.  Blocks emission on failure."""
        theta, tfloor, hi = self._f()
        if not (theta > 0 and tfloor > 0 and self.nterms >= 1):
            return False
        T = taylor_exp(theta, self.nterms)
        return (tfloor <= T            # tfloor <= Taylor_N(theta) <= exp(theta)
                and 1 / tfloor <= hi   # so exp(-theta) = 1/exp(theta) <= 1/tfloor <= hi
                and self.lo() <= hi)   # 1 - theta <= exp(-theta) <= hi (enclosure sane)

    def lean(self) -> str:
        if not self.check():
            raise ValueError(
                f"ExpBracket(theta={self.theta}): rational bracket invalid "
                f"(check() False) -- refusing to emit"
            )
        theta, tfloor, hi = self._f()
        return EXP_BRACKET_TEMPLATE.format(
            le_name=self.le_name, ge_name=self.ge_name, n=self.nterms,
            tn=theta.numerator, td=theta.denominator,
            hn=hi.numerator, hd=hi.denominator,
            fn=tfloor.numerator, fd=tfloor.denominator,
        )
