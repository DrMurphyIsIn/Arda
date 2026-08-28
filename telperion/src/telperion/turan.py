"""Turan / Laguerre inequalities for the Riemann xi function -- a Laguerre-Polya
lens on RH, certified over IMPORTED rational enclosures.

Background.  The Riemann Hypothesis is equivalent to xi lying in the
Laguerre-Polya class (the closure of real polynomials with only real zeros).
A NECESSARY consequence -- proved UNCONDITIONALLY for xi by Csordas, Norfolk
and Varga (1986) -- is that the even Taylor coefficients

    a_k := [z^{2k}] xi(1/2 + z)      (all a_k > 0)

satisfy the Turan (Laguerre) inequalities  a_k^2 >= a_{k-1} a_{k+1}  for k >= 1.
(These are necessary, not sufficient: they hold whether or not RH is true.)

What Telperion can and cannot do here.  The a_k are transcendental; exact
rational arithmetic cannot access them, so this module does NOT prove anything
about the a_k themselves.  It certifies the finite ALGEBRAIC step: given
rational enclosures

    lo_k < a_k < hi_k         (IMPORTED -- their derivation is high-precision
                               numerics, the transcendental input, done outside
                               this dependency-light core),

the strict Turan inequality a_{k-1} a_{k+1} < a_k^2 follows for every real
triple in the enclosures whenever the worst-corner margin

    hi_{k-1} * hi_{k+1}  <  lo_k^2

holds -- a single exact rational inequality (`norm_num`), bridged to the
enclosure hypotheses by a fixed monotonicity lemma `turan_from_enclosure`
(`nlinarith`).  The Lean kernel is the sole trusted component; a defective
certificate manifests as a compile failure.

HONEST SCOPE.  This certifies Turan at the given FINITE indices, CONDITIONAL on
imported enclosures.  It is NOT progress toward RH:
  * the all-k result is CNV 1986, not this;
  * Turan is necessary, never sufficient for RH;
  * the enclosures are numeric imports, not interval-proven inside Lean.
See `examples/turan_xi/README.md` for provenance and the gap statement.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


# The one reusable, once-proved bridge: worst-corner monotonicity.  Given
# 0 <= lo1 <= a1, 0 <= a0 <= hi0, 0 <= a2 <= hi2 and hi0*hi2 < lo1^2, the Turan
# inequality a0*a2 < a1^2 holds.  Verbatim-stable nlinarith shape.
TURAN_BRIDGE_LEMMA = """/-- Worst-corner bridge: a strict rational margin `hi0*hi2 < lo1^2` on the
    enclosures forces the Turan inequality `a0*a2 < a1^2` for every real triple
    inside them.  (Monotonicity: `a0*a2 <= hi0*hi2 < lo1^2 <= a1^2`.) -/
theorem turan_from_enclosure {a0 a1 a2 lo1 hi0 hi2 : ℝ}
    (hlo1 : 0 ≤ lo1) (h1 : lo1 ≤ a1)
    (hp0 : 0 ≤ a0) (h0 : a0 ≤ hi0)
    (hp2 : 0 ≤ a2) (h2 : a2 ≤ hi2)
    (hm : hi0 * hi2 < lo1 ^ 2) :
    a0 * a2 < a1 ^ 2 := by
  have hprod : a0 * a2 ≤ hi0 * hi2 := mul_le_mul h0 h2 hp2 (le_trans hp0 h0)
  have hsq : lo1 ^ 2 ≤ a1 ^ 2 := by
    nlinarith [mul_le_mul h1 h1 hlo1 (le_trans hlo1 h1)]
  nlinarith [hprod, hsq, hm]"""


def _rat_lean(x: Fr) -> str:
    """Render an exact rational as a Lean real literal `(num : ℝ) / den`."""
    x = Fr(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    return f"(({x.numerator} : ℝ) / {x.denominator})"


@dataclass(frozen=True)
class TuranEnclosureCertificate:
    """Turan inequalities a_{k-1} a_{k+1} < a_k^2 for the interior indices of a
    run of rational enclosures of xi's even Taylor coefficients.

    Parameters
    ----------
    name : str
        Base Lean name; per-index theorems are `{name}_k{k}`.
    enclosures : sequence of (lo, hi)
        Index k = 0, 1, ... gives `lo_k < a_k < hi_k` as exact rationals
        (anything `Fraction` accepts: int, str "p/q", or Fraction).  Interior
        indices k = 1 .. len-2 are certified.
    """

    name: str
    enclosures: tuple

    # -- exact-rational core ------------------------------------------------
    def _enc(self) -> list[tuple[Fr, Fr]]:
        return [(Fr(lo), Fr(hi)) for (lo, hi) in self.enclosures]

    def certified_indices(self) -> list[int]:
        return list(range(1, len(self.enclosures) - 1))

    def margin(self, k: int) -> Fr:
        """lo_k^2 - hi_{k-1} * hi_{k+1}; positive == Turan certified at k."""
        e = self._enc()
        lo_k = e[k][0]
        hi_km, hi_kp = e[k - 1][1], e[k + 1][1]
        return lo_k * lo_k - hi_km * hi_kp

    def check(self) -> bool:
        """Exact-rational self-check: enclosures well-formed (0 < lo_k < hi_k)
        and every interior margin strictly positive.  A red check must block
        emission (the generator is untrusted; this catches errors pre-Lean)."""
        e = self._enc()
        if len(e) < 3:
            return False
        for lo, hi in e:
            if not (0 < lo < hi):
                return False
        return all(self.margin(k) > 0 for k in self.certified_indices())

    # -- Lean emission ------------------------------------------------------
    def lean(self) -> str:
        """The bridge lemma plus one per-index theorem.  Each per-index theorem
        imports `0 <= a_{k-1}`, `a_{k-1} <= hi_{k-1}`, `lo_k <= a_k`,
        `0 <= a_{k+1}`, `a_{k+1} <= hi_{k+1}` as hypotheses and concludes the
        strict Turan inequality, discharging the rational margin by `norm_num`.

        Refuses to emit a certificate that does not pass `check()`."""
        if not self.check():
            raise ValueError(
                f"{self.name}: enclosures do not certify Turan "
                f"(check() is False) -- refusing to emit"
            )
        e = self._enc()
        blocks = [TURAN_BRIDGE_LEMMA, ""]
        for k in self.certified_indices():
            lo_k = _rat_lean(e[k][0])
            hi_km = _rat_lean(e[k - 1][1])
            hi_kp = _rat_lean(e[k + 1][1])
            m = self.margin(k)
            blocks.append(
                f"-- k={k}:  a_{k-1} * a_{k+1} < a_{k}^2  "
                f"(margin lo_{k}^2 - hi_{k-1}*hi_{k+1} = {m} > 0)\n"
                f"theorem {self.name}_k{k} "
                f"{{a{k-1} a{k} a{k+1} : ℝ}}\n"
                f"    (hp{k-1} : 0 ≤ a{k-1}) (h{k-1} : a{k-1} ≤ {hi_km})\n"
                f"    (h{k} : {lo_k} ≤ a{k})\n"
                f"    (hp{k+1} : 0 ≤ a{k+1}) (h{k+1} : a{k+1} ≤ {hi_kp}) :\n"
                f"    a{k-1} * a{k+1} < a{k} ^ 2 :=\n"
                f"  turan_from_enclosure (by norm_num) h{k} "
                f"hp{k-1} h{k-1} hp{k+1} h{k+1} (by norm_num)"
            )
        return "\n\n".join(blocks) + "\n"
