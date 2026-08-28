"""Total-positivity (Polya-frequency) certificates for the Riemann xi -- a
DIFFERENT RH-necessary lens from Jensen hyperbolicity.

RH <=> G(u) = sum_k a_k u^k  (a_k = [z^{2k}] xi(1/2+z))  has only real negative
zeros <=> G is a Polya-FREQUENCY function <=> the one-sided Toeplitz matrix
[a_{i-j}] is TOTALLY POSITIVE (all minors >= 0) [Edrei-Thoma / Aissen-Schoenberg-
Whitney].  The 2x2 minors are log-concavity (`turan.py`); the 3x3 minors are new
degree-3 conditions:

    minor(m) = det [[a_m, a_{m-1}, a_{m-2}],
                    [a_{m+1}, a_m, a_{m-1}],
                    [a_{m+2}, a_{m+1}, a_m]]
             = a_m^3 - 2 a_{m-1} a_m a_{m+1} + a_{m-1}^2 a_{m+2}
               + a_{m-2} a_{m+1}^2 - a_{m-2} a_m a_{m+2}   >=   0.

All a_k > 0, so a WORST-CORNER lower bound (positive monomials at the enclosure
floor, negatives at the ceiling) is exact rational; if it is positive the minor
is, over the whole box.  Certified over imported enclosures; RH-NECESSARY, finite
indices, enclosure-conditional -- same honest scope as `turan.py`/`jensen.py`.

Relabel g0..g4 = a_{m-2}, a_{m-1}, a_m, a_{m+1}, a_{m+2}:
    minor = g2^3 - 2 g1 g2 g3 + g1^2 g4 + g0 g3^2 - g0 g2 g4.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


# Fixed once-proved worst-corner bridge for the 3x3 Toeplitz minor.  Positive
# monomials bounded below at lo, negatives above at hi (mul_le_mul chains);
# nlinarith assembles the nonnegative linear combination.
TOEPLITZ3_BRIDGE_LEMMA = """/-- Worst-corner bridge for the 3x3 Toeplitz minor: a strict rational margin on
    the enclosures forces the minor positive (total-positivity necessary cond.). -/
theorem toeplitz3_pos_of_enclosure
    {g0 g1 g2 g3 g4 lo0 lo1 lo2 lo3 lo4 hi0 hi1 hi2 hi3 hi4 : ℝ}
    (l0 : 0 ≤ lo0) (l1 : 0 ≤ lo1) (l2 : 0 ≤ lo2) (l3 : 0 ≤ lo3) (l4 : 0 ≤ lo4)
    (a0 : lo0 ≤ g0) (a1 : lo1 ≤ g1) (a2 : lo2 ≤ g2) (a3 : lo3 ≤ g3) (a4 : lo4 ≤ g4)
    (b0 : g0 ≤ hi0) (b1 : g1 ≤ hi1) (b2 : g2 ≤ hi2) (b3 : g3 ≤ hi3) (b4 : g4 ≤ hi4)
    (hm : 0 < lo2*lo2*lo2 + lo1*lo1*lo4 + lo0*lo3*lo3
             - 2*hi1*hi2*hi3 - hi0*hi2*hi4) :
    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 := by
  have n0 : (0:ℝ) ≤ g0 := le_trans l0 a0
  have n1 : (0:ℝ) ≤ g1 := le_trans l1 a1
  have n2 : (0:ℝ) ≤ g2 := le_trans l2 a2
  have n3 : (0:ℝ) ≤ g3 := le_trans l3 a3
  have n4 : (0:ℝ) ≤ g4 := le_trans l4 a4
  have p1 : lo2*lo2*lo2 ≤ g2*g2*g2 :=
    mul_le_mul (mul_le_mul a2 a2 l2 n2) a2 l2 (mul_nonneg n2 n2)
  have p2 : lo1*lo1*lo4 ≤ g1*g1*g4 :=
    mul_le_mul (mul_le_mul a1 a1 l1 n1) a4 l4 (mul_nonneg n1 n1)
  have p3 : lo0*lo3*lo3 ≤ g0*g3*g3 :=
    mul_le_mul (mul_le_mul a0 a3 l3 n0) a3 l3 (mul_nonneg n0 n3)
  have q1 : g1*g2*g3 ≤ hi1*hi2*hi3 :=
    mul_le_mul (mul_le_mul b1 b2 n2 (le_trans n1 b1)) b3 n3
      (mul_nonneg (le_trans n1 b1) (le_trans n2 b2))
  have q2 : g0*g2*g4 ≤ hi0*hi2*hi4 :=
    mul_le_mul (mul_le_mul b0 b2 n2 (le_trans n0 b0)) b4 n4
      (mul_nonneg (le_trans n0 b0) (le_trans n2 b2))
  nlinarith [p1, p2, p3, q1, q2, hm]"""


def _rat_lean(x: Fr) -> str:
    x = Fr(x)
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"(({x.numerator} : ℝ) / {x.denominator})"


@dataclass(frozen=True)
class ToeplitzMinorCertificate:
    """Positivity of the 3x3 Toeplitz minors of a_k over a run of enclosures.

    enclosures[k] = (lo, hi), lo_k < a_k < hi_k.  Minors at m = 2 .. len-3 are
    certified (each needs a_{m-2} .. a_{m+2})."""

    name: str
    enclosures: tuple

    def _enc(self):
        return [(Fr(lo), Fr(hi)) for (lo, hi) in self.enclosures]

    def certified_m(self):
        return list(range(2, len(self.enclosures) - 2))

    def minor_lo(self, m: int) -> Fr:
        e = self._enc()
        lo = {i: e[m + i][0] for i in (-2, -1, 0, 1, 2)}
        hi = {i: e[m + i][1] for i in (-2, -1, 0, 1, 2)}
        return (lo[0]*lo[0]*lo[0] + lo[-1]*lo[-1]*lo[2] + lo[-2]*lo[1]*lo[1]
                - 2*hi[-1]*hi[0]*hi[1] - hi[-2]*hi[0]*hi[2])

    def check(self) -> bool:
        e = self._enc()
        if len(e) < 5:
            return False
        if any(not (0 < lo < hi) for lo, hi in e):
            return False
        return all(self.minor_lo(m) > 0 for m in self.certified_m())

    def lean(self) -> str:
        if not self.check():
            raise ValueError(
                f"{self.name}: enclosures do not certify the Toeplitz minors "
                f"(check() False) -- refusing to emit")
        e = self._enc()
        blocks = [TOEPLITZ3_BRIDGE_LEMMA, ""]
        for m in self.certified_m():
            lo = [_rat_lean(e[m + i][0]) for i in (-2, -1, 0, 1, 2)]
            hi = [_rat_lean(e[m + i][1]) for i in (-2, -1, 0, 1, 2)]
            blocks.append(
                f"-- m={m}: 3x3 Toeplitz minor of a_{m-2}..a_{m+2} positive "
                f"(worst-corner {self.minor_lo(m)} > 0)\n"
                f"theorem {self.name}_m{m} {{g0 g1 g2 g3 g4 : ℝ}}\n"
                f"    (a0 : {lo[0]} ≤ g0) (b0 : g0 ≤ {hi[0]})\n"
                f"    (a1 : {lo[1]} ≤ g1) (b1 : g1 ≤ {hi[1]})\n"
                f"    (a2 : {lo[2]} ≤ g2) (b2 : g2 ≤ {hi[2]})\n"
                f"    (a3 : {lo[3]} ≤ g3) (b3 : g3 ≤ {hi[3]})\n"
                f"    (a4 : {lo[4]} ≤ g4) (b4 : g4 ≤ {hi[4]}) :\n"
                f"    0 < g2*g2*g2 + g1*g1*g4 + g0*g3*g3 - 2*g1*g2*g3 - g0*g2*g4 :=\n"
                f"  toeplitz3_pos_of_enclosure (by norm_num) (by norm_num) (by norm_num) "
                f"(by norm_num) (by norm_num)\n"
                f"    a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (by norm_num)")
        return "\n\n".join(blocks) + "\n"
