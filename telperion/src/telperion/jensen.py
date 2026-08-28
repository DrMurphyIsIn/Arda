"""Degree-3 Jensen-Polya hyperbolicity for the Riemann xi -- the cubic rung above
`turan.py` (which is the degree-2 case), certified over imported rational
enclosures.

Background.  RH <=> G(u) = sum_k a_k u^k  (a_k = [z^{2k}] xi(1/2+z))  lies in the
Laguerre-Polya class <=> ALL Jensen polynomials of the EGF sequence

    gamma_k = k! * a_k

are hyperbolic (real-rooted).  [Normalization fixed empirically: with (2k)! a_k
the Jensen polynomials are NOT hyperbolic; with k! a_k they are -- the EGF
coefficients of G, per the classical Craven-Csordas / Jensen characterization.]
The degree-d Jensen polynomial with shift n is J^{d,n}(X) = sum_j C(d,j) g_{n+j} X^j.
Degree-2 hyperbolicity is the Turan inequality (`turan.py`); this module does
degree 3.

The cubic  J^{3,n}(X) = g0 + 3 g1 X + 3 g2 X^2 + g3 X^3   (g_i = gamma_{n+i})
has three real roots (hyperbolic) iff its discriminant is positive:

    Delta = 162 g0 g1 g2 g3 + 81 g1^2 g2^2
            - 108 g0 g2^3 - 108 g1^3 g3 - 27 g0^2 g3^2   >   0.

All g_i > 0, so a WORST-CORNER lower bound (positive monomials at the enclosure
floor, negative monomials at the ceiling) is an exact rational:

    Delta_lo = 162 lo0 lo1 lo2 lo3 + 81 lo1^2 lo2^2
               - 108 hi0 hi2^3 - 108 hi1^3 hi3 - 27 hi0^2 hi3^2.

If Delta_lo > 0 then Delta(g) >= Delta_lo > 0 for every triple in the box, so
J^{3,n} is hyperbolic.  Certified over imported enclosures; RH-NECESSARY, finite
indices, enclosure-conditional.  Same trust model and honest scope as `turan.py`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


# Fixed once-proved bridge: worst-corner monotone bound on the cubic discriminant.
# Every monomial of Delta is bounded by a mul_le_mul chain (positives below by the
# lo-corner, negatives above by the hi-corner); nlinarith then assembles the
# nonnegative linear combination.  Products spelled with `*` (not `^`) so the
# monotonicity chains and `nlinarith` normalization line up.
CUBIC_JENSEN_BRIDGE_LEMMA = """/-- Worst-corner bridge for the cubic Jensen discriminant: a strict rational
    margin on the enclosures forces `Delta(g) > 0`, hence three real roots. -/
theorem cubic_jensen_pos_of_enclosure
    {g0 g1 g2 g3 lo0 lo1 lo2 lo3 hi0 hi1 hi2 hi3 : ℝ}
    (l0 : 0 ≤ lo0) (l1 : 0 ≤ lo1) (l2 : 0 ≤ lo2) (l3 : 0 ≤ lo3)
    (a0 : lo0 ≤ g0) (a1 : lo1 ≤ g1) (a2 : lo2 ≤ g2) (a3 : lo3 ≤ g3)
    (b0 : g0 ≤ hi0) (b1 : g1 ≤ hi1) (b2 : g2 ≤ hi2) (b3 : g3 ≤ hi3)
    (hm : 0 < 162*lo0*lo1*lo2*lo3 + 81*lo1*lo1*lo2*lo2
             - 108*hi0*hi2*hi2*hi2 - 108*hi1*hi1*hi1*hi3 - 27*hi0*hi0*hi3*hi3) :
    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2
        - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 := by
  have n0 : (0:ℝ) ≤ g0 := le_trans l0 a0
  have n1 : (0:ℝ) ≤ g1 := le_trans l1 a1
  have n2 : (0:ℝ) ≤ g2 := le_trans l2 a2
  have n3 : (0:ℝ) ≤ g3 := le_trans l3 a3
  have p1 : lo0*lo1*lo2*lo3 ≤ g0*g1*g2*g3 :=
    mul_le_mul (mul_le_mul (mul_le_mul a0 a1 l1 n0) a2 l2 (mul_nonneg n0 n1)) a3 l3
      (mul_nonneg (mul_nonneg n0 n1) n2)
  have p2 : lo1*lo1*lo2*lo2 ≤ g1*g1*g2*g2 :=
    mul_le_mul (mul_le_mul (mul_le_mul a1 a1 l1 n1) a2 l2 (mul_nonneg n1 n1)) a2 l2
      (mul_nonneg (mul_nonneg n1 n1) n2)
  have q1 : g0*g2*g2*g2 ≤ hi0*hi2*hi2*hi2 :=
    mul_le_mul (mul_le_mul (mul_le_mul b0 b2 n2 (le_trans n0 b0)) b2 n2
      (mul_nonneg (le_trans n0 b0) (le_trans n2 b2))) b2 n2
      (mul_nonneg (mul_nonneg (le_trans n0 b0) (le_trans n2 b2)) (le_trans n2 b2))
  have q2 : g1*g1*g1*g3 ≤ hi1*hi1*hi1*hi3 :=
    mul_le_mul (mul_le_mul (mul_le_mul b1 b1 n1 (le_trans n1 b1)) b1 n1
      (mul_nonneg (le_trans n1 b1) (le_trans n1 b1))) b3 n3
      (mul_nonneg (mul_nonneg (le_trans n1 b1) (le_trans n1 b1)) (le_trans n1 b1))
  have q3 : g0*g0*g3*g3 ≤ hi0*hi0*hi3*hi3 :=
    mul_le_mul (mul_le_mul (mul_le_mul b0 b0 n0 (le_trans n0 b0)) b3 n3
      (mul_nonneg (le_trans n0 b0) (le_trans n0 b0))) b3 n3
      (mul_nonneg (mul_nonneg (le_trans n0 b0) (le_trans n0 b0)) (le_trans n3 b3))
  nlinarith [p1, p2, q1, q2, q3, hm]"""


def _rat_lean(x: Fr) -> str:
    x = Fr(x)
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"(({x.numerator} : ℝ) / {x.denominator})"


@dataclass(frozen=True)
class CubicJensenCertificate:
    """Hyperbolicity of the cubic Jensen polynomials J^{3,n} of xi, for the interior
    shifts of a run of rational enclosures of gamma_k = k! a_k.

    enclosures[k] = (lo, hi) with lo_k < gamma_k < hi_k (exact rationals).  Shifts
    n = 0 .. len-4 are certified (each needs gamma_n .. gamma_{n+3})."""

    name: str
    enclosures: tuple

    def _enc(self):
        return [(Fr(lo), Fr(hi)) for (lo, hi) in self.enclosures]

    def certified_shifts(self):
        return list(range(0, len(self.enclosures) - 3))

    def disc_lo(self, n: int) -> Fr:
        """Worst-corner lower bound of the cubic discriminant at shift n."""
        e = self._enc()
        lo = [e[n + i][0] for i in range(4)]
        hi = [e[n + i][1] for i in range(4)]
        return (162*lo[0]*lo[1]*lo[2]*lo[3] + 81*lo[1]*lo[1]*lo[2]*lo[2]
                - 108*hi[0]*hi[2]*hi[2]*hi[2] - 108*hi[1]*hi[1]*hi[1]*hi[3]
                - 27*hi[0]*hi[0]*hi[3]*hi[3])

    def check(self) -> bool:
        """Exact-rational self-check: enclosures well-formed and every worst-corner
        discriminant bound strictly positive.  Blocks emission on failure."""
        e = self._enc()
        if len(e) < 4:
            return False
        if any(not (0 < lo < hi) for lo, hi in e):
            return False
        return all(self.disc_lo(n) > 0 for n in self.certified_shifts())

    def lean(self) -> str:
        if not self.check():
            raise ValueError(
                f"{self.name}: enclosures do not certify cubic hyperbolicity "
                f"(check() False) -- refusing to emit")
        e = self._enc()
        blocks = [CUBIC_JENSEN_BRIDGE_LEMMA, ""]
        for n in self.certified_shifts():
            lo = [_rat_lean(e[n + i][0]) for i in range(4)]
            hi = [_rat_lean(e[n + i][1]) for i in range(4)]
            blocks.append(
                f"-- shift n={n}: J^{{3,{n}}} hyperbolic (gamma_{n}..gamma_{n+3}); "
                f"worst-corner Delta_lo = {self.disc_lo(n)} > 0\n"
                f"theorem {self.name}_n{n} {{g0 g1 g2 g3 : ℝ}}\n"
                f"    (a0 : {lo[0]} ≤ g0) (b0 : g0 ≤ {hi[0]})\n"
                f"    (a1 : {lo[1]} ≤ g1) (b1 : g1 ≤ {hi[1]})\n"
                f"    (a2 : {lo[2]} ≤ g2) (b2 : g2 ≤ {hi[2]})\n"
                f"    (a3 : {lo[3]} ≤ g3) (b3 : g3 ≤ {hi[3]}) :\n"
                f"    0 < 162*g0*g1*g2*g3 + 81*g1*g1*g2*g2"
                f" - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3 :=\n"
                f"  cubic_jensen_pos_of_enclosure (by norm_num) (by norm_num) "
                f"(by norm_num) (by norm_num)\n"
                f"    a0 a1 a2 a3 b0 b1 b2 b3 (by norm_num)")
        return "\n\n".join(blocks) + "\n"
