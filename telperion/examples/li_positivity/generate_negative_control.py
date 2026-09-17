"""Generate the Li-ladder NEGATIVE-CONTROL twin: a synthetic off-line multiset on which the
Li-type sums go negative, certified IN-KERNEL (no trust seam at all).

    python examples/li_positivity/generate_negative_control.py           # write lean/LiNegativeControl.lean
    python examples/li_positivity/generate_negative_control.py --check    # drift check (no write)

Route B / B1 (RH_ROUTES_ROADMAP_2026-09-16.md): a ladder that can only ever say "positive" is not an
instrument.  This twin shows the SAME certificate shape fires on something FALSE.

The multiset.  `S₀ = {σ ± it, (1−σ) ± it}` with rational `σ ≠ 1/2` — ONE off-line quadruple, closed
under `ρ ↦ 1 − conj ρ` and under conjugation, avoiding 0 and 1.  It is exactly the input of the
in-tree finite Bombieri–Lagarias core `bl_finite_multiset` (RvMBlFiniteMultiset.lean, B7-i):

    (∀ n > 0, 0 ≤ Re ∑_{ρ∈S} (1 − ((1 − 1/ρ)⁻¹)^n))  ↔  ∀ ρ ∈ S, Re ρ = 1/2.

Default `σ = 3/4, t = 1`: then `w(ρ) = ρ/(ρ−1)` takes the Gaussian-rational values
`(13 ∓ 16i)/17` (|w| > 1) and `(13 ∓ 16i)/25` (|w| < 1), every Li-type sum is an exact rational, and

    n = 1..5 : sum ≥ 0      (the instrument is SILENT — Freitas-type delocalization in miniature:
                              an off-line point does not show at the first rungs)
    n = 6    : sum = −309804177801344/5892961181640625 ≈ −0.0526   (the instrument FIRES)

The emitted Lean file proves all of this with `norm_num`/`simp` on exact rationals — the certificate
literals are the SAME shape as the ladder's (a rung index and a rational bound) but the sign is
opposite and, because the multiset is finite and rational, the bound is DISCHARGED in-kernel rather
than carried as an Arb hypothesis.  The file then routes the negative rung through
`bl_finite_multiset` to conclude `¬ ∀ ρ ∈ S₀, Re ρ = 1/2`: the criterion's own forward direction
certifies that the negativity is the detection of the off-line point.  It also states the exact
structural twin of the ladder's `li_neg_refutes_rh` (a negative certified upper bound refutes
"all on the line") and instantiates it with the in-kernel value.

HONEST SCOPE.  `S₀` is a synthetic finite multiset, not a zero set of anything; this file carries
ZERO zeta content and ZERO RH content.  It certifies that the Li-type positivity instrument is not
tautologically positive.  conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

_OUT = Path(__file__).resolve().parent / "lean" / "LiNegativeControl.lean"

SIGMA = Fraction(3, 4)   # off-line real part (≠ 1/2)
T = Fraction(1)          # imaginary part
MAX_N = 12               # rungs scanned for the first negativity (must fire within this range)

GRat = tuple[Fraction, Fraction]  # Gaussian rational (re, im)


def _mul(a: GRat, b: GRat) -> GRat:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _inv(a: GRat) -> GRat:
    n = a[0] * a[0] + a[1] * a[1]
    return (a[0] / n, -a[1] / n)


def _pow(a: GRat, n: int) -> GRat:
    p: GRat = (Fraction(1), Fraction(0))
    for _ in range(n):
        p = _mul(p, a)
    return p


def w_of(rho: GRat) -> GRat:
    """`(1 − 1/ρ)⁻¹` exactly (the `wOf` of RvMBlFiniteMultiset)."""
    one: GRat = (Fraction(1), Fraction(0))
    r = _inv(rho)
    return _inv((one[0] - r[0], one[1] - r[1]))


def multiset(sigma: Fraction = SIGMA, t: Fraction = T) -> list[GRat]:
    """`{σ+it, σ−it, (1−σ)+it, (1−σ)−it}` — closed under ρ ↦ 1 − conj ρ and conjugation."""
    return [(sigma, t), (sigma, -t), (1 - sigma, t), (1 - sigma, -t)]


def li_type_sum(S: list[GRat], n: int) -> Fraction:
    """`Re ∑_{ρ∈S} (1 − w(ρ)^n)` exactly."""
    return sum((1 - _pow(w_of(rho), n)[0] for rho in S), Fraction(0))


def first_negative(S: list[GRat], max_n: int = MAX_N) -> tuple[int, list[Fraction]]:
    """(first n ≥ 1 with a negative sum, [sums for n=1..that n]); refuses if none fires."""
    sums = []
    for n in range(1, max_n + 1):
        s = li_type_sum(S, n)
        sums.append(s)
        if s < 0:
            return n, sums
    raise ValueError(
        f"negative control REFUSED: no Li-type sum negative for n ≤ {max_n} on {S}; "
        "the control must FIRE (it does, for every off-line multiset, by bl_finite_multiset) — "
        "raise MAX_N or pick a point further off the line")


# ---------------------------------------------------------------- Lean rendering

def _lean_rat(q: Fraction) -> str:
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def _lean_c(rho: GRat) -> str:
    """`σ + t*I` / `σ - t*I` as a ℂ literal (rationals rendered p/q)."""
    re, im = rho
    if im >= 0:
        return f"{_lean_rat(re)} + {_lean_rat(im)} * I" if im != 1 else f"{_lean_rat(re)} + I"
    return f"{_lean_rat(re)} - {_lean_rat(-im)} * I" if -im != 1 else f"{_lean_rat(re)} - I"


def _lean_w(w: GRat) -> str:
    """w = (a + b i)/d with a common denominator, as `(a ± b * I) / d`."""
    from math import lcm
    d = lcm(w[0].denominator, w[1].denominator)
    a = w[0].numerator * (d // w[0].denominator)
    b = w[1].numerator * (d // w[1].denominator)
    sgn = "+" if b >= 0 else "-"
    return f"({a} {sgn} {abs(b)} * I) / {d}"


def build(sigma: Fraction = SIGMA, t: Fraction = T) -> str:
    assert sigma != Fraction(1, 2), "the control needs an OFF-line point"
    assert 0 < sigma < 1 and t != 0
    S = multiset(sigma, t)
    ws = [w_of(rho) for rho in S]
    n_fire, sums = first_negative(S)
    fire_val = sums[-1]
    names = ["a", "b", "c", "d"]

    w_lemmas = "\n".join(
        f"theorem w_{nm} : (1 - 1 / ({_lean_c(rho)} : ℂ))⁻¹ = {_lean_w(w)} := by\n"
        f"  apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply] <;> norm_num"
        for nm, rho, w in zip(names, S, ws))
    sum_rhs = "\n    + ".join(f"(1 - ({_lean_w(w)} : ℂ) ^ n).re" for w in ws)
    silent = "\n".join(
        f"/-- Rung n={n}: the instrument is SILENT (sum = {_lean_rat(s)} ≥ 0) — an off-line point need not\n"
        f"    show at the first rungs (delocalization in miniature). -/\n"
        f"theorem negctrl_rung_{n}_nonneg : 0 ≤ liTypeSum S₀ {n} := by\n"
        f"  rw [S₀_sum]; simp [pow_succ, Complex.mul_re, Complex.mul_im]; norm_num\n"
        for n, s in zip(range(1, n_fire), sums[:-1]))
    pts = ", ".join(_lean_c(rho) for rho in S)
    return f"""/- GENERATED by examples/li_positivity/generate_negative_control.py — DO NOT EDIT BY HAND.
   Regenerate & verify:  python examples/li_positivity/generate_negative_control.py --check

   LiNegativeControl — the Li ladder's NEGATIVE-CONTROL TWIN (Route B / B1).

   A synthetic symmetric multiset with ONE off-line quadruple,
       S₀ = {{{pts}}},
   the input of the finite Bombieri–Lagarias core `bl_finite_multiset` (RvMBlFiniteMultiset.lean).
   Its Li-type sums  Re ∑_{{ρ∈S₀}} (1 − ((1 − 1/ρ)⁻¹)^n)  are exact rationals:
   nonnegative for n = 1..{n_fire - 1} (the instrument is silent) and NEGATIVE at n = {n_fire}
   (sum = {_lean_rat(fire_val)}): the instrument FIRES.  Every fact below is decided in-kernel by
   `simp`/`norm_num` on exact rationals — NO Arb hypothesis, no trust seam.  Same certificate shape as
   the ladder's rungs, opposite sign, hypothesis discharged.

   ZERO zeta content, ZERO RH content: S₀ is not the zero set of anything.  This file certifies only
   that the Li-type positivity instrument is not tautologically positive.  conjecture1_proved = False. -/

import RvMBlFiniteMultiset

open Complex Finset

namespace LiNegativeControl

/-- The Li-type sum of `bl_finite_multiset`, verbatim: `Re ∑_{{ρ∈S}} (1 − ((1 − 1/ρ)⁻¹)^n)`. -/
noncomputable def liTypeSum (S : Finset ℂ) (n : ℕ) : ℝ :=
  (∑ ρ ∈ S, (1 - ((1 - 1 / ρ)⁻¹) ^ n)).re

/-- The synthetic multiset: one off-line quadruple `σ ± it, (1−σ) ± it` with σ = {_lean_rat(sigma)}, t = {_lean_rat(t)}. -/
noncomputable def S₀ : Finset ℂ := {{{pts}}}

-- `w(ρ) = (1 − 1/ρ)⁻¹ = ρ/(ρ−1)` on the four points, as exact Gaussian rationals.
{w_lemmas}

/-- The Li-type sum on `S₀` in closed form (four exact Gaussian-rational powers). -/
theorem S₀_sum (n : ℕ) : liTypeSum S₀ n =
    {sum_rhs} := by
  unfold liTypeSum S₀
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_pair, w_a, w_b, w_c, w_d]
  · simp only [Complex.add_re]; ring
  · norm_num [Complex.ext_iff]
  · simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num [Complex.ext_iff]
  · simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num [Complex.ext_iff]

{silent}
/-- Rung n={n_fire}: the exact value — NEGATIVE.  The certificate literal (rung index + rational bound)
    has the ladder's shape; here the kernel computes it outright. -/
theorem negctrl_fires_value : liTypeSum S₀ {n_fire} = {_lean_rat(fire_val)} := by
  rw [S₀_sum]; simp [pow_succ, Complex.mul_re, Complex.mul_im]; norm_num

/-- **The negative control FIRES**: a Li-type sum on `S₀` is strictly negative. -/
theorem negctrl_fires : liTypeSum S₀ {n_fire} < 0 := by
  rw [negctrl_fires_value]; norm_num

theorem S₀_zero_notin : (0:ℂ) ∉ S₀ := by
  unfold S₀; simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num [Complex.ext_iff]
theorem S₀_one_notin : (1:ℂ) ∉ S₀ := by
  unfold S₀; simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num [Complex.ext_iff]
theorem S₀_sym : ∀ ρ ∈ S₀, 1 - (starRingEnd ℂ) ρ ∈ S₀ := by
  unfold S₀; simp only [Finset.mem_insert, Finset.mem_singleton]
  intro ρ h
  rcases h with h | h | h | h <;> subst h <;> norm_num [Complex.ext_iff, map_ofNat]

/-- The structural twin of the ladder's `li_neg_refutes_rh`: a certified NEGATIVE upper bound on
    any Li-type rung of a finite symmetric multiset refutes "every point on the line", through the
    finite BL criterion's own forward direction. -/
theorem negctrl_neg_refutes_online (n : ℕ) (hn : 0 < n) (hi : ℝ)
    (hhi : liTypeSum S₀ n ≤ hi) (hneg : hi < 0) :
    ¬ ∀ ρ ∈ S₀, ρ.re = 1/2 :=
  fun hon =>
    absurd ((bl_finite_multiset S₀ S₀_zero_notin S₀_one_notin S₀_sym).mpr hon n hn)
      (not_le.mpr (lt_of_le_of_lt hhi hneg))

/-- **The instrument detects the off-line point**: the twin instantiated with the in-kernel
    value — the `hhi` that is a trust seam on the real ladder is DISCHARGED here. -/
theorem negctrl_detects_offline : ¬ ∀ ρ ∈ S₀, ρ.re = 1/2 :=
  negctrl_neg_refutes_online {n_fire} (by norm_num) _ (le_of_eq negctrl_fires_value) (by norm_num)

end LiNegativeControl
"""


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LiNegativeControl.lean does not match regeneration")
            return 1
        print("check: OK (negative control matches frozen output byte-for-byte)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
