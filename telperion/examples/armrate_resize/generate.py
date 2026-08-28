"""Generate the arm-load resize Lean file end to end: armRate(n)^11 <= 1, all n.

Usage:  python3 examples/armrate_resize/generate.py [--check]

Step 2 of the Hnorm/Hdom arm-rate frontier (the Telperion emitter for Step 1's
`R3Cert/R47ArmRate.lean`).  The rate-normalized arm value on the arm-load axis is

    armRate(n)^11 = A(n)^11 / (621/64)^(1+2n),   A(n) = (3/2)^n (4n+3)/(3(n+1)),

i.e.  f(n) = (64/621)^(2n+1) * ((4n+3)/(3(n+1)))^11 * (3/2)^(11n).

This is IDENTICALLY the near-star payoff sequence `Phi^11(N(0,n))`
(`examples/unimodal_maximum/generate_nearstar.py`): the arm-load resize axis and
the near-star campaign are the SAME unimodal integer sequence.  Its successor
ratio is

    Q(s) = f(s+1)/f(s) = (486/529) * (1 + 1/(4s^2 + 11s + 6))^11 ,

DECREASING in s (the inner denominator grows), crossing 1 exactly once at s* = 5:
Q(4) > 1, Q(5) < 1, and f(5) = 1 (the tie identity 64*243*23 = 621*576).

Where the near-star emit is DESCENT-ONLY (it proves `forall n >= 5, f n <= 1`),
this arm-rate emit takes the FULL range `s0 = 0`: the finite climb 0..4 (via the
same decreasing ratio: Q(s) >= Q(4) > 1) plus the descent, giving the marginal
resize envelope `forall n, f n <= 1` over EVERY load n -- matching the hand proof
`R3Cert.Step3.armRate11_le_one`.  The two `_dec`/`_cross_*` certificate leaves are
reused verbatim from the near-star; only the climb assembly is new.

Why the ratio is kept FACTORED (same reason as the near-star): rendering
`(1 + 1/(4s^2+11s+6))^11` expanded gives degree-132 numerators with 130-digit
coefficients, unusable for `field_simp`/`nlinarith`/`norm_num`.  The successor
ratio is proved monotone STRUCTURALLY: `1 + 1/(4x^2+11x+6)` is nonneg and
decreasing on `x >= 0` (its denominator grows), so its 11th power decreases
(`pow_le_pow_left0`), scaled by the positive constant 486/529.  Degree 11, no
expansion.

The generic unimodal-max library is imported (`UNIMODAL_PRELUDE` from
`telperion.emit_unimodal`: the kernel-green `namespace Telperion` block with
`unimodal_peak` + `climb_descend_of_ratio`); only the per-family body is rendered.

SCOPE / HONESTY: the certifier + per-instance obligations are exact-arithmetic
validated here; the Lean KERNEL verdict is CI-only (this repo cannot run `lake`
locally).  conjecture1_proved = False.

Without --check: writes ``lean_out/ArmRateResize.lean``.
With --check: regenerates in memory and diffs against the written copy.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import unimodal_certificate  # noqa: E402
from telperion.emit_unimodal import UNIMODAL_PRELUDE  # noqa: E402
from telperion.expr import rat_lean  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean_out" / "ArmRateResize.lean"

# f(n) = armRate(n)^11 = A(n)^11 / (621/64)^(1+2n), the near-star closed form.
ARMRATE_F_LEAN = "(64/621)^(2*n+1) * ((4*n+3)/(3*(n+1)))^11 * (3/2)^(11*n)"

# The successor ratio Q(s) = (486/529)(1 + 1/(4s^2+11s+6))^11, s* = 5, s0 = 0.
_S = sp.Symbol("s", nonnegative=True)
ARMRATE_RATIO = sp.Rational(486, 529) * (1 + 1 / (4 * _S**2 + 11 * _S + 6)) ** 11


def _armrate_cert():
    return unimodal_certificate(ARMRATE_RATIO, s0=0, s_symbol=_S, search_hi=50)


def _assert_honesty_pins(cert) -> None:
    """Fail loudly if the Lean f-def and the certified ratio ever disagree.

    (1) The successor ratio of ARMRATE_F_LEAN must equal ARMRATE_RATIO.
    (2) The peak value f(s*) must be <= 1 in exact rationals.
    (3) f(s*) must be exactly 1 (the tie), and the crossing must straddle 1.
    """
    n = sp.Symbol("n", nonnegative=True)
    f = sp.sympify(ARMRATE_F_LEAN, locals={"n": n})
    ratio = sp.cancel(f.subs(n, n + 1) / f)
    target = sp.cancel(ARMRATE_RATIO.subs(_S, n))
    assert sp.simplify(ratio - target) == 0, "ratio honesty pin failed"
    peak = sp.Rational(f.subs(n, cert.s_star))
    assert peak == 1, f"peak honesty pin failed: f({cert.s_star}) = {peak} != 1"
    assert cert.cross_hi < 1 < cert.cross_lo, "crossing must straddle 1 at s*"
    assert cert.s0 == 0 and cert.s_star == 5, "arm-rate family is full-range 0..5"


def build_armrate_lean() -> str:
    """Emit the self-contained kernel-green arm-rate resize Lean file.

    Reuses `UNIMODAL_PRELUDE` for the generic library, then appends the arm-rate
    `f` def, the FACTORED degree-11 ratio body (identical to the near-star:
    `ratio_eq`, `r_dec`, `r_anti`), both crossing evaluations, and the FULL-range
    (climb + descent) assembly of `forall n, f n <= 1`.
    """
    cert = _armrate_cert()
    _assert_honesty_pins(cert)

    lean_name = "armrate_resize"
    f_name = f"{lean_name}_f"
    r_name = f"{f_name}_r"
    sstar = cert.s_star            # 5
    s0 = cert.s0                   # 0 (full range: climb 0..4 then descent)
    cross_hi = rat_lean(cert.cross_hi)   # r(5) < 1
    cross_lo = rat_lean(cert.cross_lo)   # r(4) > 1
    slast = sstar - 1              # 4 (last climb index)

    lines: list[str] = [
        "import Mathlib",
        "",
        UNIMODAL_PRELUDE.rstrip("\n"),
        "",
        f"-- arm-rate closed form f(n) = armRate(n)^11 = A(n)^11 / (621/64)^(1+2n)",
        f"noncomputable def {f_name} : ℕ → ℝ := "
        f"fun n => {ARMRATE_F_LEAN}",
        "",
    ]

    # Factored successor ratio r(x) = (486/529) * (1 + 1/(4x^2+11x+6))^11.
    lines.append(
        f"-- successor-ratio closed form (FACTORED, degree 11): "
        f"r(x) = (486/529) * (1 + 1/(4x^2+11x+6))^11"
    )
    lines.append(
        f"noncomputable def {r_name} : ℝ → ℝ := "
        f"fun x => (486/529) * (1 + 1/(4*x^2+11*x+6))^11"
    )
    lines.append("")

    # ratio identity f(s+1)/f(s) = r(s).  field_simp + ring on the FACTORED form.
    lines.append(f"-- ratio identity: f(s+1)/f(s) = {r_name} (↑s)")
    lines.append(
        f"private lemma {f_name}_ratio_eq (s : ℕ) : "
        f"{f_name} (s + 1) / {f_name} s = {r_name} (s : ℝ) := by"
    )
    lines.append(f"  simp only [{f_name}, {r_name}]")
    lines.append(f"  push_cast")
    lines.append(f"  field_simp")
    lines.append(f"  ring")
    lines.append("")

    # r decreasing on x >= 0, STRUCTURALLY.
    lines.append(
        f"-- {r_name} is decreasing on x >= 0 "
        f"(structural: 11th power of a decreasing nonneg base)"
    )
    lines.append(
        f"private lemma {f_name}_r_dec (x : ℝ) (hx : 0 ≤ x) : "
        f"{r_name} (x + 1) ≤ {r_name} x := by"
    )
    lines.append(f"  simp only [{r_name}]")
    lines.append(f"  have hdx : (0 : ℝ) < 4*x^2+11*x+6 := by positivity")
    lines.append(f"  have hdx1 : (0 : ℝ) < 4*(x+1)^2+11*(x+1)+6 := by positivity")
    lines.append(
        f"  have hden : 4*x^2+11*x+6 ≤ 4*(x+1)^2+11*(x+1)+6 := by nlinarith [hx]"
    )
    lines.append(
        f"  have hinv : 1/(4*(x+1)^2+11*(x+1)+6) ≤ 1/(4*x^2+11*x+6) := "
        f"one_div_le_one_div_of_le hdx hden"
    )
    lines.append(
        f"  have hbase : (1 : ℝ) + 1/(4*(x+1)^2+11*(x+1)+6) ≤ "
        f"1 + 1/(4*x^2+11*x+6) := by linarith"
    )
    lines.append(
        f"  have hnn : (0 : ℝ) ≤ 1 + 1/(4*(x+1)^2+11*(x+1)+6) := by positivity"
    )
    lines.append(
        f"  have hpow : (1 + 1/(4*(x+1)^2+11*(x+1)+6))^11 ≤ "
        f"(1 + 1/(4*x^2+11*x+6))^11 := pow_le_pow_left₀ hnn hbase 11"
    )
    lines.append(f"  have hc : (0 : ℝ) ≤ 486/529 := by norm_num")
    lines.append(f"  exact mul_le_mul_of_nonneg_left hpow hc")
    lines.append("")

    # r anti-monotone in the Nat index (stack r_dec via Nat.le_induction).
    lines.append(f"-- {r_name} anti-monotone in the ℕ index")
    lines.append(
        f"private lemma {f_name}_r_anti (a b : ℕ) (hab : a ≤ b) : "
        f"{r_name} (b : ℝ) ≤ {r_name} (a : ℝ) := by"
    )
    lines.append(f"  induction b, hab using Nat.le_induction with")
    lines.append(f"  | base => exact le_refl _")
    lines.append(f"  | succ k hk ih =>")
    lines.append(
        f"    have hstep : {r_name} ((k : ℝ) + 1) ≤ {r_name} (k : ℝ) := "
        f"{f_name}_r_dec (k : ℝ) (by positivity)"
    )
    lines.append(
        f"    have hcast : {r_name} (((k + 1 : ℕ)) : ℝ) ≤ {r_name} (k : ℝ) := by"
    )
    lines.append(f"      push_cast; exact hstep")
    lines.append(f"    exact le_trans hcast ih")
    lines.append("")

    # crossing (hi): r(5) = cross_hi < 1, by norm_num on the factored form.
    lines.append(f"-- crossing (hi): {r_name} (↑{sstar}) = {cross_hi} < 1")
    lines.append(
        f"private lemma {f_name}_cross_hi_eval : "
        f"{r_name} (({sstar} : ℕ) : ℝ) = {cross_hi} := by"
    )
    lines.append(f"  simp only [{r_name}]")
    lines.append(f"  norm_num")
    lines.append("")

    # crossing (lo): r(4) = cross_lo > 1, by norm_num on the factored form.
    lines.append(f"-- crossing (lo): {r_name} (↑{slast}) = {cross_lo} > 1")
    lines.append(
        f"private lemma {f_name}_cross_lo_eval : "
        f"{r_name} (({slast} : ℕ) : ℝ) = {cross_lo} := by"
    )
    lines.append(f"  simp only [{r_name}]")
    lines.append(f"  norm_num")
    lines.append("")

    # assembly theorem: FULL range (s0 = 0), climb 0..4 then descent.
    lines.append(
        f"-- marginal resize envelope: armRate(n)^11 <= 1 for EVERY load n"
    )
    lines.append(
        f"theorem {lean_name} (n : ℕ) : {f_name} n ≤ 1 := by"
    )
    lines.append(f"  have hpos : ∀ s, {s0} ≤ s → 0 < {f_name} s := by")
    lines.append(f"    intro s hs; simp only [{f_name}]; positivity")
    lines.append(
        f"  -- climb region 0..{slast}: r(s) >= r(↑{slast}) = {cross_lo} >= 1"
    )
    lines.append(
        f"  have hrup : ∀ s, {s0} ≤ s → s < {sstar} → "
        f"1 ≤ {f_name} (s + 1) / {f_name} s := by"
    )
    lines.append(f"    intro s hs hlt")
    lines.append(f"    rw [{f_name}_ratio_eq s]")
    lines.append(f"    have hmono := {f_name}_r_anti s {slast} (by omega)")
    lines.append(f"    rw [{f_name}_cross_lo_eval] at hmono")
    lines.append(f"    norm_num at hmono ⊢")
    lines.append(f"    linarith")
    lines.append(
        f"  -- descent region s >= {sstar}: r(s) <= r(↑{sstar}) = {cross_hi} <= 1"
    )
    lines.append(
        f"  have hrdn : ∀ s, {sstar} ≤ s → "
        f"{f_name} (s + 1) / {f_name} s ≤ 1 := by"
    )
    lines.append(f"    intro s hs")
    lines.append(f"    rw [{f_name}_ratio_eq s]")
    lines.append(f"    have hmono := {f_name}_r_anti {sstar} s hs")
    lines.append(f"    rw [{f_name}_cross_hi_eval] at hmono")
    lines.append(f"    norm_num at hmono ⊢")
    lines.append(f"    linarith")
    lines.append(
        f"  obtain ⟨hclimb, hdesc⟩ := Telperion.climb_descend_of_ratio "
        f"{f_name} {s0} {sstar}"
    )
    lines.append(f"      (by norm_num) hpos hrup hrdn")
    lines.append(
        f"  have hmax := Telperion.unimodal_peak hclimb hdesc n (Nat.zero_le n)"
    )
    lines.append(
        f"  -- peak value: f({sstar}) = 1 (the tie 64*243*23 = 621*576)"
    )
    lines.append(f"  have hpeak : {f_name} {sstar} ≤ 1 := by")
    lines.append(f"    simp only [{f_name}]; norm_num")
    lines.append(f"  linarith [hmax, hpeak]")

    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="regenerate in memory and diff against lean_out/ArmRateResize.lean",
    )
    args = parser.parse_args(argv)

    src = build_armrate_lean()

    if args.check:
        if not _OUT.exists():
            print(f"MISSING: {_OUT} (run without --check to write it)")
            return 1
        if _OUT.read_text() != src:
            print(f"DRIFT: {_OUT} differs from freshly generated output")
            return 1
        print(f"OK: {_OUT} matches freshly generated output")
        return 0

    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"WROTE: {_OUT} ({len(src)} chars)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
