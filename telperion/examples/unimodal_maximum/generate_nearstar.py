"""Generate the near-star payoff Lean file end to end: Phi^11(N(0,n)) <= 1.

Usage:  python3 examples/unimodal_maximum/generate_nearstar.py [--check]

This is the campaign payoff: the near-star family N(0, s) has

    f(s) = Phi^11(N(0,s)) = (64/621)^(2s+1) * ((4s+3)/(3(s+1)))^11 * (3/2)^(11s)

whose successor ratio is

    Q(s) = f(s+1)/f(s) = (486/529) * (1 + 1/(4s^2 + 11s + 6))^11 ,

DECREASING in s (the inner denominator grows), crossing 1 at s* = 5:
Q(5) < 1 and f(5) = 1 (the tie identity 64*243*23 = 621*576).  So the integer
maximum over n >= 5 sits at n = 5 with f(5) = 1; the emitted theorem is
`forall n >= 5, f n <= 1`.

Why the ratio is kept FACTORED.  Rendering `(1 + 1/(4s^2+11s+6))^11` as a ratio
of expanded polynomials produces degree-132 numerators with 130-digit
coefficients -- unusable for `field_simp; ring` / `nlinarith` / `norm_num`.
Instead the successor ratio is proved monotone STRUCTURALLY: the inner rational
`1 + 1/(4x^2+11x+6)` is nonneg and decreasing on `x >= 0` (its denominator
increases), so its 11th power decreases (`pow_le_pow_left0`), scaled by the
positive constant 486/529.  This stays degree 11 with no expansion.

The generic unimodal-max library is NOT re-inlined here: the file imports
`UNIMODAL_PRELUDE` from `telperion.emit_unimodal` (the kernel-green
`namespace Telperion` block exporting `unimodal_peak` and
`climb_descend_of_ratio`) and references those two lemmas directly.  Only the
per-family proof body -- the factored `r`, `ratio_eq`, `r_dec`, `r_anti`, the
crossing evaluation, and the descent-only assembly -- is rendered here.

Since s0 = s* = 5 there is NO climb region: the family is already past its peak,
so the assembly is descent-only (the `hrup` hypothesis is vacuous by `omega`).

Without --check: writes ``lean_out/NearStarPhi11.lean``.
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

_OUT = Path(__file__).resolve().parent / "lean_out" / "NearStarPhi11.lean"

# The exact Phi^11(N(0,n)) closed form as a pure-arithmetic body in n: the hub
# amplitude a_hub(n) = (4n+3)/(3(n+1)) and the two power terms give exactly
# f(s+1)/f(s) = Q(s) (checked by the ratio honesty pin below).
NEARSTAR_F_LEAN = "(64/621)^(2*n+1) * ((4*n+3)/(3*(n+1)))^11 * (3/2)^(11*n)"

# The successor ratio Q(s) = (486/529)(1 + 1/(4s^2+11s+6))^11, s* = 5, s0 = 5.
_S = sp.Symbol("s", nonnegative=True)
NEARSTAR_RATIO = sp.Rational(486, 529) * (1 + 1 / (4 * _S**2 + 11 * _S + 6)) ** 11


def _nearstar_cert():
    return unimodal_certificate(NEARSTAR_RATIO, s0=5, s_symbol=_S, search_hi=50)


def _assert_honesty_pins(cert) -> None:
    """Fail loudly if the Lean f-def and the certified ratio ever disagree.

    (1) The successor ratio of NEARSTAR_F_LEAN must equal NEARSTAR_RATIO.
    (2) The peak value f(s*) must be <= 1 in exact rationals.
    """
    n = sp.Symbol("n", nonnegative=True)
    f = sp.sympify(NEARSTAR_F_LEAN, locals={"n": n})
    ratio = sp.cancel(f.subs(n, n + 1) / f)
    target = sp.cancel(NEARSTAR_RATIO.subs(_S, n))
    assert sp.simplify(ratio - target) == 0, "ratio honesty pin failed"
    peak = sp.Rational(f.subs(n, cert.s_star))
    assert peak <= 1, f"peak honesty pin failed: f({cert.s_star}) = {peak} > 1"


def build_nearstar_lean() -> str:
    """Emit the self-contained kernel-green near-star payoff Lean file.

    Uses the imported `UNIMODAL_PRELUDE` (the `namespace Telperion` block with
    `unimodal_peak` + `climb_descend_of_ratio`) for the generic library, then
    appends the near-star `f` def and the FACTORED degree-11 descent-only proof
    body and assembly theorem, referencing `Telperion.unimodal_peak` and
    `Telperion.climb_descend_of_ratio`.
    """
    cert = _nearstar_cert()
    _assert_honesty_pins(cert)

    lean_name = "nearstar_phi11"
    f_name = f"{lean_name}_f"
    r_name = f"{f_name}_r"
    sstar = cert.s_star            # 5
    s0 = cert.s0                   # 5 (== sstar: descent-only, no climb)
    assert s0 == sstar, "near-star peak is at s0; emitter is descent-only"
    cross_hi = rat_lean(cert.cross_hi)   # r(5) = (486/529)(162/161)^11 < 1

    lines: list[str] = [
        "import Mathlib",
        "",
        UNIMODAL_PRELUDE.rstrip("\n"),
        "",
        f"-- near-star closed form f(n) = Phi^11(N(0,n))",
        f"noncomputable def {f_name} : ℕ → ℝ := "
        f"fun n => {NEARSTAR_F_LEAN}",
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

    # assembly theorem: descent-only (s0 = s* = 5, hrup vacuous).
    lines.append(
        f"theorem {lean_name} (n : ℕ) (hn : {s0} ≤ n) : {f_name} n ≤ 1 := by"
    )
    lines.append(f"  have hpos : ∀ s, {s0} ≤ s → 0 < {f_name} s := by")
    lines.append(f"    intro s hs; simp only [{f_name}]; positivity")
    lines.append(
        f"  -- no climb region (s0 = s* = {sstar}): the hypothesis s < {sstar} is impossible"
    )
    lines.append(
        f"  have hrup : ∀ s, {s0} ≤ s → s < {sstar} → "
        f"1 ≤ {f_name} (s + 1) / {f_name} s := by"
    )
    lines.append(f"    intro s hs hlt; omega")
    lines.append(
        f"  have hrdn : ∀ s, {sstar} ≤ s → "
        f"{f_name} (s + 1) / {f_name} s ≤ 1 := by"
    )
    lines.append(f"    intro s hs")
    lines.append(f"    rw [{f_name}_ratio_eq s]")
    lines.append(
        f"    -- r anti-mono gives r(↑s) ≤ r(↑{sstar}) = {cross_hi} < 1"
    )
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
        f"  have hmax := Telperion.unimodal_peak hclimb hdesc n hn"
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
        help="regenerate in memory and diff against lean_out/NearStarPhi11.lean",
    )
    args = parser.parse_args(argv)

    src = build_nearstar_lean()

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
