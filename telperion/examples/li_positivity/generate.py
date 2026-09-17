"""Generate the Li positivity ladder: enclose -> certify -> emit -> write.

    python examples/li_positivity/generate.py           # write lean/LiPositivity.lean (+ LiPositivityBundle.lean)
    python examples/li_positivity/generate.py --check    # drift check (no write)
    python examples/li_positivity/generate.py --trial 100
        # write lean/LiPositivityTrial_n100.lean + lean/LiPositivityTrialBundle_n100.lean
        # (throughput trial; NOT wired into the lakefile, NOT committed — see .gitignore)

Twenty rungs of Li's criterion (RH-roadmap Track 2), onto the upstream
already-formalized reduction (pinned in lean/lakefile.toml):

    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

Per rung n = 0..N-1 the emitter proves `0 ≤ (taylorCoeff riemannXi n).re` from a
certified positive rational lower bound (kind `li_positivity`); the bound comes
from `telperion.li_coeff.enclose_li_coeffs` — Arb ball arithmetic on the
pole-free series route, self-checked against the published Li–Keiper values
before any box is handed out.  The file also carries `li_neg_refutes_rh`, the
falsifiability face: a certified NEGATIVE upper bound on any rung would refute
RH outright through the same upstream equivalence (never expected to fire).

Lower bounds are rounded DOWN to 12 significant decimals before emission: a
smaller positive lower bound is still a rigorous lower bound, and the Lean
literals stay readable.

BUNDLE FACE (Route B / B1 hypothesis-aggregation discipline).  Alongside the
per-rung file, `LiPositivityBundle.lean` packages the SAME N lower bounds as ONE
list literal `liLowerBounds : List (ℤ × ℕ)` and ONE aggregated hypothesis
`LiBundleHyp` (∀ i < N, lo_i ≤ λ-coefficient i), from which the whole certified
prefix `∀ n < N, 0 ≤ (taylorCoeff riemannXi n).re` follows by a single kernel
`decide` on the list.  This is what makes an N ≈ 10³ ladder consumable: one
hypothesis, not a thousand.  Both faces are regenerated and drift-checked together.

RUNG COUNT.  `N_RUNGS = 20` is the committed default and `--check` pins it; the
count is parameterizable (`--n-rungs N`, env `LI_N_RUNGS`) for throughput
trials.  The working precision scales with N (`prec_bits_for`): the series
route loses about one bit per rung in the F'/F inversion (measured, see
docs/LI_LADDER_COST_MODEL_2026-09-17.md).

HONEST SCOPE: rungs are a finite NECESSARY-condition check; the uniform `∀ n`
IS RH and nothing here approaches it.  Certified prefixes are instrumentation,
not evidence.  The enclosure hypotheses `hlo` / `LiBundleHyp` are the
documented Arb trust seam.  conjecture1_proved = False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_li_positivity import (  # noqa: E402
    LiPositivityLadderEmitter,
    li_positivity_family,
    li_refutation_atom_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.li_coeff import enclose_li_coeffs  # noqa: E402

N_RUNGS = 20
PREC_BITS = 192
_LEAN_DIR = Path(__file__).resolve().parent / "lean"
_OUT = _LEAN_DIR / "LiPositivity.lean"
_BUNDLE_OUT = _LEAN_DIR / "LiPositivityBundle.lean"


def prec_bits_for(n_rungs: int) -> int:
    """Working precision for an N-rung ladder.

    Measured (B1 throughput bench, docs/LI_LADDER_COST_MODEL_2026-09-17.md): the
    minimal precision at which EVERY rung n < N keeps >= 40 relative bits is
    ~ N + 56 bits (N=100: 160, N=200: 256, N=500: 544, N=1000: 1056) — the
    F'/F series inversion loses ~1 bit per rung.  `2N + 128` keeps a margin of
    >= N bits; the committed 20-rung default stays at PREC_BITS = 192.
    """
    return max(PREC_BITS, 2 * n_rungs + 128)


def _round_down_12sig(x: Fraction) -> Fraction:
    """Largest 12-significant-decimal fraction <= x (x > 0). Still a rigorous
    lower bound; keeps the emitted literal short."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**11:
        exp += 1
    num = (x.numerator * 10**exp) // x.denominator  # floor
    return Fraction(num, 10**exp)


def lower_bounds(n_rungs: int = N_RUNGS, prec_bits: int | None = None) -> list[Fraction]:
    """The N certified, 12-significant-decimal-rounded-down lower bounds (enclose + round)."""
    if prec_bits is None:
        prec_bits = prec_bits_for(n_rungs)
    boxes = enclose_li_coeffs(n_rungs, prec_bits=prec_bits)  # self-checked inside
    los = [_round_down_12sig(lo) for lo, _hi in boxes]
    for n, lo in enumerate(los):
        assert lo > 0, f"rung {n}: rounded lower bound not positive"
    return los


def build(n_rungs: int = N_RUNGS, prec_bits: int | None = None, *,
          family: str = "LiPositivity", namespace: str = "LiPositivity",
          los: list[Fraction] | None = None) -> str:
    """The per-rung ladder file (N theorems `li_rung_n` + the refutation atom)."""
    if los is None:
        los = lower_bounds(n_rungs, prec_bits)
    assert len(los) == n_rungs

    fam = li_positivity_family(
        family,
        GridSpec([("n", list(range(n_rungs)))]),
        lambda pt: f"li_rung_{pt['n']}",
        spec=lambda pt: (pt["n"], los[pt["n"]]),
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=(namespace,),
            imports=("Lc.LiCriterion.XiOrderBridge",),
            prelude=(
                "open LiCriterion\n\n"
                + li_refutation_atom_lean()
            ),
        ),
        [LiPositivityLadderEmitter()],
        ValidationReport(checks=(("li_positivity", True),)),
    )
    return next(iter(report.files.values()))


def build_bundle(n_rungs: int = N_RUNGS, prec_bits: int | None = None, *,
                 namespace: str = "LiPositivity", ladder_import: str = "LiLadder",
                 tail_lemma: str = "li_rh_iff_tail",
                 los: list[Fraction] | None = None) -> str:
    """The bundle face: the same N lower bounds as ONE list literal + ONE hypothesis.

    `ladder_import` must supply `li_rh_iff_tail` (LiLadder for the committed
    ladder; a trial passes its own hand-off).  The prefix theorem
    `li_prefix_of_bundle` is exactly the `hpre` that `li_rh_iff_tail` consumes,
    so the reduction of RH to its tail is stated ONCE from ONE hypothesis.
    """
    if los is None:
        los = lower_bounds(n_rungs, prec_bits)
    assert len(los) == n_rungs
    rows = ",\n".join(f"    ({lo.numerator}, {lo.denominator})" for lo in los)
    return f"""/- GENERATED by examples/li_positivity/generate.py (bundle face, Route B / B1) — DO NOT EDIT BY HAND.
   Regenerate & verify:  python examples/li_positivity/generate.py --check
   The {n_rungs} certified Li-ladder lower bounds as ONE list literal and ONE aggregated hypothesis
   (the hypothesis-aggregation discipline: an N-rung ladder is consumed through one seam, not N).
   The literals are byte-identical to the `li_rung_i` hypotheses in LiPositivity.lean.
   Trust seam: `LiBundleHyp` (the Arb enclosures) is a HYPOTHESIS, never discharged here.
   Certified prefixes are instrumentation, not evidence.  conjecture1_proved = False.  -/

import {ladder_import}

namespace {namespace}

open LiCriterion

/-- Rung `i ↦ (num, den)`: the certified lower bound `lo_i = num / den` on
    `(taylorCoeff riemannXi i).re` — the SAME literal as the `li_rung_i` hypothesis. -/
def liLowerBounds : List (ℤ × ℕ) :=
  [
{rows}
  ]

/-- The real value of a listed bound. -/
noncomputable def liLo (p : ℤ × ℕ) : ℝ := (p.1 : ℝ) / (p.2 : ℝ)

-- `rfl`/`decide` on an N-element list recurse ~N deep in the elaborator (default maxRecDepth 512
-- fails at N = 500); the kernel check itself is linear in N.  Budget: 8N + 512.
set_option maxRecDepth {8 * n_rungs + 512} in
theorem liLowerBounds_length : liLowerBounds.length = {n_rungs} := by rfl

set_option maxRecDepth {8 * n_rungs + 512} in
/-- Every listed numerator is positive: ONE kernel `decide` for the whole prefix
    (the analogue of the per-rung `by norm_num : (0:ℝ) ≤ lo`). -/
theorem liLowerBounds_pos : liLowerBounds.all (fun p => decide (0 < p.1)) = true := by decide

/-- THE aggregated Arb trust seam: one hypothesis for the whole {n_rungs}-rung prefix.
    `∀ i < N, lo_i ≤ (taylorCoeff riemannXi i).re`. -/
def LiBundleHyp : Prop :=
  ∀ i (h : i < liLowerBounds.length), liLo liLowerBounds[i] ≤ (taylorCoeff riemannXi i).re

/-- The certified prefix from the ONE bundled hypothesis — exactly the `hpre`
    that `li_rh_iff_tail` consumes.  A finite prefix, NOT RH. -/
theorem li_prefix_of_bundle (hlo : LiBundleHyp) :
    ∀ n, n < {n_rungs} → 0 ≤ (taylorCoeff riemannXi n).re := by
  intro n hn
  have hlen : n < liLowerBounds.length := liLowerBounds_length ▸ hn
  refine le_trans ?_ (hlo n hlen)
  have hpos : (0 : ℤ) < (liLowerBounds[n]).1 :=
    of_decide_eq_true (List.all_eq_true.mp liLowerBounds_pos _ (List.getElem_mem hlen))
  unfold liLo
  exact div_nonneg (by exact_mod_cast hpos.le) (Nat.cast_nonneg _)

/-- RH reduced to the tail past the bundled prefix, from ONE hypothesis.
    The tail is still infinite: this proves NEITHER side of RH. -/
theorem li_rh_iff_tail_of_bundle (hlo : LiBundleHyp) :
    RiemannHypothesis ↔ ∀ n, {n_rungs} ≤ n → 0 ≤ (taylorCoeff riemannXi n).re :=
  {tail_lemma} {n_rungs} (li_prefix_of_bundle hlo)

end {namespace}
"""


def _resolve_n_rungs(cli_value: int | None) -> int:
    if cli_value is not None:
        return cli_value
    env = os.environ.get("LI_N_RUNGS")
    return int(env) if env else N_RUNGS


def main(*, check: bool = False, n_rungs: int | None = None, prec_bits: int | None = None,
         trial: int | None = None) -> int:
    if trial is not None:
        # Throughput trial: separate files, separate namespace, NOT wired into the lakefile.
        los = lower_bounds(trial, prec_bits)
        ladder = build(trial, los=los, family=f"LiPositivityTrial_n{trial}", namespace="LiPositivityTrial")
        out = _LEAN_DIR / f"LiPositivityTrial_n{trial}.lean"
        out.write_text(ladder, encoding="utf-8")
        # LiLadder's `li_rh_iff_tail` is stated for any N, so the trial bundle reuses it by full name.
        bundle = build_bundle(trial, los=los, namespace="LiPositivityTrial", ladder_import="LiLadder",
                              tail_lemma="LiPositivity.li_rh_iff_tail")
        bout = _LEAN_DIR / f"LiPositivityTrialBundle_n{trial}.lean"
        bout.write_text(bundle, encoding="utf-8")
        print(f"wrote {out} ({trial} rungs, {len(ladder)} bytes) and {bout} ({len(bundle)} bytes)")
        return 0

    n = _resolve_n_rungs(n_rungs)
    los = lower_bounds(n, prec_bits)
    text = build(n, los=los)
    bundle = build_bundle(n, los=los)
    if check:
        ok = True
        for path, want in ((_OUT, text), (_BUNDLE_OUT, bundle)):
            if not path.exists() or path.read_text(encoding="utf-8") != want:
                print(f"DRIFT: {path.name} does not match regeneration")
                ok = False
        if not ok:
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte; ladder + bundle)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    _BUNDLE_OUT.write_text(bundle, encoding="utf-8")
    print(f"wrote {_OUT} ({n} rungs + refutation atom, {len(text)} bytes)")
    print(f"wrote {_BUNDLE_OUT} (bundle face, {len(bundle)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    ap.add_argument("--n-rungs", type=int, default=None,
                    help=f"rung count (default {N_RUNGS}; env LI_N_RUNGS). Changing it changes the committed output.")
    ap.add_argument("--prec-bits", type=int, default=None,
                    help="working precision in bits (default prec_bits_for(N) = max(192, 2N+128))")
    ap.add_argument("--trial", type=int, default=None, metavar="N",
                    help="write LiPositivityTrial_nN.lean (+ bundle) for a throughput trial; never wired into the lakefile")
    a = ap.parse_args()
    raise SystemExit(main(check=a.check, n_rungs=a.n_rungs, prec_bits=a.prec_bits, trial=a.trial))
