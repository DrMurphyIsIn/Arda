"""Dogfood: regenerate hand-proof sites with the `enclosure_tree` kind.

    python examples/li_positivity/dogfood_enclosure_tree.py           # write both probe files
    python examples/li_positivity/dogfood_enclosure_tree.py --check   # drift check (no write)

The sites (SHAPES_AUDIT_48H_2026-09-22.md section 7, sprint 1 item 1; D 2.4 / D 4, A N2 / N3):

  * ``LiLadderHeight.lean`` ``li_rungs_of_bands_4000_upto`` -- the pi-face rate step
    ``n <= 18848 -> (n + 1 : R) <= 3 * pi * 4000 / 2`` by ``Real.pi_gt_d4`` (the audit's
    ``:602-609``; the file shrank when the shared ``LiFacePrelude`` pack landed, the lemma is now
    at the end of section 4), regenerated as ``li_height_rate_4000`` + ``_rate``;
  * ``LiLadderSharp.lean`` ``li_rungs_of_bands_4000_upto_sharp`` -- ``n <= 25128 -> (n + 1 : R)
    <= 2 * pi * (4000 - 1/2)`` by ``Real.pi_gt_d6`` (the audit's ``:154-161``), regenerated as
    ``li_sharp_rate_4000`` + ``_rate``.  The ladder search lands on d4 and d6 by itself;
  * ``quasicrystal/lean/LeakageDictionary.lean:276-359`` -- the nine bracket lemmas
    (``sqrt_five_bounds``, ``sqrt_inner_bounds``, ``dhKappa_gt``/``_lt``/``_bounds``,
    ``log_three_halves_bounds``, ``log_six_bounds``, ``log_two_bounds``, ``log_three_bounds``) as
    seven emitted theorems (the three ``dhKappa`` lemmas are one two-sided enclosure).

Two files are written:

  * ``li_positivity/lean/Probes/Dogfood_enclosure_tree.lean`` (this island; COMPILED): the pi-face
    rates with kernel cross-checks that feed each emitted rate lemma to the hand theorem whose side
    condition it replaces; the nine leakage brackets regenerated on Mathlib alone (the quasicrystal
    island is v4.32.0 and not importable here); and a route-coverage section exercising every
    tactic skeleton the two sites do not (exp, both arctan routes, McCormick products, powers,
    negation, a Taylor log at 1/2, the order-level search, a shared-root alias, a named linear
    node, the B C2 / C 2.10 ``sqrt (2 pi)`` and ``pi^2/6`` numerics, the C 4.7 log/sqrt face);
  * ``quasicrystal/lean/Probes/Dogfood_enclosure_tree.lean`` (that island; the lead compiles it):
    the nine brackets under new names with cross-checks BOTH ways against ``Quasicrystal.*``.

Each file is a banner, the FROZEN emitter output (provenance header, imports, namespace), then the
generator-appended cross-checks and ``#print axioms`` lines.  ``tests/test_emit_enclosure_tree.py``
regenerates both through this module and asserts byte equality.

    cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
    cd telperion/examples/quasicrystal/lean && lake env lean Probes/Dogfood_enclosure_tree.lean

conjecture1_proved = False -- finite rational arithmetic facts about real constants and one
elementary inequality; nothing here bears on RH.
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as R
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    EnclosureTreeEmitter, ValidationReport, certify, emit, enclosure_tree_family,
)
from telperion.emit_enclosure_tree import (  # noqa: E402
    node_add, node_arctan, node_div, node_exp, node_log, node_mul, node_neg, node_pi,
    node_pow, node_rat, node_sqrt, node_sub,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_EXAMPLES = Path(__file__).resolve().parents[1]
OUT_LI = _EXAMPLES / "li_positivity" / "lean" / "Probes" / "Dogfood_enclosure_tree.lean"
OUT_QC = _EXAMPLES / "quasicrystal" / "lean" / "Probes" / "Dogfood_enclosure_tree.lean"


# --- the instances ------------------------------------------------------------------

def li_specs() -> dict:
    """The two pi-face rate corollaries, exactly as the hand proofs shape them."""
    return {
        # LiLadderHeight.li_rungs_of_bands_4000_upto: (n + 1 : R) <= 3 * pi * 4000 / 2, n <= 18848
        "li_height_rate_4000": dict(
            tree=node_div(node_mul(node_mul(node_rat(3), node_pi()), node_rat(4000)),
                          node_rat(2)),
            rate_cap=18848),
        # LiLadderSharp.li_rungs_of_bands_4000_upto_sharp: ... <= 2 * pi * (4000 - 1/2), n <= 25128
        "li_sharp_rate_4000": dict(
            tree=node_mul(node_mul(node_rat(2), node_pi()),
                          node_sub(node_rat(4000), node_rat(R(1, 2)))),
            rate_cap=25128),
    }


def qc_specs(prefix: str = "qc_") -> dict:
    """LeakageDictionary.lean:276-359, the nine bracket lemmas, with the ORIGINAL claims.  The
    shared atoms are built once and consumed by name (`sqrt 5` by the inner radical and the DH
    quotient; `log 2` and `log (3/2)` by both folds), exactly as the hand proofs chain them."""
    s5 = node_sqrt(node_rat(5), lo=R(1118033988749, 500000000000),
                   hi=R(2236067977501, 1000000000000), strict=True,
                   name=f"{prefix}sqrt_five_bounds")
    inner = node_sqrt(node_sub(node_rat(10), node_mul(node_rat(2), s5)),
                      lo=R(1175570504583, 500000000000), hi=R(2351141009173, 1000000000000),
                      strict=True, name=f"{prefix}sqrt_inner_bounds")
    kappa = node_div(node_sub(inner, node_rat(2)), node_sub(s5, node_rat(1)))
    l32 = node_log(R(3, 2), order=24, lo=R(6070423640075591, 14971509072199680),
                   hi=R(6070425424818551, 14971509072199680), strict=False,
                   name=f"{prefix}log_three_halves_bounds")
    l2 = node_log(2, lo=R(6931471803, 10 ** 10), hi=R(6931471808, 10 ** 10), strict=True,
                  name=f"{prefix}log_two_bounds")
    l6 = node_log(6, factors=[(2, l2), (1, l32)],
                  lo=R(52393246555737784416259, 29241228656640000000000),
                  hi=R(52393250070805106822899, 29241228656640000000000), strict=True)
    l3 = node_log(3, factors=[(1, l2), (1, l32)],
                  lo=R(32124771363880211544067, 29241228656640000000000),
                  hi=R(32124774864326919622387, 29241228656640000000000), strict=True)
    return {
        f"{prefix}sqrt_five_bounds": dict(tree=s5),
        f"{prefix}sqrt_inner_bounds": dict(tree=inner),
        f"{prefix}dhKappa_bounds": dict(tree=kappa, lo=R(284079041, 10 ** 9),
                                        hi=R(142039523, 500000000), strict=True),
        f"{prefix}log_three_halves_bounds": dict(tree=l32),
        f"{prefix}log_six_bounds": dict(tree=l6),
        f"{prefix}log_two_bounds": dict(tree=l2),
        f"{prefix}log_three_bounds": dict(tree=l3),
    }


def route_specs() -> dict:
    """Route coverage: every tactic skeleton the two sites do not exercise, kernel-checked."""
    pi = node_pi()
    s5 = node_sqrt(node_rat(5))
    return {
        # B C2 (E6Bridge11:1097-1099) / C 2.10 (E6Bridge16:348-350): sqrt (2 pi) <= 2.51
        "rt_sqrt_two_pi": dict(tree=node_sqrt(node_mul(node_rat(2), pi)), hi=R(251, 100)),
        # B C2: sqrt (32 pi) <= 11, a bracketed (non-rational) radicand
        "rt_sqrt_thirty_two_pi": dict(tree=node_sqrt(node_mul(node_rat(32), pi)), hi=11),
        # C 2.10 (E6Bridge16:770-772): sqrt 2 <= 1.5
        "rt_sqrt_two": dict(tree=node_sqrt(node_rat(2)), hi=R(3, 2)),
        # C 2.10 (E6Bridge16:467): pi^2 / 6 <= 2, a power then a constant quotient
        "rt_pi_sq_div_six": dict(tree=node_div(node_pow(pi, 2), node_rat(6)), hi=2),
        # C 2.10 (E6Bridge16:681-685): 1.648 <= e^(1/2)
        "rt_exp_half": dict(tree=node_exp(R(1, 2)), lo=R(1648, 1000)),
        # exp at a negative point
        "rt_exp_neg_one": dict(tree=node_exp(-1), lo=R(36, 100), hi=R(37, 100)),
        # D 4 arctan faces: the half route (t/2 <= arctan t <= t on [0, 1]) and the abs route
        "rt_arctan_half": dict(tree=node_arctan(node_rat(R(1, 2)))),
        "rt_arctan_abs": dict(tree=node_arctan(node_sub(pi, node_rat(R(7, 2))))),
        # a product of two non-constants: the four McCormick corner facts
        "rt_sqrt5_mul_log2": dict(tree=node_mul(s5, node_log(2))),
        # negation, and an open endpoint carried through it (4 - pi > 0 strictly)
        "rt_four_sub_pi": dict(tree=node_add(node_neg(pi), node_rat(4)), lo=0),
        # a Taylor log at an argument with numerator 1 (the `generalize` hardening)
        "rt_log_half": dict(tree=node_log(R(1, 2))),
        # the order-level search: order-24 atoms cannot carry this root claim, level 32 can
        "rt_log_two_split": dict(tree=node_add(node_log(R(3, 2)), node_log(R(4, 3))),
                                 lo=R(693147180, 10 ** 9), hi=R(693147181, 10 ** 9)),
        # the same tree as rt_sqrt_two under another name: a shared-root alias
        "rt_sqrt_two_alias": dict(tree=node_sqrt(node_rat(2)), hi=R(3, 2)),
        # a named LINEAR node emits its own theorem; strictness mixes per side
        "rt_named_radicand_plus_exp": dict(tree=node_add(
            node_sub(node_rat(10), node_mul(node_rat(2), s5), name="rt_radicand"),
            node_exp(R(1, 10)))),
        # a general quotient, both sides non-strict
        "rt_pi_div_golden": dict(tree=node_div(pi, node_add(s5, node_rat(1))), strict=False),
        # the half arctan route on a fused argument
        "rt_arctan_pi_sub_three": dict(tree=node_arctan(node_sub(pi, node_rat(3)))),
        # C 4.7: E6Bridge23 log_add_four_le (k = 3, c = 6) and E6Bridge16's log n <= 2 sqrt n
        "rt_log_add_four_le": dict(face="log_sqrt", shift=4, floor=1),
        "rt_log_le_two_sqrt": dict(face="log_sqrt", floor=2),
    }


# --- the files -------------------------------------------------------------------------

BANNER_LI = """/-
  Dogfood_enclosure_tree -- the Telperion `enclosure_tree` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 1; A N2/N3/N4, B C2, C 4.7, D 4) regenerating hand-proof sites, 2026-09-22:

    LiLadderHeight.lean   `li_rungs_of_bands_4000_upto`: n <= 18848 -> (n + 1 : R) <= 3 pi 4000 / 2
                          by Real.pi_gt_d4 (`li_height_rate_4000`, `_rate`);
    LiLadderSharp.lean    `li_rungs_of_bands_4000_upto_sharp`: n <= 25128 -> (n + 1 : R) <=
                          2 pi (4000 - 1/2) by Real.pi_gt_d6 (`li_sharp_rate_4000`, `_rate`);
    quasicrystal LeakageDictionary.lean:276-359, the nine bracket lemmas (`qc_*`), regenerated on
                          Mathlib alone -- that island (v4.32.0) is not importable here; its own
                          probe, quasicrystal/lean/Probes/Dogfood_enclosure_tree.lean, carries the
                          cross-checks against the originals;
    route coverage (`rt_*`): every tactic skeleton the sites above do not exercise.

  The block between the telperion provenance header and `end DogfoodEnclosureTree` is the FROZEN
  emitter output (examples/li_positivity/dogfood_enclosure_tree.py regenerates it; a test pins the
  bytes).  The cross-checks after it feed each emitted rate lemma to the hand theorem whose side
  condition it replaces, so the kernel confirms the regeneration is interchangeable with the hand
  `pi_gt_dN` step.  Nothing in LiLadderHeight / LiLadderSharp is modified.

  Run: cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite rational
  arithmetic fact about real constants (or one elementary real inequality); the cross-checks
  compose with CONDITIONAL hand theorems and inherit their hypotheses unchanged.
-/
"""

_HALL = "(hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2)"

TRAILER_LI_HEAD = f"""
/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block above
    is the frozen emitter output).  Each `example` feeds an emitted rate lemma to the hand theorem
    whose side condition it replaces, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodEnclosureTree

/-- `LiLadderHeight.li_rungs_of_bands_4000_upto`, with its hand `Real.pi_gt_d4` + `linarith` step
    replaced by the emitted `li_height_rate_4000_rate`.  Conditional on `hall`, exactly as the
    original; proves nothing about RH. -/
example {_HALL} :
    ∀ n : ℕ, n ≤ 18848 → 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re :=
  fun n hn => LiLadderHeight.li_rungs_of_bands_4000 hall n (li_height_rate_4000_rate n hn)

/-- `LiLadderHeight.li_rungs_of_bands_4000_upto_sharp` (LiLadderSharp), with its hand
    `Real.pi_gt_d6` + `nlinarith` step replaced by the emitted `li_sharp_rate_4000_rate`. -/
example {_HALL} :
    ∀ n : ℕ, n ≤ 25128 → 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re :=
  fun n hn => LiLadderHeight.li_rungs_of_bands_4000_sharp hall n (li_sharp_rate_4000_rate n hn)

end CrossChecks
"""

BANNER_QC = """/-
  Dogfood_enclosure_tree -- the Telperion `enclosure_tree` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 1; A N2 / N3) regenerating LeakageDictionary.lean:276-359, 2026-09-22: the nine
  bracket lemmas `sqrt_five_bounds`, `sqrt_inner_bounds`, `dhKappa_gt`, `dhKappa_lt`,
  `dhKappa_bounds`, `log_three_halves_bounds`, `log_six_bounds`, `log_two_bounds`,
  `log_three_bounds`, as seven emitted theorems under NEW names (`qc_*`; the three `dhKappa`
  lemmas are one two-sided enclosure of the unfolded constant).  The emitted theorems chain like
  the hand proofs: `sqrt 5` is consumed by name by the inner radical and the DH quotient, `log 2`
  and `log (3/2)` by both folds.

  The block between the telperion provenance header and `end DogfoodEnclosureTreeQC` is the FROZEN
  emitter output (examples/li_positivity/dogfood_enclosure_tree.py regenerates it; a test pins the
  bytes).  The cross-checks after it prove every ORIGINAL statement from the regenerated theorems
  and every regenerated statement from the originals.  Nothing in LeakageDictionary is modified.

  Run: cd telperion/examples/quasicrystal/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].
  (The same seven theorems are compiled on the li_positivity island's Mathlib as the `qc_*`
  section of li_positivity/lean/Probes/Dogfood_enclosure_tree.lean.)

  conjecture1_proved = False.  Nothing here bears on RH: finite rational arithmetic facts about
  sqrt 5, the Davenport-Heilbronn constant and log 2, log 3, log 6, log (3/2).
-/
"""

#: The ORIGINAL LeakageDictionary statements, verbatim (the test re-reads the island source and
#: asserts each one appears there), and whether the regenerated statement is literally the same.
QC_ORIGINALS = (
    ("sqrt_five_bounds", "qc_sqrt_five_bounds", None,
     "(1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧ "
     "Real.sqrt 5 < (2236067977501 / 1000000000000 : ℝ)"),
    ("sqrt_inner_bounds", "qc_sqrt_inner_bounds", None,
     "(1175570504583 / 500000000000 : ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) ∧\n"
     "    Real.sqrt (10 - 2 * Real.sqrt 5) < (2351141009173 / 1000000000000 : ℝ)"),
    ("dhKappa_gt", "qc_dhKappa_bounds", ".1", "(284079041 / 1000000000 : ℝ) < dhKappa"),
    ("dhKappa_lt", "qc_dhKappa_bounds", ".2", "dhKappa < (142039523 / 500000000 : ℝ)"),
    ("dhKappa_bounds", "qc_dhKappa_bounds", None,
     "(284079041 / 1000000000 : ℝ) < dhKappa ∧ dhKappa < (142039523 / 500000000 : ℝ)"),
    ("log_three_halves_bounds", "qc_log_three_halves_bounds", None,
     "(6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧ "
     "Real.log (3 / 2) ≤ (6070425424818551 / 14971509072199680 : ℝ)"),
    ("log_six_bounds", "qc_log_six_bounds", None,
     "(52393246555737784416259 / 29241228656640000000000 : ℝ) < Real.log 6 ∧ "
     "Real.log 6 < (52393250070805106822899 / 29241228656640000000000 : ℝ)"),
    ("log_two_bounds", "qc_log_two_bounds", None,
     "(6931471803 / 10000000000 : ℝ) < Real.log 2 ∧\n"
     "    Real.log 2 < (6931471808 / 10000000000 : ℝ)"),
    ("log_three_bounds", "qc_log_three_bounds", None,
     "(32124771363880211544067 / 29241228656640000000000 : ℝ) < Real.log 3 ∧\n"
     "    Real.log 3 < (32124774864326919622387 / 29241228656640000000000 : ℝ)"),
)


def _qc_statement_in_ns(stmt: str) -> str:
    """An original statement as written INSIDE `namespace Quasicrystal`, qualified for use
    outside it (only `dhKappa` is a local name)."""
    return stmt.replace("dhKappa", "Quasicrystal.dhKappa")


def trailer_qc() -> str:
    lines = [
        "",
        "/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the "
        "block above",
        "    is the frozen emitter output).  Regenerated => original: every one of the nine "
        "ORIGINAL",
        "    statements is proved from the emitted theorems (`dhKappa` unfolded; `linarith` "
        "absorbs the",
        "    one literal the emitter writes in lowest terms, `6931471808 / 10000000000 = "
        "108304247 / 156250000`).",
        "    Original => regenerated: every emitted statement is proved from the originals. -/",
        "",
        "section CrossChecks",
        "open DogfoodEnclosureTreeQC",
        "",
    ]
    for orig, regen, proj, stmt in QC_ORIGINALS:
        s = _qc_statement_in_ns(stmt)
        unfold = "  unfold Quasicrystal.dhKappa\n" if "dhKappa" in stmt else ""
        if proj is None:
            body = (f"  have h := {regen}\n{unfold}"
                    "  exact ⟨by linarith [h.1], by linarith [h.2]⟩\n")
        else:
            body = f"  have h := ({regen}){proj}\n{unfold}  linarith\n"
        lines.append(f"/-- regenerated `{regen}` => original `Quasicrystal.{orig}`. -/")
        lines.append(f"example :\n    {s} := by\n{body}")
    lines.append("/-- original => regenerated, for each of the seven emitted statements. -/")
    back = (
        ("qc_sqrt_five_bounds", "Quasicrystal.sqrt_five_bounds", False),
        ("qc_sqrt_inner_bounds", "Quasicrystal.sqrt_inner_bounds", False),
        ("qc_dhKappa_bounds", "Quasicrystal.dhKappa_bounds", True),
        ("qc_log_three_halves_bounds", "Quasicrystal.log_three_halves_bounds", False),
        ("qc_log_six_bounds", "Quasicrystal.log_six_bounds", False),
        ("qc_log_two_bounds", "Quasicrystal.log_two_bounds", False),
        ("qc_log_three_bounds", "Quasicrystal.log_three_bounds", False),
    )
    for regen, orig, unfold in back:
        u = f"  unfold Quasicrystal.dhKappa at h\n" if unfold else ""
        lines.append(f"example : type_of% {regen} := by\n  have h := {orig}\n{u}"
                     "  exact ⟨by linarith [h.1], by linarith [h.2]⟩\n")
    lines.append("end CrossChecks")
    lines.append("")
    return "\n".join(lines)


def _family(name: str, specs: dict):
    keys = list(specs)
    return enclosure_tree_family(name, GridSpec([("i", list(range(len(keys))))]),
                                 lambda pt: keys[pt["i"]], spec=lambda pt: specs[keys[pt["i"]]])


def _emitted(name: str, specs: dict, imports: tuple, file_name: str) -> str:
    report = emit(
        certify(_family(name, specs)),
        LeanProfile(namespace=(name,), imports=imports),
        [EnclosureTreeEmitter()],
        ValidationReport(checks=(("enclosure_tree", True),)),
        file_name=file_name,
    )
    return report.files[file_name]


def _axioms(ns: str, text: str) -> str:
    names = [ln.split()[1] for ln in text.splitlines() if ln.startswith("theorem ")]
    return "".join(f"#print axioms {ns}.{nm}\n" for nm in names)


def emitted_li() -> str:
    specs = {**li_specs(), **qc_specs(), **route_specs()}
    return _emitted("DogfoodEnclosureTree", specs, ("LiLadderHeight", "LiLadderSharp"),
                    "Dogfood_enclosure_tree.lean")


def emitted_qc() -> str:
    return _emitted("DogfoodEnclosureTreeQC", qc_specs(), ("LeakageDictionary",),
                    "Dogfood_enclosure_tree.lean")


def build_li() -> str:
    body = emitted_li()
    return BANNER_LI + body + TRAILER_LI_HEAD + "\n" + _axioms("DogfoodEnclosureTree", body)


def build_qc() -> str:
    body = emitted_qc()
    return BANNER_QC + body + trailer_qc() + "\n" + _axioms("DogfoodEnclosureTreeQC", body)


def outputs() -> dict:
    return {OUT_LI: build_li(), OUT_QC: build_qc()}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="drift check against the files on disk")
    args = ap.parse_args(argv)
    status = 0
    for out, text in outputs().items():
        if args.check:
            if not out.is_file():
                print(f"MISSING {out}")
                status = 1
            elif out.read_text(encoding="utf-8") != text:
                print(f"DRIFT {out}: regenerate with {Path(__file__).name}")
                status = 1
            else:
                print(f"OK {out} matches the emitter")
            continue
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
        print(f"wrote {out}")
    return status


if __name__ == "__main__":
    sys.exit(main())
