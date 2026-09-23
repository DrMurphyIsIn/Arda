"""Dogfood: regenerate the Li box rungs of this island with the `preordering_multiplier` kind.

    python examples/li_positivity/dogfood_preordering_multiplier.py           # write lean/Probes/...
    python examples/li_positivity/dogfood_preordering_multiplier.py --check   # drift check (no write)

The sites (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 3; SHAPES_AUDIT_D_LI_FACE section 3.1 and
the `li_box_rung` dogfood family of section 3.3), in `lean/LiBoxRungs.lean`:

  * ``re_Q3_nonneg`` / ``re_Q4_nonneg`` / ``re_Q5_nonneg`` (the audit's ``:139-212``; lines 126-199
    of the current file): ``0 <= Re Q_N(z)`` on the disk ``(Re z)^2 + (Im z)^2 <= Re z`` from the
    hand certificates with multipliers ``1``, ``14 s``, ``s^2`` over the generators ``d = Re z -
    |z|^2`` (the disk hypothesis), ``B = (Im z)^2``, ``s = |z|^2``.  The three certificates are
    transcribed VERBATIM (``HAND_CERTIFICATES``; a test pins them against the island file) and
    re-checked exactly by the certifier -- ``*_regen``;
  * the same rungs ``N = 4, 5`` with the certificate FOUND by the emitter's exact LP (multiplier
    candidates ``"auto"``: the constant, then ``s, s^2, s^3``) -- ``*_lp``;
  * ``re_Q1_nonneg`` / ``re_Q2_nonneg`` (the audit's ``:128-137``, the ``M = 1`` MISS rows), found
    by the LP -- ``*_regen``, so all five rungs of ``liPairedSummand_re_nonneg`` are regenerated;
  * ``N = 6``: REFUSED.  The exact grid scan of the disk locates a point where ``Re Q_6 < 0``
    (OBSTRUCTED_AND_LOCATED); the probe states that refutation for the kernel
    (``re_Q6_disk_claim_false``), so the refusal is itself kernel-checked.

The written file is: a banner, the FROZEN emitter output (provenance header, imports, namespace),
then generator-appended blocks -- the kernel-checked ``Q_6`` refutation, and cross-checks applying
each regenerated lemma to the ORIGINAL's statement (and the original to the regenerated one), plus
the island's termwise dispatch re-assembled from the regenerated lemmas alone.  It imports the
module it regenerates from and touches nothing in it; compile it on the island:

    cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_preordering_multiplier.lean

``tests/test_emit_preordering_multiplier.py`` regenerates the file through this module and asserts
byte equality, so the checked-in Lean can never drift from the emitter.

conjecture1_proved = False -- finite real polynomial inequalities on a disk; nothing here bears on
RH (Li's criterion needs ALL rungs, and N = 6 already fails termwise on this disk).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    ComplexFace, PreorderingMultiplierEmitter, PreorderingObstruction, ValidationReport, certify,
    emit, li_box_rung_target, li_disk_generators, obstruction_refutation_lean,
    preordering_multiplier_certificate, preordering_multiplier_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
OUT = _LEAN / "Probes" / "Dogfood_preordering_multiplier.lean"
NAMESPACE = "DogfoodPreorderingMultiplier"

X, Y = sp.symbols("x y")
ALIASES = (sp.Symbol("d"), sp.Symbol("B"), sp.Symbol("s"))

#: The hand certificates of LiBoxRungs.lean, VERBATIM (the right-hand side of each `key`), with
#: the hand multiplier `(kappa, alias, power)`.
HAND_CERTIFICATES = {
    3: ((1, None, 0),
        "15 * B + 4 * d ^ 3 + 12 * d ^ 2 * s + 3 * d ^ 2 + 12 * d * s ^ 2 + 3 * d * s + 9 * d "
        "+ 4 * s ^ 3"),
    4: ((14, "s", 1),
        "433 * B ^ 2 + 112 * B * d ^ 2 * s + 438 * B * d ^ 2 + 224 * B * d * s ^ 2 "
        "+ 408 * B * d * s + 44 * B * d + 112 * B * s ^ 3 + 44 * B * s + 5 * d ^ 4 + 44 * d ^ 3 "
        "+ 20 * d * s ^ 3 + 180 * d * s + 15 * s ^ 4 + 27 * s ^ 2"),
    5: ((1, "s", 2),
        "68 * B ^ 3 + 72 * B ^ 2 * d ^ 2 + 16 * B ^ 2 * d * s ^ 2 + 128 * B ^ 2 * d * s "
        "+ 16 * B ^ 2 * s ^ 3 + 4 * B ^ 2 * s + 4 * B * d ^ 4 + 70 * B * d ^ 2 * s "
        "+ 4 * B * d * s ^ 3 + 11 * B * d * s ^ 2 + 14 * B * d * s + 3 * B * s ^ 2 "
        "+ 2 * d ^ 4 * s + 3 * d ^ 3 * s ^ 2 + 14 * d ^ 3 * s + d ^ 2 * s ^ 2 + 11 * d * s ^ 2 "
        "+ s ^ 5"),
}

#: The island's own `simp only` lists for `(Q_N z).re` (LiBoxRungs.lean, qualified).
_RE_LEMMAS = ("Complex.sub_re", "Complex.mul_re", "Complex.re_ofNat", "Complex.im_ofNat",
              "pow_succ", "pow_zero", "Complex.one_re", "Complex.one_im", "Complex.mul_im")

#: The disk's bounding box, for the exact negative-witness scan.
SCAN_BOX = {"x": (0, 1), "y": ("-1/2", "1/2")}
SCAN_STEPS = 60


def hand_terms(N: int) -> list[tuple[sp.Rational, tuple[int, ...]]]:
    """The verbatim hand certificate of rung `N` as `(coef, alpha)` over `(d, B, s)`."""
    _mult, text = HAND_CERTIFICATES[N]
    loc = {a.name: a for a in ALIASES}
    poly = sp.Poly(sp.sympify(text.replace("^", "**"), locals=loc), *ALIASES)
    return [(sp.Rational(c), tuple(int(e) for e in m)) for m, c in poly.as_dict().items()]


def face(N: int) -> ComplexFace:
    """The island's own real-part step for `(Q_N z).re`: `simp only [Q_N, ...]` then `ring`, the
    lemma lists of LiBoxRungs.lean (qualified); for `Q_1 z = z` the unfolding alone closes it."""
    unfold = (f"LowHeightBox.Q{N}",)
    if N >= 2:
        unfold += _RE_LEMMAS + (("Complex.add_re",) if N >= 3 else ())
    return ComplexFace(var="z", target=f"LowHeightBox.Q{N} z",
                       coords=(("x", "z.re"), ("y", "z.im")), unfold=unfold,
                       simp_closes=(N == 1))


def _spec(N: int, how: str) -> dict:
    spec = dict(target=li_box_rung_target(N, X, Y), generators=li_disk_generators(X, Y),
                face=face(N))
    if how == "hand":
        mult, _text = HAND_CERTIFICATES[N]
        spec.update(multiplier=mult, terms=hand_terms(N))
        if mult[1] is not None:
            spec["locus"] = "auto"
    else:  # "lp": the emitter finds the multiplier and the certificate
        spec.update(multiplier_candidates="auto", max_total_degree=5)
    return spec


#: (lean name, rung, how) in emission order.
INSTANCES = (
    ("re_Q1_nonneg_regen", 1, "lp"),
    ("re_Q2_nonneg_regen", 2, "lp"),
    ("re_Q3_nonneg_regen", 3, "hand"),
    ("re_Q4_nonneg_regen", 4, "hand"),
    ("re_Q5_nonneg_regen", 5, "hand"),
    ("re_Q4_nonneg_lp", 4, "lp"),
    ("re_Q5_nonneg_lp", 5, "lp"),
)


def family():
    return preordering_multiplier_family(
        "DogfoodPreorderingMultiplier", (X, Y),
        GridSpec([("i", list(range(len(INSTANCES))))]),
        lambda pt: INSTANCES[pt["i"]][0],
        spec=lambda pt: _spec(INSTANCES[pt["i"]][1], INSTANCES[pt["i"]][2]),
    )


def q6_obstruction() -> PreorderingObstruction:
    """The N = 6 refusal: the claim is located FALSE on the disk (never certified)."""
    try:
        preordering_multiplier_certificate(
            symbols=(X, Y), target=li_box_rung_target(6, X, Y),
            generators=li_disk_generators(X, Y), multiplier_candidates="auto",
            max_total_degree=5, scan_box=SCAN_BOX, scan_steps=SCAN_STEPS)
    except PreorderingObstruction as obs:
        return obs
    raise AssertionError("Re Q_6 was not refused as OBSTRUCTED_AND_LOCATED")  # pragma: no cover


BANNER = """/-
  Dogfood_preordering_multiplier -- the Telperion `preordering_multiplier` kind
  (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 3; SHAPES_AUDIT_D_LI_FACE section 3.1, with the
  `li_box_rung` dogfood family of section 3.3) regenerating the Li box rungs of LiBoxRungs.lean:

    re_Q3/Q4/Q5_nonneg_regen   the three hand certificates (multipliers 1, 14 s, s^2 over the
                               generators d = Re z - |z|^2, B = (Im z)^2, s = |z|^2), transcribed
                               verbatim and re-checked exactly by the certifier;
    re_Q4/Q5_nonneg_lp         the same rungs with the certificate FOUND by the emitter's exact
                               LP (multiplier candidates: the constant, then s, s^2, s^3);
    re_Q1/Q2_nonneg_regen      the two M = 1 rungs (the audit's MISS rows), LP-found;
    re_Q6_disk_claim_false     the N = 6 REFUSAL made kernel-checkable: the exact grid scan of the
                               disk located a point where Re Q_6 < 0 (OBSTRUCTED_AND_LOCATED).

  Each regenerated lemma is a real-variable core `<name>_real` (x = Re z, y = Im z) plus a thin
  complex face `<name>` stating the island's form `0 <= (LowHeightBox.Q<N> z).re`.  The block
  between the telperion provenance header and `end DogfoodPreorderingMultiplier` is the FROZEN
  emitter output (examples/li_positivity/dogfood_preordering_multiplier.py regenerates it; a test
  pins the bytes).  The blocks after it are generator-appended: the Q_6 refutation, then
  cross-checks applying each regenerated lemma to the ORIGINAL's statement, and the island's
  termwise dispatch `liPairedSummand_re_nonneg` re-assembled from the regenerated lemmas alone.
  Nothing in LiBoxRungs is modified.

  Run: cd telperion/examples/li_positivity/lean && lake env lean Probes/Dogfood_preordering_multiplier.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite real
  polynomial inequality on the disk (Re z)^2 + (Im z)^2 <= Re z, and N = 6 already fails there.
-/
"""


def _refutation_block() -> str:
    obs = q6_obstruction()
    w = obs.witness
    return (
        "\n/-! ## The N = 6 refusal, kernel-checked (generator-appended).\n"
        f"    `preordering_multiplier` REFUSED `0 <= Re Q_6` on the disk as OBSTRUCTED_AND_LOCATED:\n"
        f"    the exact grid scan ({SCAN_STEPS} steps per axis of [0, 1] x [-1/2, 1/2]) found\n"
        f"    Re Q_6 = {obs.value} < 0 at (x, y) = ({w['x']}, {w['y']}), a point of the disk.  No\n"
        "    certificate was emitted; the theorem below confirms in the kernel that the refused\n"
        "    claim is FALSE, so the refusal is a located obstruction and not a give-up. -/\n\n"
        f"namespace {NAMESPACE}\n\n"
        + obstruction_refutation_lean(obs, "re_Q6_disk_claim_false")
        + f"\nend {NAMESPACE}\n"
    )


TRAILER = """
/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block
    above the refutation is the frozen emitter output).  Each `example` is closed by applying one
    side to the other's statement, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodPreorderingMultiplier

/-- The regenerated rungs prove the ORIGINAL `LowHeightBox.re_Q<N>_nonneg` statements ... -/
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q1 z).re :=
  re_Q1_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q2 z).re :=
  re_Q2_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q3 z).re :=
  re_Q3_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  re_Q4_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  re_Q5_nonneg_regen hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  re_Q4_nonneg_lp hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  re_Q5_nonneg_lp hz

/-- ... and the originals prove the regenerated statements: the two are interchangeable. -/
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q3 z).re :=
  LowHeightBox.re_Q3_nonneg hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q4 z).re :=
  LowHeightBox.re_Q4_nonneg hz
example {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (LowHeightBox.Q5 z).re :=
  LowHeightBox.re_Q5_nonneg hz

/-- The island's termwise dispatch (`LowHeightBox.liPairedSummand_re_nonneg`) re-assembled from the
    regenerated lemmas alone: they are drop-in replacements for the hand proofs. -/
example (n : ℕ) (hn : n ≤ 4) (ρ : LiCriterion.NontrivialZero) :
    0 ≤ (LiCriterion.liPairedSummand n ρ).re := by
  have hz := LowHeightBox.zOf_mem_disk ρ
  interval_cases n
  · rw [LowHeightBox.liPairedSummand_zero_eq]; exact re_Q1_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_one_eq]; exact re_Q2_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_two_eq]; exact re_Q3_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_three_eq]; exact re_Q4_nonneg_regen hz
  · rw [LowHeightBox.liPairedSummand_four_eq]; exact re_Q5_nonneg_regen hz

end CrossChecks

"""


def _axioms_block() -> str:
    names = []
    for nm, _N, _how in INSTANCES:
        names += [f"{nm}_real", nm]
    names.append("re_Q6_disk_claim_false")
    return "".join(f"#print axioms {NAMESPACE}.{nm}\n" for nm in names)


def emitted_text() -> str:
    """The frozen emitter output alone (header + imports + namespace + theorems)."""
    report = emit(
        certify(family()),
        LeanProfile(namespace=(NAMESPACE,), imports=("LiBoxRungs",)),
        [PreorderingMultiplierEmitter()],
        ValidationReport(checks=(("preordering_multiplier", True),)),
        file_name="Dogfood_preordering_multiplier.lean",
    )
    return report.files["Dogfood_preordering_multiplier.lean"]


def build_text() -> str:
    """The complete probe file: banner + frozen emitter output + the Q_6 refutation +
    kernel cross-checks + axiom prints."""
    return BANNER + emitted_text() + _refutation_block() + TRAILER + _axioms_block()


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="drift check against the file on disk")
    args = ap.parse_args(argv)
    text = build_text()
    if args.check:
        if not OUT.is_file():
            print(f"MISSING {OUT}")
            return 1
        if OUT.read_text(encoding="utf-8") != text:
            print(f"DRIFT {OUT}: regenerate with {Path(__file__).name}")
            return 1
        print(f"OK {OUT} matches the emitter")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
