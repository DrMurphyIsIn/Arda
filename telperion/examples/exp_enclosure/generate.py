"""Generate the exp-enclosure example: certify -> emit -> write INTO the zeta island.

    python examples/exp_enclosure/generate.py           # write the island lib
    python examples/exp_enclosure/generate.py --check   # drift check (no write)

WHAT THIS DOGFOODS
------------------
Four certified rational enclosures, all from Mathlib's `Real.exp_bound`, each one the exact
numeric seam some MIRRORMERE artifact currently carries as an Arb hypothesis or an ad-hoc
local bracket:

  (i)   `exp_tenth_bracket`      -- `expLo <= e^(1/10) <= expHi` with BraggDefect's OWN 40-digit
        literals, READ VERBATIM out of `BraggDefect.lean` at generation time (so a drift in the
        driver that produced those literals breaks `--check` here, not silently downstream).
        This discharges the `hexp` hypothesis of `BraggDefect.bragg_defect_witness`, and the
        hand-written bridge below states the MIRRORMERE node's witness UNCONDITIONALLY.
  (ii)  `deficit_tenth_bracket`  -- `e^(1/10) + e^(-1/10) - 2` bracketed by BraggDefect's own
        `excess_bracket` constants (QC_RECURRENCE row a; the numeric twin of
        MM_recurrence_deficit_eq_excess).
  (iii) `deficit_fifth_bracket`  -- the same deficit at `d = 1/5`, `defect_eq_two`'s second
        synthetic channel.
  (iv)  `cosh_zoodh_bracket`     -- `cosh (21487557/100000000)` with ZooDH's own order-6
        bracket constants, read verbatim out of `ZooDH.lean`.

The lib is emitted INTO the `zeta_zero_localization` island (as `BraggAmplitudeInstances` is),
because the bridge imports `BraggDefect`; the `exp-enclosure-compiles` CI job builds it in
`zzl_aux`.

conjecture1_proved = False -- rational enclosures of transcendental constants at four rational
points, plus one hypothesis discharge.  Nothing about RH.
"""
import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import (  # noqa: E402
    ExpEnclosureEmitter, ValidationReport, certify, emit,
)
from telperion.emit_exp_enclosure import exp_enclosure_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_ISLAND = Path(__file__).resolve().parents[1] / "zeta_zero_localization" / "lean"
_OUT = _ISLAND / "ExpEnclosureInstances.lean"
_BRAGG_DEFECT = _ISLAND / "BraggDefect.lean"
_ZOODH = _ISLAND / "ZooDH.lean"

# --- literals that MUST match the island sources verbatim (asserted at generate time) ------

# BraggDefect.lean:68-69 -- the Arb enclosure of e^(1/10) carried by `hexp`.
_EXP_LO = sp.Rational(442068367230259049924676660787771898883,
                      400000000000000000000000000000000000000)
_EXP_HI = sp.Rational(11051709180756476248117094953514706601127,
                      10000000000000000000000000000000000000000)
# BraggDefect.excess_bracket -- the bracket of excess = e^(1/10) + e^(-1/10) - 2.
_D_LO = sp.Rational(
    44243688035498337190547890814412959087189025996450853896963629856431657841141,
    4420683672302590499246837981405882640450800000000000000000000000000000000000000)
_D_HI = sp.Rational(
    44243688035498337190690637870740262328789025996450853896963629856431657841141,
    4420683672302590499246766607877718988830000000000000000000000000000000000000000)
# ZooDH.lean -- the order-6 cosh bracket used by the off-line DH diffraction term at u2.
_COSH_X = sp.Rational(21487557, 100000000)
_COSH_LO = sp.Rational(511587210574920885840517, 500000000000000000000000)
_COSH_HI = sp.Rational(511587370066054060481853, 500000000000000000000000)
# defect_eq_two's second channel d = 1/5 (no island constants exist for it; these are the
# generator's own claim, a plain 21-decimal bracket that the Taylor box must imply).
_D5_LO = sp.Rational(40133511238151692591, 10 ** 21)
_D5_HI = sp.Rational(401335112381516925911, 10 ** 22)

# The off-line bracket constants of `BraggDefect.bragg_defect_witness` are NOT pinned here as
# hand-typed numerals (a truncated pin would still substring-match the source); they are
# EXTRACTED from BraggDefect.lean at generate time by `_island_offline_bracket()` below and
# rendered into the bridge, so the bridge cannot drift from the island statement it applies.

_CASES = {
    0: ("exp_tenth_bracket", {"x": sp.Rational(1, 10), "lo": _EXP_LO, "hi": _EXP_HI,
                              "mode": "exp"}),
    1: ("deficit_tenth_bracket", {"x": sp.Rational(1, 10), "lo": _D_LO, "hi": _D_HI,
                                  "mode": "deficit"}),
    2: ("deficit_fifth_bracket", {"x": sp.Rational(1, 5), "lo": _D5_LO, "hi": _D5_HI,
                                  "mode": "deficit"}),
    3: ("cosh_zoodh_bracket", {"x": _COSH_X, "lo": _COSH_LO, "hi": _COSH_HI,
                               "mode": "cosh"}),
}


def _one_rational(src: str, pattern: str, what: str) -> sp.Rational:
    """Extract exactly one `<digits> / <digits>` literal matched by `pattern` from `src`."""
    hits = re.findall(pattern, src)
    if len(hits) != 1:
        raise SystemExit(f"DRIFT: expected exactly one {what} literal, found {len(hits)}")
    p, q = hits[0]
    return sp.Rational(int(p), int(q))


def _island_offline_bracket() -> tuple[str, str]:
    """The two off-line defect constants, read VERBATIM out of `bragg_defect_witness`.

    Returned as source text (not parsed rationals) so the bridge reproduces the island
    statement numeral-for-numeral; a drift in BraggDefect.lean changes these bytes and the
    `--check` gate fires here rather than at CI build time."""
    bd = _BRAGG_DEFECT.read_text(encoding="utf-8")
    start = bd.index("theorem bragg_defect_witness")
    body = bd[start:bd.index("defect_leakage_gap", start)]
    hits = re.findall(r"\(-(\d+) / (\d+) : ℝ\)", body)
    if len(hits) != 2:
        raise SystemExit(
            f"DRIFT: bragg_defect_witness no longer carries exactly two negative rational "
            f"literals (found {len(hits)})")
    return tuple(f"-{p} / {q}" for p, q in hits)  # type: ignore[return-value]


def _assert_island_literals() -> None:
    """The instances quote island literals; pin them EXACTLY so driver drift breaks --check
    HERE.  Every comparison is on the parsed rational (not a substring), so a truncated or
    extended numeral cannot slip through."""
    bd = _BRAGG_DEFECT.read_text(encoding="utf-8")
    for name, q in (("expLo", _EXP_LO), ("expHi", _EXP_HI)):
        got = _one_rational(
            bd, rf"noncomputable def {name} : ℝ := \((\d+) / (\d+) : ℝ\)", f"BraggDefect.{name}")
        if got != q:
            raise SystemExit(
                f"DRIFT: BraggDefect.{name} is {got}, the certified bracket uses {q}")
    ex_start = bd.index("theorem excess_bracket")
    ex_body = bd[ex_start:bd.index("theorem defect_witness_offline", ex_start)]
    ex_hits = [sp.Rational(int(p), int(q)) for p, q in re.findall(r"\((\d+) / (\d+) : ℝ\)", ex_body)]
    for label, q in (("excess_bracket lower", _D_LO), ("excess_bracket upper", _D_HI)):
        if q not in ex_hits:
            raise SystemExit(
                f"DRIFT: BraggDefect.excess_bracket no longer carries the {label} constant {q}")
    zd = _ZOODH.read_text(encoding="utf-8")
    for label, q in (("cosh lower", _COSH_LO), ("cosh upper", _COSH_HI)):
        if f"({q.p} / {q.q} : ℝ)" not in zd:
            raise SystemExit(
                f"DRIFT: ZooDH.lean no longer carries the {label} constant {q.p}/{q.q}")


def _bridge() -> str:
    """The hand-written bridge: BraggDefect's vocabulary, then the UNCONDITIONAL witness.

    Five lines of real content.  `exp_tenth_bracket` is the emitted certificate; `expLo`/`expHi`
    are definitionally those literals, so unfolding them turns the certificate into exactly the
    `hexp` the MIRRORMERE artifact assumes -- and `bragg_defect_witness` then applies with no
    hypothesis left.  The hypothesis-carrying form is kept (and gated by the `example` below)
    because the registry's grant gate matches the node statement syntactically.
    """
    off_lo, off_hi = _island_offline_bracket()
    return f"""
/-- `exp_tenth_bracket_defs` -- the SAME certified bracket in BraggDefect's own vocabulary:
    `expLo`/`expHi` are by definition the two literals `exp_tenth_bracket` brackets between,
    so this is a pure unfolding.  It is the exact shape of the `hexp` hypothesis that
    `BraggDefect.bragg_defect_witness` (and the MIRRORMERE node `MM_bragg_defect_witness`)
    carries as an Arb input.  conjecture1_proved = False. -/
theorem exp_tenth_bracket_defs :
    BraggDefect.expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ BraggDefect.expHi := by
  unfold BraggDefect.expLo BraggDefect.expHi
  exact exp_tenth_bracket

/-- **`bragg_defect_witness_unconditional`** -- the MIRRORMERE defect witness with its Arb
    exponential-enclosure hypothesis DISCHARGED in the kernel.  Identical conclusion to
    `BraggDefect.bragg_defect_witness`; the `hexp` binder is gone, supplied by
    `exp_tenth_bracket_defs` (order-14 `Real.exp_bound`).

    SCOPE, unchanged: this is the finite synthetic-pair diffraction experiment of
    `BraggDefect.lean` -- the on-line configuration's defect functional is exactly 0 and the
    one-off-line-pair configuration's is bracketed strictly below 0.  Discharging a NUMERIC
    hypothesis makes the witness unconditional; it does not enlarge what the witness says, and
    the experiment's other trust seams (the BraggH100 Arb sign boxes, the band `hLine`) are
    untouched.  Nothing here is about RH.  conjecture1_proved = False. -/
theorem bragg_defect_witness_unconditional :
    BraggDefect.defectFunctional 0 = 0 ∧
    (({off_lo} : ℝ) ≤ BraggDefect.defectFunctional BraggDefect.excess ∧
      BraggDefect.defectFunctional BraggDefect.excess ≤ ({off_hi} : ℝ)) :=
  BraggDefect.bragg_defect_witness exp_tenth_bracket_defs

/-- The hypothesis-carrying form, kept so the MIRRORMERE grant gate's syntactic match against
    `Statements/MM_bragg_defect_witness.lean` still finds its statement.  The hypothesis is now
    inert -- the conclusion is `bragg_defect_witness_unconditional`. -/
theorem bragg_defect_witness_hyp_form
    (_hexp : BraggDefect.expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ BraggDefect.expHi) :
    BraggDefect.defectFunctional 0 = 0 ∧
    (({off_lo} : ℝ) ≤ BraggDefect.defectFunctional BraggDefect.excess ∧
      BraggDefect.defectFunctional BraggDefect.excess ≤ ({off_hi} : ℝ)) :=
  bragg_defect_witness_unconditional

-- STATEMENT GATE (kernel-enforced): the node statement of MM_bragg_defect_witness, written
-- exactly as `Statements/MM_bragg_defect_witness.lean` writes it (under `open BraggDefect`),
-- is inhabited by the hypothesis-carrying form.  A drift in either statement fails the build.
open BraggDefect in
example (hexp : expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ expHi) :
    defectFunctional 0 = 0 ∧
    (({off_lo} : ℝ) ≤ defectFunctional excess ∧
      defectFunctional excess ≤ ({off_hi} : ℝ)) :=
  bragg_defect_witness_hyp_form hexp
"""


def build() -> str:
    _assert_island_literals()
    fam = exp_enclosure_family(
        "ExpEnclosureInstances",
        GridSpec([("case", sorted(_CASES))]),
        lambda pt: _CASES[pt["case"]][0],
        spec=lambda pt: dict(_CASES[pt["case"]][1]),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ExpEnclosureInstances",),
                    imports=("Mathlib", "BraggDefect")),
        [ExpEnclosureEmitter()],
        ValidationReport(checks=(("exp_enclosure", True),)),
    )
    text = next(iter(report.files.values()))
    end = "end ExpEnclosureInstances"
    if end not in text:
        raise SystemExit("emitted file has no namespace footer to splice the bridge into")
    return text.replace(end, _bridge().lstrip("\n") + "\n" + end)


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ExpEnclosureInstances.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
