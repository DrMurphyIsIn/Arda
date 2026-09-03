"""Generate the tight-cap-enclosure example: certify -> emit -> write.

    python examples/tight_cap_enclosure/generate.py           # write lean/TightCapEnclosure.lean
    python examples/tight_cap_enclosure/generate.py --check    # drift check (no write)

The Brualdi–Goldwasser g-step "tight-cap enclosure" for NAMED child-message
configs.  For a config ``l`` (a list of rational cavity messages μ) the g-step
closure is

    (baseOf l)¹¹ · prodBcap l / (W · (5/3)¹¹)  ≤  1

with the EXACT rational defs of ``proof/formalization/R3Cert/`` (W = 64/621,
glemma, master_ub, Bcap = three-way min, baseOf, prodBcap), inlined into the
emitted file's prelude so it is self-contained (only ``import Mathlib``; does NOT
import the R3Cert project).

Two instances:
* the CONCRETE d=6 all-cherry TIE config ``[1/3]*5`` (5 children, μ = 1/3), the
  "27·23 = 621" integrality-tie config — a single ``norm_num`` over the unfolded
  defs (concrete rational LHS = 47976111050506371072/87946907297998046875 ≤ 1);
* the SYMBOLIC single non-leaf child over the box ``0 < μ ≤ 1/2`` (the arm face),
  mirroring ``single_child_le_one`` EXACTLY.

HONEST SCOPE: this emitter does the FIXED-named-config closures (the cert_jk /
tie faces), NOT the general-arity g-lemma ``gV_le`` / ``gstep_lt_gamma`` open
core.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_tight_cap_enclosure import (  # noqa: E402
    _INLINE_DEFS,
    TightCapEnclosureEmitter,
    tight_cap_enclosure_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# The `tight_cap_enclosure` kind is registered in telperion/certify.py.

# spec: pt -> {"mode": ..., "children": [...], "frac_cap": ...}
_SPECS = {
    0: {"mode": "concrete", "children": ["1/3", "1/3", "1/3", "1/3", "1/3"]},
    1: {"mode": "symbolic1"},
}
_NAMES = {0: "tie_cherry_d6", 1: "single_child_box"}
_OUT = Path(__file__).resolve().parent / "lean" / "TightCapEnclosure.lean"


def build() -> str:
    fam = tight_cap_enclosure_family(
        "TightCapEnclosure",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("TightCapEnclosure",), prelude=_INLINE_DEFS),
        [TightCapEnclosureEmitter()],
        ValidationReport(checks=(("tight_cap_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: TightCapEnclosure.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
