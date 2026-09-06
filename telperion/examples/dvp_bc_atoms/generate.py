"""Generate the dVP entire-part (i-b') atoms example: certify -> emit -> write.

    python examples/dvp_bc_atoms/generate.py           # write the three lean/*.lean files
    python examples/dvp_bc_atoms/generate.py --check    # drift check (no write)

Three self-contained certificate families (only ``import Mathlib``), distilled from the
de la Vallee Poussin entire-part argument:
  * max_modulus       — maximum-modulus propagation: ‖f‖≤B on the sphere ⟹ ‖f‖≤B on the disk;
  * bc_deriv_re       — real-part → derivative bound: Re h - Re h(c) ≤ M' ⟹ ‖deriv h c‖ ≤ 2M'/(R-r)
                        (Borel-Caratheodory + Cauchy);
  * entire_part_bound — ‖logDeriv g c‖ ≤ 2M'/(R-r) from the log‖g‖ oscillation (self-contained
                        3-lemma preamble: log branch + BC-Cauchy + composition).

conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    BCDerivReEmitter, EntirePartBoundEmitter, GridSpec, LeanProfile, MaxModulusEmitter,
    ValidationReport, bc_deriv_re_family, certify, emit, entire_part_bound_family,
    max_modulus_family,
)

_HERE = Path(__file__).resolve().parent

# (module name, kind, family builder, emitter, {case: spec}, {case: lean_name})
_JOBS = [
    ("MaxModulus", "max_modulus", max_modulus_family, MaxModulusEmitter,
     {0: {"R": "1/2", "B": 12}, 1: {"R": "1/4", "B": 3}},
     {0: "max_modulus_half", 1: "max_modulus_qtr"}),
    ("BCDerivRe", "bc_deriv_re", bc_deriv_re_family, BCDerivReEmitter,
     {0: {"R": "3/2", "r": "1/2", "Mp": 6}, 1: {"R": 1, "r": "1/4", "Mp": 2}},
     {0: "bc_deriv_re_a", 1: "bc_deriv_re_b"}),
    ("EntirePartBound", "entire_part_bound", entire_part_bound_family, EntirePartBoundEmitter,
     {0: {"R": "3/2", "r": "1/2", "Mp": 6}},
     {0: "entire_part_bound_a"}),
]


def _build_one(module, kind, fam_fn, emitter, specs, names) -> str:
    fam = fam_fn(
        module,
        GridSpec([("case", sorted(specs))]),
        lambda pt: names[pt["case"]],
        spec=lambda pt: specs[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=(module,)),
        [emitter()],
        ValidationReport(checks=((kind, True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    rc = 0
    for module, kind, fam_fn, emitter, specs, names in _JOBS:
        text = _build_one(module, kind, fam_fn, emitter, specs, names)
        out = _HERE / "lean" / f"{module}.lean"
        if check:
            if not out.exists() or out.read_text(encoding="utf-8") != text:
                print(f"DRIFT: {module}.lean does not match regeneration")
                rc = 1
            else:
                print(f"check OK: {module}.lean matches regeneration")
        else:
            out.parent.mkdir(exist_ok=True)
            out.write_text(text, encoding="utf-8")
            print(f"wrote {out.relative_to(_HERE)}")
    return rc


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check (no write)")
    args = ap.parse_args()
    raise SystemExit(main(check=args.check))
