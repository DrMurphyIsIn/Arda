"""Generate the dVP-atoms example: certify -> emit -> write, for the three zero-free-region
frontier certificate shapes distilled from the de la Vallee Poussin work.

    python examples/dvp_atoms/generate.py           # write the three lean/*.lean files
    python examples/dvp_atoms/generate.py --check    # drift check (no write)

Three self-contained certificate families (only ``import Mathlib``):
  * bc_split          — log-derivative COMBINE: w = Z+E, ‖E‖≤B ⟹ -Re w ≤ B - Re Z (+slack≥0);
  * jensen_zero_count — Jensen zero-count for ANY analytic f (wraps sum_divisor_le);
  * sphere_bound      — strip-type growth bound ⟹ uniform bound on a sphere (disk geometry).

conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    BCSplitEmitter, GridSpec, JensenZeroCountEmitter, LeanProfile, SphereBoundEmitter,
    ValidationReport, bc_split_family, certify, emit, jensen_zero_count_family,
    sphere_bound_family,
)

_HERE = Path(__file__).resolve().parent

# (module name, kind, family builder, emitter, {case: spec}, {case: lean_name}, import line)
_JOBS = [
    ("BCSplit", "bc_split", bc_split_family, BCSplitEmitter,
     {0: {"slack": 0}, 1: {"slack": "1/10"}},
     {0: "bc_split_tight", 1: "bc_split_slack"}),
    ("JensenZeroCount", "jensen_zero_count", jensen_zero_count_family, JensenZeroCountEmitter,
     {0: {"r": "1/2", "R": "1"}, 1: {"r": "1/4", "R": "3/4"}},
     {0: "jensen_count_half_one", 1: "jensen_count_qtr_3qtr"}),
    ("SphereBound", "sphere_bound", sphere_bound_family, SphereBoundEmitter,
     {0: {"R": "1/2"}, 1: {"R": "1/4"}},
     {0: "sphere_bound_half", 1: "sphere_bound_qtr"}),
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
            print(f"wrote {out} ({len(text)} bytes)")
    return rc


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
