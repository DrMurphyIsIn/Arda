"""Generate the dVP geometry/two-scale atoms example: certify -> emit -> write.

    python examples/dvp_geom_atoms/generate.py           # write the three lean/*.lean files
    python examples/dvp_geom_atoms/generate.py --check    # drift check (no write)

Three self-contained certificate families (only `import Mathlib`), distilled from the dVP Blaschke /
two-scale work:
  * two_scale_separation — inner-disk point vs outer-sphere point: R − R₀ ≤ ‖z − ρ‖;
  * far_pole_sum         — rational sum with poles outside the disk: ‖Σ (n u)conj u/(R²−conj u z)‖ ≤ (Σ|n u|)/(R−‖z‖);
  * herglotz_lower       — keep equal-height zero, drop nonneg rest: k/(σ−β) ≤ Re(Σ m/((σ+γI)−ρ)).

conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    FarPoleSumEmitter, GridSpec, HerglotzLowerEmitter, LeanProfile, TwoScaleSeparationEmitter,
    ValidationReport, certify, emit, far_pole_sum_family, herglotz_lower_family,
    two_scale_separation_family,
)

_HERE = Path(__file__).resolve().parent

_JOBS = [
    ("TwoScaleSeparation", "two_scale_separation", two_scale_separation_family, TwoScaleSeparationEmitter,
     {0: {"R": "3/2", "R0": 1}, 1: {"R": 2, "R0": "1/2"}},
     {0: "two_scale_3half_one", 1: "two_scale_two_half"}),
    ("FarPoleSum", "far_pole_sum", far_pole_sum_family, FarPoleSumEmitter,
     {0: {"R": "3/2"}, 1: {"R": 2}},
     {0: "far_pole_3half", 1: "far_pole_two"}),
    ("HerglotzLower", "herglotz_lower", herglotz_lower_family, HerglotzLowerEmitter,
     {0: {"sigma": "3/2", "beta": "1/2", "k": 1}},
     {0: "herglotz_lower_a"}),
]


def _build_one(module, kind, fam_fn, emitter, specs, names) -> str:
    fam = fam_fn(module, GridSpec([("case", sorted(specs))]),
                 lambda pt: names[pt["case"]], spec=lambda pt: specs[pt["case"]])
    report = emit(certify(fam), LeanProfile(namespace=(module,)), [emitter()],
                  ValidationReport(checks=((kind, True),)))
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    rc = 0
    for module, kind, fam_fn, emitter, specs, names in _JOBS:
        text = _build_one(module, kind, fam_fn, emitter, specs, names)
        out = _HERE / "lean" / f"{module}.lean"
        if check:
            if not out.exists() or out.read_text(encoding="utf-8") != text:
                print(f"DRIFT: {module}.lean does not match regeneration"); rc = 1
            else:
                print(f"check OK: {module}.lean matches regeneration")
        else:
            out.parent.mkdir(exist_ok=True); out.write_text(text, encoding="utf-8")
            print(f"wrote {out.relative_to(_HERE)}")
    return rc


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    raise SystemExit(main(check=args.check))
