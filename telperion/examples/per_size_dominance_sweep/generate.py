"""Generate the per-size-dominance-sweep example: certify -> emit -> write.

    python examples/per_size_dominance_sweep/generate.py           # write lean/PerSizeDominanceSweep.lean
    python examples/per_size_dominance_sweep/generate.py --check    # drift check (no write)

The Brualdi–Goldwasser g-step per-size DOMINATION SWEEP (Hdom) — a FINITE sweep of
named configs at a fixed size ``n``.  EVOLVES the ``tight_cap_enclosure``
fixed-named-config emitter: for a fixed ``n`` we enumerate a finite SET of size-n
configs (each a list of rational cavity messages μ), certify the g-step closure

    (baseOf l)¹¹ · prodBcap l / (W · (5/3)¹¹)  ≤  1

for EACH config (the same concrete ``norm_num`` face tight_cap_enclosure emits),
then AGGREGATE into one theorem ``∀ l ∈ [l₁, l₂, …], … ≤ 1`` via
``List.forall_mem_cons`` dispatching to the per-config faces.

The EXACT rational defs of ``proof/formalization/R3Cert/`` (W = 64/621, glemma,
master_ub, Bcap = three-way min, baseOf, prodBcap) are inlined into the emitted
file's prelude (the SAME ``_INLINE_DEFS`` reused from ``emit_tight_cap_enclosure``)
so the file is self-contained (only ``import Mathlib``; does NOT import R3Cert).

This example emits a size-``n = 3`` sweep of three representative configs:
* all-cherry ``[1/3, 1/3, 1/3]`` (LHS ≈ 0.6463),
* mixed ``[1/3, 1/2, 1/3]`` (LHS ≈ 0.5301),
* arm-heavy ``[1/2, 1/2, 1/3]`` (LHS ≈ 0.4304).

HONEST SCOPE: this closes each LISTED config at size ``n = 3`` — a FINITE sweep,
aggregating the tight_cap_enclosure per-config certificate.  It does NOT prove the
enumeration is EXHAUSTIVE over all Balanced+Capped merge-normal states of size
``n`` (the structural normal-form characterization, still open), and it is
PER-``n``, NOT uniform in ``n`` (uniform-in-``n`` is the arm-rate unimodality,
partly in ``R47ArmRate``).  It does NOT touch the general-arity g-lemma open core.
conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `per_size_dominance_sweep` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_per_size_dominance_sweep import (  # noqa: E402
    _INLINE_DEFS,
    PerSizeDominanceSweepEmitter,
    per_size_dominance_sweep_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"size": n, "configs": [[μ, …], …]}
_SPECS = {
    0: {
        "size": 3,
        "configs": [
            ["1/3", "1/3", "1/3"],
            ["1/3", "1/2", "1/3"],
            ["1/2", "1/2", "1/3"],
        ],
    },
}
_NAMES = {0: "sweep_n3"}
_OUT = Path(__file__).resolve().parent / "lean" / "PerSizeDominanceSweep.lean"


def build() -> str:
    fam = per_size_dominance_sweep_family(
        "PerSizeDominanceSweep",
        GridSpec([("case", [0])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("PerSizeDominanceSweep",), prelude=_INLINE_DEFS),
        [PerSizeDominanceSweepEmitter()],
        ValidationReport(checks=(("per_size_dominance_sweep", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: PerSizeDominanceSweep.lean does not match regeneration")
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
