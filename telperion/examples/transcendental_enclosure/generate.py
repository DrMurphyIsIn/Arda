"""Generate the transcendental-enclosure example: certify -> emit -> write.

    python examples/transcendental_enclosure/generate.py           # write lean/TranscendentalEnclosure.lean
    python examples/transcendental_enclosure/generate.py --check    # drift check (no write)

Certifies RATIONAL lower/upper bounds ``L ≤ expr ≤ U`` for a transcendental
expression over a box, kernel-checked via Mathlib.  This serves TWO fronts:

  * FRONT 1 (BG compact-core cells, LIVE): each per-cell inequality contains
    ``e_v = log(1 + S/d) − F*``; enclosing ``log(1 + x)`` between rationals over
    the cell box turns the cell into a pure-rational ``nlinarith`` goal.  The
    ``log`` face does exactly this: UPPER ``log(1+x) ≤ x`` (all x ≥ 0) via
    ``Real.log_le_sub_one_of_pos``, and a rational LOWER bound over the box via
    ``Real.log`` monotonicity + ``Real.le_log_iff_exp_le`` + the degree-3 Taylor
    ``Real.exp_bound'``.

  * FRONT 2 (Montgomery–Taylor extremal constant, AxiomMath/ZetaZeros,
    arXiv:2609.02882): ``C₀ = 3/2 − (1/√2)·cot(1/√2) = 0.6725…``; a rational
    enclosure needs cos/sin bounds at ``1/√2``.  HONESTY: a kernel-checked
    enclosure of ``C₀`` is genuinely fiddly (needs ``√2`` + cos/sin Taylor bounds),
    so — per the mandate that a valid loose bound that COMPILES beats a tight
    bound that does not — the trig face is DEFERRED as a follow-on and is NOT
    emitted here.  The log face (BG-critical) ships alone and green.

Three self-contained theorems per instance (only ``import Mathlib``): the tangent
UPPER bound, the rational LOWER bound over the box, and the packaged enclosure.

conjecture1_proved=False.
"""
import argparse
import importlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `transcendental_enclosure` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_transcendental_enclosure import (  # noqa: E402
    TranscendentalEnclosureEmitter,
    transcendental_enclosure_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"face": "log", "x0": ..., "x1": ..., "L": ..., "U": ...}.
# Instance 0: nontrivial box [1/4, 1/2], L = 1/5 (exp(1/5) ≤ 5/4), U = 1/2.
# Instance 1: box [0, 1/2], L = 0 (trivial floor via exp(0)=1 ≤ 1), U = 1/2.
_SPECS = {
    0: {"face": "log", "x0": "1/4", "x1": "1/2", "L": "1/5", "U": "1/2"},
    1: {"face": "log", "x0": "0", "x1": "1/2", "L": "0", "U": "1/2"},
}
_NAMES = {0: "log1p_encl_qtr_half", 1: "log1p_encl_zero_half"}
_OUT = Path(__file__).resolve().parent / "lean" / "TranscendentalEnclosure.lean"


def build() -> str:
    fam = transcendental_enclosure_family(
        "TranscendentalEnclosure",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("TranscendentalEnclosure",),
            prelude=(
                "-- Provenance: kin to the Montgomery-Taylor transcendental-constant\n"
                "-- enclosure of AxiomMath/ZetaZeros (arXiv:2609.02882); this ships the\n"
                "-- rational log face only (the trig/C0 face is deferred). Independently\n"
                "-- re-implemented; see NOTICE.md for full attribution."
            ),
        ),
        [TranscendentalEnclosureEmitter()],
        ValidationReport(checks=(("transcendental_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: TranscendentalEnclosure.lean does not match regeneration")
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
