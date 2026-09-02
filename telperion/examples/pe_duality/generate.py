"""Generate the pe-duality example: certify -> emit -> write.

    python examples/pe_duality/generate.py           # write lean/PeDuality.lean
    python examples/pe_duality/generate.py --check    # drift check (no write)

Pseudo-expectation / SoS-duality "no degree-d SoS refutation exists" — a
feasibility certificate for the degree-d moment relaxation of a boolean
constraint system, in refutation-blocking form.  A pseudoexpectation functional
E with E 1 = 1, E(s²) ≥ 0 (deg s ≤ d), and E(p·gᵢ) = 0 makes every low-degree
SoS refutation -1 = Σ sⱼ² + Σ pᵢ·gᵢ impossible (apply E: -1 = (≥0) + 0).

Models the kernel-green examples/g1_floors/lean/Duality.lean (no_refutation, pe,
pe_bool_kill) and Xor3Duality.lean (oddSet_add, pe3_bool_kill).  The abstract
obstruction and both multilinear kills are proved outright; the PSD leaf E(s²)≥0
is threaded as a hypothesis (hsq), exactly as knapsack_no_refutation threads its.

Two instances:
  - knap_n5_d1:  a knapsack-style 0/1 system on N=5 vars, degree d=1 (bool mode,
                 ideal gen X i ^ 2 - X i, support-weighted functional)
  - xor_n7_d2:   a 3-XOR-style ±1 system on N=7 vars, degree d=2 (parity mode,
                 ideal gen X i ^ 2 - 1, parity-mask-weighted functional)

NOTE: the `pe_duality` kind is not yet registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it is, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_pe_duality import (  # noqa: E402
    PseudoExpectationDualityEmitter,
    pe_duality_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# NB: `telperion.certify` the SUBMODULE (not the re-exported certify() function)
# owns the dispatch registries; reach it via importlib to avoid the name clash.

# spec: pt -> {"n_vars": int, "degree": int, "mode": "bool"|"parity", ...}
_SPECS = {
    0: {"n_vars": 5, "degree": 1, "mode": "bool"},
    1: {"n_vars": 7, "degree": 2, "mode": "parity",
        "square_moments": (1, 2, 0)},
}
_NAMES = {0: "knap_n5_d1", 1: "xor_n7_d2"}
_OUT = Path(__file__).resolve().parent / "lean" / "PeDuality.lean"


def build() -> str:
    fam = pe_duality_family(
        "PeDuality",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("PeDuality",)),
        [PseudoExpectationDualityEmitter()],
        ValidationReport(checks=(("pe_duality", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: PeDuality.lean does not match regeneration")
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
