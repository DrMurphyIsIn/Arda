"""Generate the 3-XOR moment-matrix PSD example: certify -> emit -> write.

    python examples/xor3_moment/generate.py           # write lean/Xor3Moment.lean
    python examples/xor3_moment/generate.py --check    # drift check (no write)

The Petersen-graph Tseitin 3-XOR instance (girth 5, UNSAT, width-4-conflict-free):
its degree-2 moment matrix is block-rank-one, certified PSD via the compact SOS
xᵀMx = Σ_class (Σ σ_S x_S)² — one square per derivability class.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import Xor3MomentPSDEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_xor3 import xor3_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "Xor3Moment.lean"


def _petersen():
    edges = []
    for i in range(5):
        edges.append((i, (i + 1) % 5))
        edges.append((5 + i, 5 + (i + 2) % 5))
        edges.append((i, i + 5))
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    eidx = {e: k for k, e in enumerate(edges)}
    inst = [(frozenset(eidx[e] for e in edges if v in e), -1 if v == 0 else 1)
            for v in range(10)]
    return inst, len(edges)


def build() -> str:
    inst, n = _petersen()
    fam = xor3_family(
        "Xor3Moment",
        GridSpec([("_", [0])]),
        lambda pt: "petersen_moment_psd",
        spec=lambda pt: (inst, n, 2),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("Xor3Moment",)),
        [Xor3MomentPSDEmitter()],
        ValidationReport(checks=(("xor3_moment", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: Xor3Moment.lean does not match regeneration")
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
