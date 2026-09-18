"""Generate certified Lehmer pairs — Face 5 (de Bruijn–Newman / criticality).

    python examples/lehmer_pair/generate.py           # write lean/LehmerPair.lean
    python examples/lehmer_pair/generate.py --check    # drift check (no write)

The de Bruijn–Newman constant Λ satisfies RH ⟺ Λ ≤ 0 (Rodgers–Tao proved Λ ≥ 0).
A *Lehmer pair* — two consecutive zeros anomalously closer than the mean spacing —
is the Face-5 witness.  This example scans the low-height zeros for the closest
pairs and, for each, emits the certified quality inequality
``quality_short ≤ qcap < 1`` (quality = δ²·C_n from the Arb-certified ordinates,
an exact rational rounded up, checked by ``norm_num``).  The de Bruijn–Newman Λ
LOWER BOUND that CNV derives from a Lehmer pair is shipped as the documented WIP
skeleton ``lehmer_lambda_bound_wip`` (the CNV constant is unverified this pass —
see the emitter's module WIP note); no numeric Λ bound is a kernel claim.

The file also carries ``lehmer_neg_refutes``, the falsifiability face.

HONEST SCOPE: at accessible heights no strong Lehmer pair exists, so these are
modest close pairs (quality ~0.09, well below the 1 threshold), NOT record
Λ bounds.  The instrument is real (certified Lehmer pairs); the Λ arithmetic is
WIP.  conjecture1_proved = False.

Dependency: python-flint with Platt machinery (see the `flint` manifest group).
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_lehmer_pair import (  # noqa: E402
    LehmerPairEmitter,
    find_closest_pair,
    lehmer_lambda_bound_wip_lean,
    lehmer_pair_family,
    lehmer_pair_quality,
    lehmer_refutation_atom_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# Scan windows; the closest pair in each is a Lehmer-pair candidate.
SCAN_WINDOWS = [(1, 200), (200, 500), (500, 900), (900, 1400)]
_OUT = Path(__file__).resolve().parent / "lean" / "LehmerPair.lean"


def _pairs():
    seen = set()
    out = []
    for lo, hi in SCAN_WINDOWS:
        n, ratio = find_closest_pair(lo, hi)
        if n in seen:
            continue
        q, _gap, _info = lehmer_pair_quality(n)
        if q < 1 and n not in seen:  # a genuine Lehmer pair
            seen.add(n)
            out.append(n)
    return out


def build() -> str:
    ns = _pairs()
    assert ns, "no Lehmer pair found in the scan windows"
    fam = lehmer_pair_family(
        "LehmerPair",
        GridSpec([("n", ns)]),
        lambda pt: f"lehmer_n{pt['n']}",
        spec=lambda pt: {"n_index": pt["n"]},
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("LehmerPair",),
            prelude=(lehmer_lambda_bound_wip_lean() + "\n" + lehmer_refutation_atom_lean()),
        ),
        [LehmerPairEmitter()],
        ValidationReport(checks=(("lehmer_pair", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LehmerPair.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} (Lehmer pairs + WIP Λ skeleton + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
