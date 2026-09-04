"""Generate the cavity-exchange example: certify -> emit -> write.

    python examples/cavity_exchange/generate.py           # write lean/CavityExchange.lean
    python examples/cavity_exchange/generate.py --check    # drift check (no write)

The Brualdi–Goldwasser Kelmans DE-BRANCH monotonicity step (Obligation A).  The
change ``Aobj(t')−Aobj(t) = P·FS·FQ·Φ`` factors with ``P,FS,FQ > 0`` (proven
context) and ``Φ`` BILINEAR in two marginals.  Affine-in-each-variable ⟹ ``Φ ≥ 0``
on the box reduces to ``Φ ≥ 0`` at the FOUR CORNERS; each corner, after the nonneg
domain shift (da=1+u, db=2+v, c=3+s), is an ALL-NONNEG-COEFF polynomial ⟹ positivity.

Four instances:
* CORNER C0 — the EXACT R47R4KelmansCornerCert.lean polynomial (all-nonneg-coeff Polya
  cert, coeffs [3,9,3,9,3,9,7,54,108,7,51,99]) → ``positivity``;
* CORNER C1 — a sibling all-nonneg-coeff polynomial (same shape) → ``positivity``;
* the REDUCTION application — a worked application of the reusable
  ``bilinear_ge_of_corners`` engine (in the prelude) on a concrete
  all-corner-nonneg form, closed by ``nlinarith`` inside the lemma.
The reusable ``bilinear_ge_of_corners`` lemma itself ships in the prelude.

HONEST SCOPE: certifies the bilinear-form corner reduction + the all-nonneg-coeff
Polya corners of the Kelmans de-branch ``Φ`` (generalizing the fixed R47R4Kelmans
corner certs to the parametric bilinear shape); the outer ``P·FS·FQ > 0`` factors
are the proven context.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `cavity_exchange` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_cavity_exchange import (  # noqa: E402
    _INLINE_DEFS,
    CavityExchangeEmitter,
    cavity_exchange_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"mode": ..., "corner": ..., "box": ...}
_SPECS = {
    0: {"mode": "corner", "corner": "C0"},
    1: {"mode": "corner", "corner": "C1"},
    2: {"mode": "reduction"},
}
_NAMES = {
    0: "kelmans_corner_C0_nonneg",
    1: "kelmans_corner_C1_nonneg",
    2: "kelmans_bilinear_box_reduction",
}
_OUT = Path(__file__).resolve().parent / "lean" / "CavityExchange.lean"


def build() -> str:
    fam = cavity_exchange_family(
        "CavityExchange",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("CavityExchange",), prelude=_INLINE_DEFS),
        [CavityExchangeEmitter()],
        ValidationReport(checks=(("cavity_exchange", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: CavityExchange.lean does not match regeneration")
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
