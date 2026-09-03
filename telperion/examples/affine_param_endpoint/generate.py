"""Generate the affine-param-endpoint example: certify -> emit -> write.

    python examples/affine_param_endpoint/generate.py           # write lean/AffineParamEndpoint.lean
    python examples/affine_param_endpoint/generate.py --check    # drift check (no write)

The Brualdi–Goldwasser SCLStep "affine-in-parameter endpoint collapse".  The
value functional ``bV μ b = bell b + μ·bY b`` is AFFINE in the price ``μ``, and
the SCL obligation ``bV μ (node cs) ≤ bV μ cherry`` on the price interval
``I = [456/3703, 3/7]`` is equivalent — because the gap ``G(μ) = A + μ·B`` is
affine — to nonnegativity at the two rational endpoints, via the identity

    (hi−lo)(A+μB) = (hi−μ)(A+loB) + (μ−lo)(A+hiB),   both summands ≥ 0.

Three self-contained theorems (only ``import Mathlib``): the abstract core, the
bV-shaped SCLStep application (``bell``/``bY`` opaque), and a concrete rational
sanity instance at the real endpoints ``456/3703`` and ``3/7``.

HONEST SCOPE: this reduces the affine-in-parameter interval inequality to two
endpoints — for SCLStep it collapses the price interval ``I``.  It does NOT
prove the endpoint inequalities themselves.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `affine_param_endpoint` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_affine_param_endpoint import (  # noqa: E402
    AffineParamEndpointEmitter,
    affine_param_endpoint_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"A": ..., "B": ..., "lo": ..., "hi": ..., "mu_test": ...}.
# Defaults use the real SCLStep interval I = [456/3703, 3/7], interior μ = 1/4.
_SPECS = {
    0: {"A": 1, "B": 2, "mu_test": "1/4"},     # ascending gap
    1: {"A": 1, "B": -1, "mu_test": "3/8"},    # descending gap, still ≥0 on I
}
_NAMES = {0: "scl_gap_ascending", 1: "scl_gap_descending"}
_OUT = Path(__file__).resolve().parent / "lean" / "AffineParamEndpoint.lean"


def build() -> str:
    fam = affine_param_endpoint_family(
        "AffineParamEndpoint",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("AffineParamEndpoint",)),
        [AffineParamEndpointEmitter()],
        ValidationReport(checks=(("affine_param_endpoint", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: AffineParamEndpoint.lean does not match regeneration")
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
