"""Generate the parametric-holomorphy example: certify -> emit -> write.

    python examples/parametric_holomorphy/generate.py           # write lean/ParametricHolomorphy.lean
    python examples/parametric_holomorphy/generate.py --check    # drift check (no write)

Analyticity of a parametric tail integral: the fractional-part tail integral

    fractIntegral_c s = ∫ x in Ioi c, {x} · (x:ℂ)^{-(s+1)} dx      (c ≥ 1)

is COMPLEX-DIFFERENTIABLE in the parameter `s` on `{σ₀ < Re s}` (σ₀ > 0).  A
`(c, σ₀)`-parameterized copy of the PROVEN `differentiableAt_fractIntegral`
(examples/zero_free_bridge/lean/StripReprR2.lean), gated by the two exact decay
inequalities `−σ₀−1 < −1` and `−(σ₀/2)−1 < −1`.

ONE instance (the fract integrand is the only integrand in the corpus):
  - fract_c1_sig_half:  ray Ioi 1, floor σ₀ = 1/2.

The `fractIntegrand_c` / `fractIntegral_c` defs and the `open` line live in the
LeanProfile prelude, so the emitted file is self-contained (import Mathlib).

NOTE: the `parametric_holomorphy` kind is not yet registered in
certify._SPECIAL_KINDS / _SPECIAL_DISPATCH (that is a REPORTED shared-file edit).
Until it lands, this script registers the dispatch locally at runtime so the real
certify()->emit() path exercises the emitter exactly as it would in production.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from fractions import Fraction  # noqa: E402


from telperion import ValidationReport, certify, emit  # noqa: E402

# reach the certify SUBMODULE (the package re-binds the name `certify` to the
# certify() function, so import the module object explicitly).
from telperion.emit_parametric_holomorphy import (  # noqa: E402
    ParametricHolomorphyEmitter,
    parametric_holomorphy_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


# spec: pt -> {"c": ..., "sigma0": ..., "integrand": "fract"}
_SPECS = {
    0: {"c": Fraction(1), "sigma0": Fraction(1, 2), "integrand": "fract"},
}
_NAMES = {0: "differentiableAt_fractIntegral_c"}
_OUT = Path(__file__).resolve().parent / "lean" / "ParametricHolomorphy.lean"

# The fract-integrand defs + open line, supplied to the emitted file's prelude so
# it is self-contained.  `fractIntegrand_c`/`fractIntegral_c` mirror StripRepr.lean
# with the ray left as a general `c` fixed per-instance (here 1); the emitted proof
# only ever unfolds these two defs by name.
_PRELUDE = """\
open Set MeasureTheory Filter Topology

/-- The fractional-part integrand `{x} · (x)^{-(s+1)}` (ray-agnostic). -/
noncomputable def fractIntegrand_c (s : ℂ) (x : ℝ) : ℂ :=
  ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)

/-- The fractional-part tail integral over `Ioi 1` (the corpus's `c = 1`). -/
noncomputable def fractIntegral_c (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), fractIntegrand_c s x"""


def build() -> str:
    fam = parametric_holomorphy_family(
        "ParametricHolomorphy",
        GridSpec([("case", [0])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ParametricHolomorphy",), prelude=_PRELUDE),
        [ParametricHolomorphyEmitter()],
        ValidationReport(checks=(("parametric_holomorphy", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ParametricHolomorphy.lean does not match regeneration")
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
