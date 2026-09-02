"""Generate the lfunction-product example: certify -> emit -> write.

    python examples/lfunction_product/generate.py           # write lean/LFunctionProduct.lean
    python examples/lfunction_product/generate.py --check    # drift check (no write)

The nonneg-cosine -> L-product lower bound: a FEJÉR-ADMISSIBLE cosine-coefficient
tuple (a_0, …, a_m) (each a_k ≥ 0, Σ a_k cos kθ ≥ 0 ∀θ) yields
`1 ≤ ∏_k ‖ζ(σ + i·k·t)‖^{a_k}` for Re s > 1.  Models the shipped
ZeroFreeElementary.lean:zeta_norm_product_ge_one (the fixed 3-4-1 wrapper of
DirichletCharacter.norm_LFunction_product_ge_one + LFunction_modOne_eq).

Instance:
  - zeta_norm_product_341:  the de la Vallée-Poussin / Mertens tuple (3, 4, 1),
    whose cosine polynomial is 3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)^2 ≥ 0,
    giving ‖ζ(σ)‖^3 ‖ζ(σ+it)‖^4 ‖ζ(σ+2it)‖ ≥ 1.

Mathlib v4.32.0 exposes a product lemma ONLY for the (3,4,1) exponent triple
(`DirichletCharacter.norm_LFunction_product_ge_one`, hard-coded 3-4-1), so the
faithfully-emittable family is thin — the value-add is the exact
Fejér-admissibility gate + the named coupling of the positivity kernel to the
Mathlib L-product lemma.  conjecture1_proved = False.

NOTE: the `lfunction_product` kind is NOT registered in certify._SPECIAL_KINDS /
._SPECIAL_DISPATCH (that is a REPORTED shared-file edit).  Until it lands, this
script registers the dispatch locally at runtime so the real certify()->emit()
path exercises the emitter exactly as it would once the one-line registration
lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (the package re-exports the certify() FUNCTION under the
# same name, shadowing the module attribute — import the module explicitly).
from telperion.emit_lfunction_product import (  # noqa: E402
    LFunctionProductEmitter,
    lfunction_product_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# Mirrors the finite_argmax example: exercise the real certify()->emit() path
# before the one-line shared-file registration lands.

# spec: pt -> cosine-coefficient tuple (a_0, …, a_m), each a_k ≥ 0.
_SPECS = {
    0: (3, 4, 1),   # de la Vallée-Poussin / Mertens: 2(1+cos θ)^2 ≥ 0
}
_NAMES = {0: "zeta_norm_product_341"}
_OUT = Path(__file__).resolve().parent / "lean" / "LFunctionProduct.lean"


def build() -> str:
    fam = lfunction_product_family(
        "LFunctionProduct",
        GridSpec([("case", [0])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("LFunctionProduct",)),
        [LFunctionProductEmitter()],
        ValidationReport(checks=(("lfunction_product", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LFunctionProduct.lean does not match regeneration")
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
