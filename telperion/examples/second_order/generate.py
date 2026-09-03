"""Generate the second-order-recurrence example: certify -> emit -> write.

    python examples/second_order/generate.py           # write lean/SecondOrder.lean
    python examples/second_order/generate.py --check     # drift check (no write)

Closed forms for a second-order (three-term) linear recurrence
``A(q)*f(q+2) + B(q)*f(q+1) + C(q)*f(q) = 0`` — the Hahn/Krawtchouk/Jacobi
generalization of the shipped first-order forward-telescoping emitter
(examples/fwd_telescope).  See telperion/examples/knapsack_sos/FULLRANK_W2_SCOPING.md
item (c) for the W2 motivation.

Two instances:
  - so_geom_2_3: f(q+2) - 5 f(q+1) + 6 f(q) = 0, characteristic (x-2)(x-3),
                 closed form g(q) = 2^q + 3^q (bases 2, 5).
  - so_linear:   f(q+2) - 2 f(q+1) + f(q) = 0 (second difference zero),
                 closed form g(q) = q, tail start q0 = 3 (bases 3, 4).

NOTE: the `second_order` kind's one-line registration in certify._SPECIAL_KINDS /
_SPECIAL_DISPATCH is a REPORTED shared-file edit.  Once it lands, the real
certify()->emit() path exercises this emitter with no local shims (this script
uses only the public builder + emitter, exactly like examples/finite_argmax).
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_second_order import (  # noqa: E402
    SecondOrderRecurrenceEmitter,
    second_order_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# The `second_order` kind's registration in certify._SPECIAL_KINDS /
# _SPECIAL_DISPATCH is a REPORTED one-line shared-file edit (see module
# real certify()->emit() path exercises the emitter exactly as it will once the
# registration is in place — same pattern the finite_argmax example used
# pre-registration.  This touches no shared file.



_q = sp.Symbol("q")

# spec: pt -> {"q0", "A", "B", "C", "g", "g_lean"}
_SPECS = {
    0: {
        "q0": 0,
        "A": sp.Integer(1), "B": sp.Integer(-5), "C": sp.Integer(6),
        "g": 2 ** _q + 3 ** _q,
        "g_lean": "(2 : ℝ) ^ q + (3 : ℝ) ^ q",
    },
    1: {
        "q0": 3,
        "A": sp.Integer(1), "B": sp.Integer(-2), "C": sp.Integer(1),
        "g": _q,
        "g_lean": "(q : ℝ)",
    },
}
_NAMES = {0: "so_geom_2_3", 1: "so_linear"}
_OUT = Path(__file__).resolve().parent / "lean" / "SecondOrder.lean"


def build() -> str:
    fam = second_order_family(
        "SecondOrder",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SecondOrder",)),
        [SecondOrderRecurrenceEmitter()],
        ValidationReport(checks=(("second_order", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SecondOrder.lean does not match regeneration")
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
