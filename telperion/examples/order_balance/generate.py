"""Generate the order-balance example: certify -> emit -> write.

    python examples/order_balance/generate.py           # write lean/OrderBalance.lean
    python examples/order_balance/generate.py --check    # drift check (no write)

The integer zero/pole-order HINGE at the 1-line (`ζ(1+it) ≠ 0`).  A
nonnegative-cosine weight vector `(a₀, …, a_m)` and integer zero orders
`(k₁, …, k_m ≥ 1)` force the boundary contradiction whenever the order balance is
strictly violated (`a₀ < Σ_{j≥1} a_j·k_j`): the pole residue `+a₀·1` at `s = 1`
loses to the zero residues `-a_j·k_j`, so `0 ≤ a₀ − Σ a_j k_j < 0` — `False`.
Generalizes `examples/zero_free_bridge` `zeta_boundary_contradiction`
(`3·1 − 4k − k' ≥ 0 ⟹ False`); the residue LIMITS are abstract-real hypotheses,
the emitter certifies only the finite linear hinge.

Two instances (the classical dVP boundary case):
  - dvp_341: weights a = (3, 4, 1), orders k = (1, 1) — the exact Mertens 3-4-1
             boundary (`3 < 4·1 + 1·1 = 5`), i.e. `zeta_boundary_contradiction`.
  - fejer_deg3: weights a = (20, 30, 12, 2), orders k = (1, 1, 1) — the degree-3
             Fejer `(1+cos)^3` certificate (`20 < 30 + 12 + 2 = 44`).

NOTE: the `order_balance` kind is registered by the maintainer in
certify._SPECIAL_KINDS / _SPECIAL_DISPATCH (a REPORTED one-line shared-file edit).
This script drives the emitter directly (no runtime monkeypatch) — the certify()
dispatch is exercised once the registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.emit_order_balance import (  # noqa: E402
    OrderBalanceEmitter,
    certify_order_balance_point,
    order_balance_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"weights": (a0, …, a_m), "orders": (k1, …, k_m)}
_SPECS = {
    0: {"weights": (3, 4, 1), "orders": (1, 1)},
    1: {"weights": (20, 30, 12, 2), "orders": (1, 1, 1)},
}
_NAMES = {0: "ob_dvp_341", 1: "ob_fejer_deg3"}
_OUT = Path(__file__).resolve().parent / "lean" / "OrderBalance.lean"


def build() -> str:
    fam = order_balance_family(
        "OrderBalance",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    insts = []
    for case in (0, 1):
        inst, _n = certify_order_balance_point(fam, {"case": case}, _NAMES[case])
        insts.append(inst)

    class _View:
        instances = insts

    profile = LeanProfile(namespace=("OrderBalance",))
    body, nthm = OrderBalanceEmitter().emit_body(_View(), profile)
    header = (
        "/- telperion order-balance example | family OrderBalance\n"
        f"   {nthm} theorems, {len(insts)} generation-time self-checks passed.\n"
        "   The integer zero/pole-order hinge at the 1-line (`ζ(1+it) ≠ 0`),\n"
        "   generalizing `zeta_boundary_contradiction` (examples/zero_free_bridge).\n"
        "   Residue limits are abstract-real hypotheses; only the finite linear\n"
        "   order-balance hinge is certified.  conjecture1_proved = False. -/\n\n"
        "import Mathlib\n\n"
        "namespace OrderBalance\n\n"
    )
    return header + body + "\nend OrderBalance\n"


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: OrderBalance.lean does not match regeneration")
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
