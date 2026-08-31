"""Generate the BG m=2 arm-balancing certificate (route-b, kernel-gated).

    python examples/bg_arm_balancing/generate.py           # write lean/BGArmBalancing.lean
    python examples/bg_arm_balancing/generate.py --check    # drift check (no write)

The two-hub length-2-arm caterpillar `T(a, b)` (two adjacent hubs carrying `a` and `b` pendant length-2 arms)
has the EXACT closed-form monomer-dimer partition function

    Z(T(a,b)) = (3/2)^(a+b-2) * ( (4a+3)(4b+3) + 9 ) / ( 4 (a+1)(b+1) )

(`telperion.transfer_caterpillar.two_hub_Z`, derived from the (U,M) cavity, verified == `matching_free_energy.rho`
on the 0..8 grid).  At FIXED spine-arm-total `s = a+b` the `(3/2)^(s-2)/4` prefactor is common, so the
split-dependent factor is `g(a,b) = ((4a+3)(4b+3)+9)/((a+1)(b+1))`, and the toward-balance move satisfies the
FACTORED identity

    g(a-1, b+1) - g(a, b) = 2 (a-b-1)(2a+2b-1) / ( a (a+1)(b+1)(b+2) )   >  0   for integers a >= b+2

(every factor positive; `= 0` at the balanced tie `a = b+1`).  So moving one arm from the fuller hub to the
emptier one STRICTLY increases `Z` -- the rigorous, all-`(a,b)` m=2 arm-balancing lemma.  It is the one monotone
local move SALVAGED after "local Z-monotone reduction of every tree to the caterpillar family" was refuted at
n=16 (the balanced symmetric 3-spider S(3;2,2,2) is a strict single-edge-swap local max below the family max;
see docs/BG_PIECE3_OBSTRUCTION_MAP.md).

This example kernel-gates the balancing DIRECTION `Z(T(a,b)) < Z(T(a-1,b+1))` (exact closed-form rationals,
`two_hub_Z`) as finite `norm_num` anchor atoms over a spread of `(a,b)` with `a >= b+2`.  The rationals ARE the
graph invariants `Z(T(...))` (the closed form == `rho`, checked in `tests/test_transfer_caterpillar.py`); the
all-`(a,b)` generality is the Python-verified `arm_balance_delta_g` lemma, whose Lean upgrade obligation
(`field_simp; ring` for the identity, factor-sign positivity for `> 0`) is recorded there.  NOT the full BG
proof -- the reduction of the caterpillar complement + the exceptional-spider comparison remain.
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.transfer_caterpillar import two_hub_Z  # noqa: E402

NAMESPACE = "BGArmBalancing"
_OUT = Path(__file__).resolve().parent / "lean" / "BGArmBalancing.lean"

# (a, b) instances with a >= b+2 (toward-balance move a->a-1, b->b+1 strictly increases Z).
_INSTANCES = [(2, 0), (3, 0), (3, 1), (4, 1), (4, 2), (5, 2), (5, 3), (6, 3), (7, 4), (9, 3)]


def _rat(f) -> str:
    return f"(({f.numerator} : ℚ)/{f.denominator})"


def atoms():
    """List of (name, lhs, rhs) with the certified strict inequality Z(T(a,b)) < Z(T(a-1,b+1))."""
    out = []
    for a, b in _INSTANCES:
        lhs = two_hub_Z(a, b)                              # Z(T(a,b))
        rhs = two_hub_Z(a - 1, b + 1)                      # Z(T(a-1,b+1)) -- toward balance
        out.append((f"bg_armbal_{a}_{b}", lhs, rhs))
    return out


def build() -> str:
    for nm, lhs, rhs in atoms():
        assert lhs < rhs, f"{nm}: balancing inequality fails ({lhs} < {rhs})"
    head = (
        "/- BG m=2 arm-balancing (route-b, kernel-gated).\n"
        "   Two-hub caterpillar T(a,b): Z = (3/2)^(a+b-2)((4a+3)(4b+3)+9)/(4(a+1)(b+1)) (== rho, exact). At fixed\n"
        "   s=a+b the toward-balance move satisfies g(a-1,b+1)-g(a,b) = 2(a-b-1)(2a+2b-1)/(a(a+1)(b+1)(b+2)) > 0\n"
        "   for a>=b+2, so moving an arm from the fuller hub to the emptier one strictly increases Z. The one\n"
        "   monotone move salvaged after the n=16 refutation of local Z-monotone reduction to the family. Atoms:\n"
        "   Z(T(a,b)) < Z(T(a-1,b+1)) as exact closed-form rationals over a>=b+2 instances. The all-(a,b) lemma is\n"
        "   the Python-verified arm_balance_delta_g (field_simp;ring + positivity obligation recorded there). NOT\n"
        "   a proof of Brualdi-Goldwasser (complement reduction + exceptional-spider comparison remain).\n"
        "   conjecture1_proved = False. -/\n"
        "import Mathlib\n\n"
        f"namespace {NAMESPACE}\n\n"
    )
    body = "\n".join(f"theorem {nm} : {_rat(lhs)} < {_rat(rhs)} := by norm_num" for nm, lhs, rhs in atoms())
    return head + body + f"\n\nend {NAMESPACE}\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        if cur != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py"); return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches"); return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
