"""Generate the integrality-gate example: certify -> emit -> write.

    python examples/integrality_gate/generate.py           # write lean/IntegralityGate.lean
    python examples/integrality_gate/generate.py --check    # drift check (no write)

Integrality gate — a finite exceptional table + a uniform p-adic valuation
certificate (the BG "23-gate" strictness).  A property P(n) holds STRICTLY for
all n EXCEPT a finite exceptional set, and the exceptions occur exactly when a
prime p | n (the arithmetic obstruction).  Two composable decidable parts:

  * the p-adic tie pin  v_p(N) = k  (emit_padic's ValuationFact shape:
    (p^k | N) ∧ ¬ (p^(k+1) | N) := by norm_num), and
  * the finite exceptional table — one ℤ inequality per row (by norm_num) plus
    a single guarded  ∀ x ∈ table, x.1 < x.2 := by decide  (emit_finite_decide).

Two instances:
  - bg_23gate:  the BG 23-gate.  621/64 = 27·23 and 64·243·23 = 621·576 = 357696
                — the tie sits exactly on the 23-column, so the strict inequality
                is arithmetic, not smooth.  p-adic: v_23(621) = 1.  Table: the
                strict flanks around the 357696 tie + the 27·23 identity flanks.
  - p5_gate:    a small p=5 illustration.  v_5(50) = 2 (50 = 2·5²) + a 3-row table.

NOTE: the `integrality_gate` kind is not yet registered in
certify._SPECIAL_KINDS / _SPECIAL_DISPATCH (that is a REPORTED shared-file edit).
Until it lands, this script registers the dispatch locally at runtime so the real
certify()->emit() path exercises the emitter exactly as it would once the
one-line registration is in place.

HONEST SCOPE: certifies ONLY the finite exceptional table + the single p-adic
valuation fact pinning the tie at p | n.  Does NOT prove strictness on the
infinite non-exceptional set, nor close any BG obligation.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (telperion.certify is re-exported as the certify()
# FUNCTION at package level, so reach the module object directly).
from telperion.emit_integrality_gate import (  # noqa: E402
    IntegralityGateEmitter,
    integrality_gate_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# --- local dispatch registration (REPORTED as a shared-file edit) -------------
# Register "integrality_gate" so certify() routes it to the emitter's
# certify_integrality_gate_point exactly as the one-line shared edit would.

# spec: pt -> {"prime": p, "valuation_n": N, "valuation_k": k, "rows": [...]}
_SPECS = {
    0: {
        "prime": 23,
        "valuation_n": 621,          # 621 = 27·23 = 3^3·23  =>  v_23(621) = 1
        "valuation_k": 1,
        "rows": [
            (64 * 243 * 23, 621 * 576 + 1),   # 357696 < 357697  (tie +1)
            (621 * 576 - 1, 64 * 243 * 23),   # 357695 < 357696  (tie -1)
            (27 * 23, 622),                   # 621   < 622
            (64 * 243, 15553),                # 15552 < 15553
        ],
    },
    1: {
        "prime": 5,
        "valuation_n": 50,           # 50 = 2·5^2  =>  v_5(50) = 2
        "valuation_k": 2,
        "rows": [(1, 2), (7, 10), (49, 50)],
    },
}
_NAMES = {0: "ig_bg_23gate", 1: "ig_p5_gate"}
_OUT = Path(__file__).resolve().parent / "lean" / "IntegralityGate.lean"


def build() -> str:
    fam = integrality_gate_family(
        "IntegralityGate",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("IntegralityGate",)),
        [IntegralityGateEmitter()],
        ValidationReport(checks=(("integrality_gate", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: IntegralityGate.lean does not match regeneration")
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
