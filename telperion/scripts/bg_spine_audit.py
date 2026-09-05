#!/usr/bin/env python3
"""Fast BG-spine statement-identity gate (both trust halves, batched).

Runs the signature/statement-match audit over the trust-critical BG additive-
subaction spine against a BUILT ``R3Cert`` environment, in a SINGLE ``lake env lean``
load (batched — ~N× faster than per-decl).  Exits 0 iff every spine declaration
states its INDEPENDENTLY-specified intended proposition (defeq), else 1 with the
mismatches.  CI-able wherever the BG proof is built.

    python scripts/bg_spine_audit.py --env /path/to/proof/formalization

The intended statements are written here from the additive-subaction MATH, not copied
from the repo — a match certifies the bridge/witness/obligation are NOT weakened; a
weakened bound would mismatch (gate liveness is covered in tests/test_statement_match).
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.statement_match import statement_match_check, def_identity_check  # noqa: E402

_IMPORTS = ("import R3Cert.BGSCLSubaction", "import R3Cert.BGSCLGStepBridge")
_PRELUDE = "open R3Cert.BGSCL"

# INDEPENDENTLY-written intended types (from the additive-subaction math).
_SPINE = {
    "R3Cert.BGSCL.ceiling_of_subaction":
        "∀ (ρ : Branch → ℝ), IsSubaction ρ → (∀ b, 0 ≤ ρ b) → ∀ b, bell b ≤ 0",
    "R3Cert.BGSCL.ceiling_of_witness":
        "IsSubaction ρwit → ∀ b, bell b ≤ 0",
    "R3Cert.BGSCL.ceiling_of_gstep":
        "GStep → ∀ b, bell b ≤ 0",
}
# IsSubaction is a Prop-valued def — check it UNFOLDS to the genuine additive inequality.
_ISSUBACTION_BODY = (
    "∀ cs : List Branch, "
    "(Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) "
    "+ ρ (Branch.node cs) ≤ (cs.map ρ).sum"
)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="BG spine statement-identity gate")
    ap.add_argument("--env", required=True, help="built R3Cert Lake project dir")
    a = ap.parse_args(argv)

    res = statement_match_check(_SPINE, env_dir=a.env, imports=_IMPORTS,
                                prelude=_PRELUDE, batch=True)
    ok_def, err = def_identity_check("IsSubaction", "(ρ : Branch → ℝ)", _ISSUBACTION_BODY,
                                     env_dir=a.env, imports=_IMPORTS, prelude=_PRELUDE)
    print(f"BG spine signature audit: {res.summary()}")
    for n in res.matched:
        print(f"  MATCH    {n.split('.')[-1]}")
    for n, e in res.mismatched.items():
        print(f"  MISMATCH {n.split('.')[-1]}: {e[:80]}")
    print(f"IsSubaction def-identity (genuine additive inequality): "
          f"{'MATCH' if ok_def else 'MISMATCH: ' + str(err)[:80]}")

    ok = res.all_match and ok_def
    print(f"\n{'PASS' if ok else 'FAIL'} — spine states its intended propositions"
          if ok else f"\nFAIL — {len(res.mismatched) + (0 if ok_def else 1)} divergence(s)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
