"""One-command verification of the 2026-08-14 arc (MR !69): runs every module's run_all().

Usage:  python3 proof/verify.py
Every claim in every module is an assert; any regression fails loudly (non-zero exit).
Full run ~20-40 min (the 442,800-case exact sweep dominates).
"""
from __future__ import annotations

import importlib
import os
import sys
import time

# self-locate the package root (the directory containing 'verification/')
_here = os.path.abspath(os.path.dirname(__file__))
if _here not in sys.path:
    sys.path.insert(0, _here)

MODULES = [
    "kelmans_mixed_load",
    "kelmans_vertex_budget",
    "kelmans_env_rules",
    "kelmans_unified_merge",
    "rate_bound_fixed_n",
    "slack_ledger_dichotomy",
    "amortized_hub_bound",
    "gap_discharges",
    "g34_merge_unblocking",
    "g34_residual_domination",
    "g34_multi_starofhubs",
    "g34_deep",
    "interpolation_lemma",
    "g1_floor_certificates",
    "g1_endpoint_certificates",
]

PKG = "verification"


def main() -> int:
    t0 = time.time()
    failed = []
    for name in MODULES:
        print(f"\n=== {name} ===", flush=True)
        t = time.time()
        try:
            mod = importlib.import_module(f"{PKG}.{name}")
            mod.run_all()
            print(f"--- {name}: GREEN ({time.time() - t:.0f}s)", flush=True)
        except Exception as e:                                    # noqa: BLE001
            print(f"--- {name}: FAILED: {e!r}", flush=True)
            failed.append(name)
    print(f"\n{'=' * 60}\nTOTAL: {len(MODULES) - len(failed)}/{len(MODULES)} modules green "
          f"({time.time() - t0:.0f}s)")
    if failed:
        print("FAILED:", failed)
        return 1
    print("THE 2026-08-14 ARC VERIFIES END TO END.  conjecture1_proved=False "
          "(G1 hardening, G7 Lean, independent review remain).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
