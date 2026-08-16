"""HypStarSymbolic: certify -> validate -> emit -> freeze.  --check = drift diff.

The 972-cell star-of-hubs discharge, sharded for compilability.  Emitted Lean
is not compiled in this repo's CI (large batch — the origin campaign's project
is the consumer); the regeneration diff + the exact validation + margins are.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from family import family, profile, validation  # noqa: E402

from telperion import DirectPolyaEmitter, certify, diff_frozen, emit, freeze  # noqa: E402
from telperion.workflow import ShardSpec  # noqa: E402

HERE = Path(__file__).resolve().parent


def build():
    fam = family()
    cf = certify(fam, workers=8)
    return emit(
        cf,
        profile(),
        [DirectPolyaEmitter()],
        validation(),
        shard=ShardSpec(max_theorems=120, module_base="R7Hyps.StarOfHubs.Cells"),
    ), cf


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--margins", action="store_true", help="tightness analysis")
    args = ap.parse_args()
    res, cf = build()
    if args.margins:
        from telperion.margins import margin_report

        reports = margin_report(cf, samples=20)
        tight = [r for r in reports if r.is_tight]
        print(f"{len(reports)} certificates; {len(tight)} tight/marginal; 5 smallest margins:")
        for r in reports[:5]:
            print("  " + r.render())
        return 0
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        if not rep.ok:
            print("DRIFT:", *rep.details, sep="\n  ")
        print("check:", "OK" if rep.ok else "FAILED")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(
        f"wrote {len(res.files)} shard(s), {res.n_theorems} theorems, "
        f"{res.n_checks} self-checks; hash {res.input_hash[:16]}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
