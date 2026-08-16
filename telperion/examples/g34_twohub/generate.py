"""G34 two-hub: tails + witness-searched small-donor certs.  --check = drift."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import family as F  # noqa: E402

from telperion import DirectPolyaEmitter, certify, diff_frozen, emit, freeze  # noqa: E402
from telperion.workflow import ShardSpec  # noqa: E402

HERE = Path(__file__).resolve().parent


def build():
    val = F.validation()
    tails = emit(
        certify(F.tails_family(), workers=8,
                cache_dir=HERE / ".telperion_cache"),
        F.profile(),
        [DirectPolyaEmitter()],
        val,
        file_name="TwoHubTails.lean",
    )
    small_cf = certify(F.smalldonor_family(), workers=8,
                       cache_dir=HERE / ".telperion_cache")
    small = emit(
        small_cf,
        F.profile(),
        [DirectPolyaEmitter()],
        val,
        shard=ShardSpec(max_theorems=400, module_base="G34.TwoHub.SmallDonor"),
    )
    return tails, small, small_cf


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    tails, small, small_cf = build()
    if args.check:
        ok = True
        for res, sub in ((tails, "tails"), (small, "smalldonor")):
            rep = diff_frozen(res, HERE / "frozen" / sub)
            if not rep.ok:
                ok = False
                print(f"DRIFT in {sub}:", *rep.details, sep="\n  ")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    for res, sub in ((tails, "tails"), (small, "smalldonor")):
        freeze(res, HERE / "frozen" / sub)
    (HERE / "frozen" / "witness_table.json").write_text(
        json.dumps(small_cf.witness_table(), indent=1)
    )
    print(
        f"TwoHubTails: {tails.n_theorems}; SmallDonor: {small.n_theorems} "
        f"across {len(small.files)} shard(s); witness table exported"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
