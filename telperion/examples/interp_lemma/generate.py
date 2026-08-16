"""Interpolation lemma: I1/I2 symbolic identities + light-top facts."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import family as F  # noqa: E402

from telperion import (  # noqa: E402
    ExactFactEmitter,
    IdentityEmitter,
    certify,
    diff_frozen,
    emit,
    freeze,
)

HERE = Path(__file__).resolve().parent


def build():
    val = F.validation()
    ids = emit(
        certify(F.i1_family()),
        F.profile(),
        [IdentityEmitter()],
        val,
        file_name="InterpI1.lean",
    )
    i2 = emit(
        certify(F.i2_family()),
        F.profile(),
        [IdentityEmitter()],
        val,
        file_name="InterpI2.lean",
    )
    light = emit(
        certify(F.light_family()),
        F.profile(),
        [ExactFactEmitter(spelling=F.light_spelling, tactic="norm_num",
                          type_ascription="ℚ")],
        val,
        file_name="InterpLight.lean",
    )
    return ids, i2, light


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    ids, i2, light = build()
    if args.check:
        ok = True
        for res, sub in ((ids, "i1"), (i2, "i2"), (light, "light")):
            rep = diff_frozen(res, HERE / "frozen" / sub)
            if not rep.ok:
                ok = False
                print(f"DRIFT in {sub}:", *rep.details, sep="\n  ")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    for res, sub in ((ids, "i1"), (i2, "i2"), (light, "light")):
        freeze(res, HERE / "frozen" / sub)
    (HERE / "frozen" / "witness_table.json").write_text(
        json.dumps({k: list(v) for k, v in F.witness_table().items()}, indent=1)
    )
    print(
        f"InterpI1: {ids.n_theorems} identities; InterpI2: {i2.n_theorems}; "
        f"InterpLight: {light.n_theorems} facts (witness table exported)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
