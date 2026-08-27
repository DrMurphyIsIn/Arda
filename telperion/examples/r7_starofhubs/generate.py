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

from telperion import (  # noqa: E402
    DirectPolyaEmitter, certify, diff_frozen, emit, freeze,
    render_sharded_challenge_scaffolds, sharded_challenge_configs,
    write_challenge_config,
)
from telperion.workflow import ShardSpec  # noqa: E402

HERE = Path(__file__).resolve().parent
MODULE_BASE = "R7Hyps.StarOfHubs.Cells"


def build():
    import time as _t

    marks = [("start", _t.monotonic())]
    fam = family()
    cf = certify(fam, workers=8, cache_dir=HERE / ".telperion_cache")
    marks.append(("certify", _t.monotonic()))
    val = validation()
    marks.append(("validate", _t.monotonic()))
    res = emit(
        cf,
        profile(),
        [DirectPolyaEmitter()],
        val,
        shard=ShardSpec(max_theorems=120, module_base=MODULE_BASE),
    )
    marks.append(("hash+emit", _t.monotonic()))
    for (label, t1), (_, t0) in zip(marks[1:], marks):
        print(f"[phase] {label}: {t1 - t0:.0f}s", flush=True)
    return res, cf


def write_comparator(res, out_dir: Path) -> None:
    """Emit one Comparator challenge per shard (config JSON + challenge module).

    A sharded emit spans modules ``R7Hyps.StarOfHubs.Cells``, ``…Cells2``, …;
    each shard DECLARES its own 120 theorems, so each becomes its own
    ``solution_module`` with a paired ``…Challenge`` module restating just that
    shard's statements.  `lake exe comparator <json>` then certifies each shard
    independently (parallelizable) against the clean axiom set + nanoda kernel.
    """
    from family import profile as _profile

    prof = _profile()
    out_dir.mkdir(parents=True, exist_ok=True)
    scaffolds = render_sharded_challenge_scaffolds(res, prof, module_base=MODULE_BASE)
    for chal_file, text in scaffolds.items():
        (out_dir / chal_file).write_text(text)
    configs = sharded_challenge_configs(res, prof, module_base=MODULE_BASE)
    for cfg in configs:
        stem = str(cfg["solution_module"]).rsplit(".", 1)[-1]
        write_challenge_config(out_dir / f"{stem}.comparator.json", cfg)
    total = sum(len(c["theorem_names"]) for c in configs)
    print(f"wrote {len(configs)} shard comparator challenge(s) "
          f"({total} theorems) + {len(scaffolds)} challenge module(s)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--margins", action="store_true", help="tightness analysis")
    ap.add_argument("--comparator", action="store_true",
                    help="also emit per-shard openai/ten-proofs Comparator challenges")
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
    if args.comparator:
        write_comparator(res, HERE / "comparator")
    return 0


if __name__ == "__main__":
    sys.exit(main())
