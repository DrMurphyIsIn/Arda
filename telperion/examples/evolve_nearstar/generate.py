"""Freeze the evolve-discovered near-star champion into Lean.

Runs the structured (LLM-free) evolve loop (deterministic, seed=0), takes the
certifying champion, and writes its reusable ratio certificate — bundled with the
`Telperion.unimodal_peak` prelude — to `lean/EvolveNearStar.lean`.

    python examples/evolve_nearstar/generate.py

Idempotent: same seed → byte-identical output.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.evolve.freeze import build_frozen_lean, discover_nearstar_champion  # noqa: E402


def main() -> int:
    rep = discover_nearstar_champion(seed=0)
    c = rep.champion
    print(
        f"champion: ratio_src={c.ratio_src} s0={c.s0} lift_max={c.lift_max} "
        f"score={rep.champion_score} evals={rep.evaluations}"
    )
    text = build_frozen_lean(c)
    out = Path(__file__).resolve().parent / "lean" / "EvolveNearStar.lean"
    out.parent.mkdir(exist_ok=True)
    out.write_text(text, encoding="utf-8")
    print(f"wrote {out} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
