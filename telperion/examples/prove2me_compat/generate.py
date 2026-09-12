"""Compat smoke: emit the known-good Bernoulli family, build under Lean 4.33.1.

The bridge submits proofs to prove2.me, which accepts only Lean 4.33.1 /
4.30.0 / 4.29.0-rc3.  Telperion examples pin v4.32.0.  This example proves
the emitted tactic cores (ring/positivity/norm_num/linarith) survive the
newer pin.

Run:  python3 generate.py && cd lean && lake exe cache get && lake build
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "src"))
sys.path.insert(0, str(HERE.parents[0] / "bernoulli"))

from generate import (  # noqa: E402  # type: ignore[import]
    _exact_spot_checks,
    bernoulli_family,
    bernoulli_profile,
)
from telperion import DirectPolyaEmitter, certify, emit  # noqa: E402


def main() -> int:
    res = emit(
        certify(bernoulli_family()),
        bernoulli_profile(),
        [DirectPolyaEmitter()],
        _exact_spot_checks(),
        file_name="Prove2MeCompat.lean",
    )
    out = HERE / "lean" / "Prove2MeCompat.lean"
    # res.files is a dict[str, str]; we want the single emitted file.
    (text,) = res.files.values()
    out.write_text(text)
    print(f"emitted {res.n_theorems} theorems -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
