"""Assemble the RH lake library from the frozen emitted Lean + transcendental
samples, so CI `lake build` actually KERNEL-CHECKS the whole RH/transcendental
line (turan/jensen/toeplitz/newton hyperbolicity + exp/log brackets).

Frozen files stay the source of truth; this copies them into RH/<Module>.lean
(module path = namespace-independent) and writes the library root.  Transcendental
certificates without an example (LogBound) get a small generated sample module.

    python3 examples/rh_lean/build.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXAMPLES = HERE.parent
sys.path.insert(0, str(EXAMPLES.parent / "src"))

from telperion import (  # noqa: E402
    LogBoundCertificate, PiBracketCertificate, SqrtBracketCertificate,
)

# frozen emitted Lean  ->  RH library module
FROZEN = {
    "Turan": "turan_xi/frozen/RiemannTuran.lean",
    "Jensen": "jensen_xi/frozen/CubicJensen.lean",
    "Toeplitz": "toeplitz_xi/frozen/ToeplitzXi.lean",
    "Newton": "newton_xi/frozen/NewtonXi.lean",
    "ExpBracket": "exp_bracket/frozen/ExpBracket.lean",
}


def _logbound_module() -> str:
    # a handful of in-kernel Real.log brackets (transcendental skill, no example)
    samples = [("log_two", 2, 1), ("log_three_halves", 3, 2), ("log_ten", 10, 1)]
    body = "\n\n".join(
        LogBoundCertificate(name=nm, n=n, d=d).lean().rstrip() for nm, n, d in samples)
    return ("/- Generated transcendental samples (LogBoundCertificate). -/\n"
            "import Mathlib\n\nnamespace LogBound\n\n" + body + "\n\nend LogBound\n")


def _pi_module() -> str:
    thm = PiBracketCertificate(name="pi_bracket").lean().rstrip()
    return ("/- Generated transcendental sample (PiBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace PiBracket\n\n" + thm + "\n\nend PiBracket\n")


def _sqrt_module() -> str:
    samples = [("sqrt_two", 2, 1), ("sqrt_three", 3, 1), ("sqrt_ten", 10, 1)]
    body = "\n\n".join(
        SqrtBracketCertificate.build(nm, qn, qd).lean().rstrip() for nm, qn, qd in samples)
    return ("/- Generated transcendental samples (SqrtBracketCertificate). -/\n"
            "import Mathlib\n\nnamespace SqrtBracket\n\n" + body + "\n\nend SqrtBracket\n")


def modules() -> dict:
    out = {}
    for mod, rel in FROZEN.items():
        out[mod] = (EXAMPLES / rel).read_text()
    out["LogBound"] = _logbound_module()
    out["PiBracket"] = _pi_module()
    out["SqrtBracket"] = _sqrt_module()
    return out


def root(mods) -> str:
    return ("/- RH library root -- every module is generated/frozen. -/\n"
            + "\n".join(f"import RH.{m}" for m in mods) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    mods = modules()
    files = {f"RH/{m}.lean": text for m, text in mods.items()}
    files["RH.lean"] = root(mods)
    if args.check:
        ok = True
        for rel, text in files.items():
            p = HERE / rel
            if not p.exists() or p.read_text() != text:
                ok = False
                print(f"DRIFT: {rel}")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    (HERE / "RH").mkdir(exist_ok=True)
    for rel, text in files.items():
        (HERE / rel).write_text(text)
    print(f"assembled RH library: {len(mods)} modules ({', '.join(mods)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
