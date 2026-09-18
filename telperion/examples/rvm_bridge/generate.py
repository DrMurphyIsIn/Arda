"""E6 RvM bridge island -- drift check (no generation; the Lean is hand-written).

    python examples/rvm_bridge/generate.py --check    # drift check (the only mode)
    python examples/rvm_bridge/generate.py            # same as --check

The island `examples/rvm_bridge/lean/` discharges the MIRRORMERE residual
`MM_rvm_unbounded_mean_density` from Anthropic's zeta-23-lean (Alpoege--Furman
Theorem A + the unconditional Riemann--von Mangoldt main clause), on its own
toolchain island (Lean v4.33.0-rc2 / Mathlib 51e6992e, the zeta-23-lean pin).

Nothing is emitted, so "regeneration" is the containment invariant the registry's
grant gate relies on:

  1. `lean/E6Bridge.lean` contains, verbatim modulo whitespace/comments and the
     trailing `:= by sorry`, the node statement line of
     `missions/mirrormere/lean/Statements/MM_rvm_unbounded_mean_density.lean`
     (theorem NAME and binder-free form must match exactly);
  2. the two mirrored definitions (`RvMUnboundedMeanDensity`, `zetaOrdinates`)
     match `missions/mirrormere/lean/Statements/MMDefs.lean` verbatim modulo
     whitespace/comments;
  3. the island's toolchain pin is the zeta-23-lean pin recorded in
     `lean/lakefile.toml` (Lean v4.33.0-rc2);
  4. (second bridge, 2026-09-17) `lean/E6Bridge2.lean` contains the node statement
     of `missions/rh/lean/Statements/RH_rvm_unconditional.lean` verbatim, and its
     mirrored `RvMCount.zetaZeroCount` matches `missions/rh/lean/Statements/RHDefs.lean`.

Any drift in the registry statement or definitions fails this check, so the
island cannot silently stop matching the node it discharges.

HONEST SCOPE: the discharged statement is a classical (Selberg-type) consequence
of a positive proportion of zeros on the critical line; it is not RH and does
not approach it.  conjecture1_proved = False.
"""
import argparse
import re
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_TELPERION = _HERE.parents[1]
_ISLAND = _HERE / "lean"
_BRIDGE = _ISLAND / "E6Bridge.lean"
_TOOLCHAIN = _ISLAND / "lean-toolchain"
_NODE = _TELPERION / "missions" / "mirrormere" / "lean" / "Statements" / "MM_rvm_unbounded_mean_density.lean"
_MMDEFS = _TELPERION / "missions" / "mirrormere" / "lean" / "Statements" / "MMDefs.lean"
_BRIDGE2 = _ISLAND / "E6Bridge2.lean"
_NODE2 = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RH_rvm_unconditional.lean"
_RHDEFS = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RHDefs.lean"
_DEF_NAMES2 = ("zetaZeroCount",)

_EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.0-rc2"
_DEF_NAMES = ("RvMUnboundedMeanDensity", "zetaOrdinates")


def _strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def _normalize(text: str) -> str:
    return re.sub(r"\s+", " ", _strip_comments(text)).strip()


def _node_statement(node_text: str, node_path: Path = _NODE) -> str:
    """The `theorem NAME : BODY` of the node file, with the `:= by sorry` tail dropped."""
    body = _normalize(node_text)
    m = re.search(r"(theorem\s+\S+\s*:.*?)\s*:=\s*by\s+sorry", body)
    if not m:
        raise SystemExit(f"cannot find the node theorem in {node_path}")
    return m.group(1)


def _def_block(text: str, name: str) -> str:
    """The normalized `def NAME ... :=` block up to the next top-level declaration."""
    body = _strip_comments(text)
    m = re.search(rf"\bdef\s+{re.escape(name)}\b.*?(?=\n(?:def|theorem|lemma|end|namespace|noncomputable|abbrev|structure|open|section)\b)",
                  body, flags=re.S)
    if not m:
        raise SystemExit(f"cannot find `def {name}` in the source")
    return re.sub(r"\s+", " ", m.group(0)).strip()


def check() -> int:
    failures = []
    bridge = _BRIDGE.read_text(encoding="utf-8")
    bridge_norm = _normalize(bridge)

    # 1. the node statement line, verbatim (name + binder-free form)
    stmt = _node_statement(_NODE.read_text(encoding="utf-8"))
    if stmt not in bridge_norm:
        failures.append(f"node statement not contained verbatim in E6Bridge.lean: {stmt!r}")
    if re.search(r":=\s*by\s+sorry", bridge_norm) or "sorry" in bridge_norm.split():
        failures.append("E6Bridge.lean contains a `sorry`")

    # 2. the two mirrored definitions
    mmdefs = _MMDEFS.read_text(encoding="utf-8")
    for name in _DEF_NAMES:
        want = _def_block(mmdefs, name)
        have = _def_block(bridge, name)
        if want != have:
            failures.append(f"`def {name}` drifted from MMDefs.lean:\n  registry: {want}\n  island:   {have}")

    # 3. the toolchain pin
    tc = _TOOLCHAIN.read_text(encoding="utf-8").strip()
    if tc != _EXPECTED_TOOLCHAIN:
        failures.append(f"lean-toolchain is {tc!r}, expected {_EXPECTED_TOOLCHAIN!r}")

    # 4. the second bridge: the RH node RH_rvm_unconditional + its mirrored definition
    bridge2 = _BRIDGE2.read_text(encoding="utf-8")
    bridge2_norm = _normalize(bridge2)
    stmt2 = _node_statement(_NODE2.read_text(encoding="utf-8"), _NODE2)
    if stmt2 not in bridge2_norm:
        failures.append(f"node statement not contained verbatim in E6Bridge2.lean: {stmt2!r}")
    if re.search(r":=\s*by\s+sorry", bridge2_norm) or "sorry" in bridge2_norm.split():
        failures.append("E6Bridge2.lean contains a `sorry`")
    rhdefs = _RHDEFS.read_text(encoding="utf-8")
    for name in _DEF_NAMES2:
        want = _def_block(rhdefs, name)
        have = _def_block(bridge2, name)
        if want != have:
            failures.append(f"`def {name}` drifted from RHDefs.lean:\n  registry: {want}\n  island:   {have}")

    if failures:
        print("rvm_bridge drift check FAILED:")
        for f in failures:
            print("  - " + f)
        return 1
    print(f"rvm_bridge: node statement + {len(_DEF_NAMES)} mirrored defs + toolchain pin match "
          f"({_BRIDGE.relative_to(_TELPERION)}); "
          f"RH node statement + {len(_DEF_NAMES2)} mirrored def match "
          f"({_BRIDGE2.relative_to(_TELPERION)})")
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--check", action="store_true", help="drift check (the only mode; default)")
    p.parse_args(argv)
    return check()


if __name__ == "__main__":
    sys.exit(main())
