"""Generate the recursion-closure example: certify -> emit -> write.

    python examples/recursion_closure/generate.py           # write lean/RecursionClosure.lean
    python examples/recursion_closure/generate.py --check    # drift check (no write)

The BG per-hub SCL (single-child-lift) node-decouple ASSEMBLY at a fixed price
μ*.  From the PROVEN tangent-majorant (`bell_node_tangent` of
``proof/formalization/R3Cert/BGSCLInduction.lean``) plus a per-hub ceiling,
conclude the node ceiling:

    nodeVal ≤ childBellSum + tangentBracket + μ*·nodeY   (htan, the proven tangent)
    childBellSum + tangentBracket + μ*·nodeY ≤ cherryVal (hceil, per-hub ceiling)
    ─────────────────────────────────────────────────
    nodeVal ≤ cherryVal

The reusable abstract-real assembly lemma ``recursion_closure_assembly`` is
inlined into the emitted file's prelude, so it is self-contained (only
``import Mathlib``; does NOT import the R3Cert project).

Instances:
* a CONCRETE grounding at price μ* = 1/4 ∈ I = [456/3703, 3/7], with concrete
  rational childBellSum/tangentBracket/nodeY/cherryVal and abstract htan/hceil;
* a TIE grounding where the all-cherry config makes the middle quantity EQUAL
  the cherry ceiling (composes with the `tight_cap_enclosure` tie).

HONEST SCOPE: packages the tangent+ceiling → node-ceiling ASSEMBLY at a fixed
price.  Does NOT re-derive the log-tangent (that is the proven
`bell_node_tangent`) nor prove the all-cherry exchange (structural).
conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


# The `recursion_closure` kind is registered in telperion/certify.py.

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_recursion_closure import (  # noqa: E402
    _INLINE_DEFS,
    RecursionClosureEmitter,
    recursion_closure_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# concrete rational grounding values (see module docstring for the shapes).
_MU = "1/4"
_CB = "1/5"
_TB = "-1/20"
_NY = "1/8"
# tie cherry_val = child_bell + tangent + mu*node_y = 1/5 - 1/20 + 1/4*1/8 = 29/160
_CV_TIE = "29/160"
# non-tie cherry_val strictly above the middle quantity 29/160.
_CV = "1/5"

_SPECS = {
    0: {"mu_star": _MU, "node_val": "1/10", "child_bell": _CB,
        "tangent": _TB, "node_y": _NY, "cherry_val": _CV},
    1: {"mu_star": _MU, "node_val": "1/10", "child_bell": _CB,
        "tangent": _TB, "node_y": _NY, "cherry_val": _CV_TIE},
}
_NAMES = {0: "scl_node_decouple", 1: "scl_node_decouple_tie"}
_OUT = Path(__file__).resolve().parent / "lean" / "RecursionClosure.lean"


def build() -> str:
    fam = recursion_closure_family(
        "RecursionClosure",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("RecursionClosure",), prelude=_INLINE_DEFS),
        [RecursionClosureEmitter()],
        ValidationReport(checks=(("recursion_closure", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: RecursionClosure.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
