"""The telescoping-closure primitive, compile-gated + demonstrated.

Emits the reusable rose-tree telescoping lemma (RTree.telescope: per-node
super-solution ⟹ telescoped global bound) and a worked instantiation that
CLOSES with an explicit potential, so the gate verifies both the primitive and a
real use of it.

Demonstration: local ≡ -1 (each node costs 1), P = -(subtree node count).  Then
the super-solution holds with equality, and telescoping gives
Σ_nodes (-1) ≤ P(root) = -(node count) -- exact.  This is the shape the
Brualdi-Goldwasser ledger needs (Σ growth ≤ tax); here P is explicit, there it
is the open crux, but the ASSEMBLY is the same and now reusable.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402
from telperion.telescope import TELESCOPE_LEMMA, TelescopeSpec  # noqa: E402

HERE = Path(__file__).resolve().parent

# A worked instantiation that closes: nodeCount as potential, -1 as local term.
DEMO = """/-- Worked telescoping: local ≡ -1, potential P = -(node count), with the node
    count itself expressed as `sumOver (fun _ => 1)` (real-valued, no ℕ casts).
    The per-node super-solution holds with equality, so telescoping gives the
    global bound `Σ (-1) ≤ -(node count)`. -/
theorem telescope_nodecount (t : RTree) :
    RTree.sumOver (fun _ => (-1 : ℝ)) t ≤ -(RTree.sumOver (fun _ => (1 : ℝ)) t) := by
  refine RTree.telescope (loc := fun _ => (-1 : ℝ))
    (P := fun s => -(RTree.sumOver (fun _ => (1 : ℝ)) s)) ?_ t
  intro cs
  simp only [RTree.sumOver]
  have key : ∀ l : List RTree,
      (l.map (fun s => -(RTree.sumOver (fun _ => (1 : ℝ)) s))).sum
        = -((l.map (RTree.sumOver (fun _ => (1 : ℝ)))).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [key]
  linarith
"""


def _spec() -> TelescopeSpec:
    # exact-engine dual of the demo: local=-1, P=-count, obligation slack = 0.
    # represent a "class" as an integer child-count; children each count 1 here.
    return TelescopeSpec(
        name="nodecount",
        classes=list(range(0, 6)),                       # node with r children
        local_of=lambda r: sp.Integer(-1),
        potential_node_of=lambda r: sp.Integer(-(1 + r)),  # -(1 + r children of count 1)
        potential_children_of=lambda r: [sp.Integer(-1)] * r,
    )


def build():
    emitter = CustomAssemblyEmitter(
        statement_template="«lemma»\n«demo»«branches»",
        branch_template="",
        fills=lambda fam: {"lemma": TELESCOPE_LEMMA, "demo": DEMO},
        branch_fills=lambda inst: {},
        theorems=1,   # the worked instantiation (the lemma is prelude infrastructure)
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "Telescope")),
                [emitter], _validation(), file_name="Telescope.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="Telescope", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "telescope_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def telescopes():
        spec = _spec()
        # every super-solution obligation holds (slack >= 0) -- the dual of the
        # Lean proof; and here with equality (slack == 0).
        for c, slack in spec.obligations():
            assert slack == 0, (c, slack)
        assert spec.check()

    return ValidationReport.from_asserts([("nodecount_telescopes", telescopes)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"Telescope: RTree.telescope lemma + worked instantiation, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
