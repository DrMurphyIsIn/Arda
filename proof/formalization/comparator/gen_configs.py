"""Generate openai/ten-proofs Comparator configs for the Brualdi-Goldwasser
anchor theorems, reusing the Telperion Comparator bridge (telperion.comparator).

These are the same three theorems AxiomGuard.lean guards -- the sorry-free,
axiom-clean core of the formalization:

  * R3Cert.Step3.conjecture1_of_layers  -- the R7' top capstone (conditional on
    the two still-open layers Hnorm/Hdom); verifying it verifies its whole cone.
  * R3Cert.phi_le_one                    -- the Phi <= 1 analytic crux.
  * R3Cert.CappedJointConfig.gstep_le_one_achievable -- the g-step / master ineq crux.

SELF-CHECK mode (challenge_module == solution_module): unlike the bernoulli
example, the BG theorems ARE the artifact -- there is no independent way to
re-state the capstone (its statement is *about* R3Cert's tree/hub structures), so
an independent challenge module is not meaningful here.  What Comparator adds over
the existing `#print axioms` AxiomGuard is therefore:

  1. an EXPORT-based, machine-checked axiom whitelist (forbids native_decide's
     ofReduceBool etc., not just sorryAx), and
  2. an INDEPENDENT second kernel -- nanoda (a separate Rust reimplementation of
     the Lean kernel) re-checks the exported proof, so a soundness bug would have
     to fool two independently-written kernels.

Run:  python3 comparator/gen_configs.py   (from proof/formalization/)
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
# telperion lives in the same monorepo (telperion/src); reuse its bridge.
sys.path.insert(0, str(HERE.parents[2] / "telperion" / "src"))

from telperion.comparator import (  # noqa: E402
    CLEAN_AXIOMS, challenge_config, write_challenge_config,
)

# (module that declares/exposes the theorem, fully-qualified theorem name, config stem)
ANCHORS = [
    ("R3Cert.R47TopCapstone", "R3Cert.Step3.conjecture1_of_layers", "conjecture1_of_layers"),
    ("R3Cert.PotentialFinal", "R3Cert.phi_le_one", "phi_le_one"),
    ("R3Cert.CappedJointClosure",
     "R3Cert.CappedJointConfig.gstep_le_one_achievable", "gstep_le_one_achievable"),
]


def main() -> int:
    for module, theorem, stem in ANCHORS:
        cfg = challenge_config(
            challenge_module=module,      # self-check: the theorem IS the reference
            solution_module=module,
            theorem_names=[theorem],
            permitted_axioms=CLEAN_AXIOMS,   # [propext, Quot.sound, Classical.choice]
            enable_nanoda=True,              # replay through the 2nd (nanoda) kernel
        )
        path = write_challenge_config(HERE / f"{stem}.comparator.json", cfg)
        print(f"wrote {path.name}: {theorem}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
