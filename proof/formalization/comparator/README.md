# Comparator verification of the Brualdi–Goldwasser anchors

Independent re-verification of the formalization's sorry-free, axiom-clean core by
the [openai/ten-proofs](https://github.com/openai/ten-proofs)
**[Comparator](https://github.com/leanprover/comparator)** — the same machinery
now wired into Telperion (`telperion/examples/bernoulli/lean`), pointed at the real
BG proofs.

## What it adds over `lake build` + AxiomGuard

`lake build` says the Lean kernel accepts the proofs; `AxiomGuard.lean` greps
`#print axioms` for `sorryAx`. Comparator adds, per anchor theorem:

1. an **export-based, machine-checked axiom whitelist**
   `[propext, Quot.sound, Classical.choice]` — stronger than a grep (also forbids
   e.g. `native_decide`'s `ofReduceBool`); and
2. an **independent second kernel** — [nanoda](https://github.com/ammkrn/nanoda_lib),
   a separate Rust reimplementation of the Lean kernel, re-checks the exported
   proof. A soundness bug would have to fool **two independently-written kernels**.

## The three anchors (= AxiomGuard's)

| config | theorem | role |
|---|---|---|
| `conjecture1_of_layers.comparator.json` | `R3Cert.Step3.conjecture1_of_layers` | R7' top capstone (**conditional** on the two still-open layers Hnorm/Hdom) |
| `phi_le_one.comparator.json` | `R3Cert.phi_le_one` | the Φ ≤ 1 analytic crux |
| `gstep_le_one_achievable.comparator.json` | `R3Cert.CappedJointConfig.gstep_le_one_achievable` | the g-step / master-inequality crux |

## Self-check mode (challenge == solution)

Unlike the bernoulli example, the BG theorems **are** the artifact — there is no
independent way to *re-state* the capstone (its statement is *about* R3Cert's
tree/hub structures), so an independent challenge module is not meaningful. Each
config therefore sets `challenge_module == solution_module`: the statement-identity
check is trivial, but the **axiom whitelist and the two-kernel replay are real
independent verification**. Statement integrity is separately assured by human
review and by the anchors being the named capstone / cruxes.

## Scope honesty

Comparator re-verifies what is **already proved**: the anchors are kernel-clean and
`conjecture1_of_layers` is the *conditional* reduction. It does **not** close the
two open layers **Hnorm** and **Hdom** — those remain research-open (full Hnorm
needs the {4,5}-arm-rate pinning, Capped establishment, tree→hub domination, and
multi-hub extremality). Comparator confirms the reduction and the cruxes are sound;
it does not manufacture the missing halves.

## Regenerate / run

```sh
python3 comparator/gen_configs.py            # regenerate the 3 configs via the telperion bridge
# CI (.github/workflows/proof-comparator.yml) builds R3Cert + comparator + nanoda, then:
lake env comparator comparator/phi_le_one.comparator.json
```

The capstone's proof cone is large; if its export exhausts the runner the CI reports
it per-anchor (smaller cruxes first) rather than aborting — the Lean kernel +
AxiomGuard verification of that anchor still stands regardless.
