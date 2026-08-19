# Applying evolve to the remaining Brualdi–Goldwasser gaps — scoping result

**Request:** apply the `telperion.evolve` subsystem to all remaining unproven parts of BG.
**Method:** map every OPEN / VERIFIED-not-proven piece in `PROOF_ASSEMBLY.md` against what
evolve can actually search — a **finite grid of Pólya-lowerable rational-function
inequalities**, scored by the exact `hunt → certify → parsimony → lake build` cascade,
with tunable parameters `(ratio_src, s0, lift_max, multiplier degree, subdivision)`.
`conjecture1_proved = False` (unchanged; nothing here proves or freezes anything).

## What evolve can and cannot express

Evolve certifies a **fixed, finite family of instances**. Its genuine power is: *given a
one-/few-variable rational inequality that holds, find the Pólya multiplier / subdivision /
crossover that certifies it in exact arithmetic and goes kernel-green.* It has **no**
representation for: a statement quantified over *all n* / *all trees*; a recursive per-tree
quantity; a structural induction; or an arithmetic (p-adic) gap.

## The remaining pieces, classified

| Open / verified piece (PROOF_ASSEMBLY) | Shape | Evolve target? | Why |
|---|---|---|---|
| **R1 branch-induction wiring** (`g_bound<γ` + children-master ⟹ parent-master) | Lean structural induction | **No** | no genome; it is tree-induction wiring, defeating the `C^{j'-1}` blow-up |
| **R1 leaf-child case** (`F_B ≤ 486/529`, `arm_monotone`) | ∀ blocks-with-leaf-child; `F_B` recursive | **No** | infinite combinatorial family; all-n proof is a decomposition (`F_leaf · F_other`, `F_other ≤ 1`), not a fixed grid |
| **R2 multi-hub maximality** ("DN is the max at each n") | competitor extremality over trees | **No** | combinatorial optimization, not a parameterized inequality |
| **Irreducible-family bound** ("irreducible ⇒ Φ¹¹≤0.386") | the **collective crux** | **No — provably** | the per-node super-solution **fails** on the relaxed domain (non-local coupling) — i.e. no local/Pólya/SOS certificate exists; a Perron/transfer-decay statement |
| **Per-root reduction** (verified n≤10) | restatement / direct argument | **No** | not a parameter search |
| **23-gate-strictness lemma** (the live lead, `gate_strictness`) | arithmetic (23-adic) lower bound | **No** | archimedean-vs-arithmetic (PROOF_STATUS dead-end #2); invisible to a smooth/Pólya certificate |

The single-/few-variable rational inequalities that **are** evolve-shaped — the near-star
tail `Φ¹¹(N(0,s))≤1 ∀s`, the g-lemma's two rational leaves (`μ*<1/3`, `W(4/3)¹¹<γ`), the
interior-max single-point reduction — are **already PROVEN** (and Lean-green). Evolve has
nothing to add to them beyond re-derivation.

## Conclusion

**No remaining OPEN gap on the current BG frontier is a valid evolve target.** The frontier
is exactly the two things evolve was designed *not* to be: (a) Lean structural-induction
wiring (R1/R2), and (b) the collective/arithmetic crux (ruled out for local certificates by
a *reasoned* dead-end, and firewalled out of evolve's own design as a compute sink). The
evolve-shaped rational inequalities are already closed.

This is the honest payoff of scoping before running: pointing evolve at these gaps would
have burned compute and produced nothing, and reporting "applied evolve to the BG proof"
would have been an overclaim.

## Where evolve *is* valid (demonstrated)

Evolve's live-verified capability is certifying the evolve-shaped BG sub-lemmas: from a
**failing** seed it re-discovers the near-star-tail unimodal certificate with
`certify_rate = 1.0` (structured arm), and the LLM arm proposes novel whitelisted ratios
judged by the cascade. So the valid role for evolve in this program is a **certifier /
parsimony tool for future single-/few-variable rational sub-lemmas** as they arise — not a
prover of the current structural frontier.

**The real next step for BG is the R1 branch-induction wiring and R2 multi-hub maximality —
Lean structural work, not an evolve task.** `conjecture1_proved = False`.
