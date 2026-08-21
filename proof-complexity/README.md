# Proof complexity — the P-vs-NP certificate ladder

The repository's third research arc (alongside the Brualdi–Goldwasser campaign
in [`proof/`](../proof/) and the [Telperion](../telperion/) engine): a program
of **kernel-checked lower bounds in proof complexity**, climbing a ladder of
progressively harder systems with the same discipline as the BG campaign —
exact-arithmetic validation first, then Lean theorems whose only trusted
component is the kernel. `p_vs_np_proved = False`, permanently implied; each
rung is a certified formalization of a *known* lower bound, and the novelty
claims live in the formalization, not the mathematics.

This page is the front door and index. The artifacts currently live inside the
Telperion tree (they grew out of it and share its pinned Lean toolchain);
nothing here is a second copy — every row links to the single source.

## The rungs

| Rung | Result | Status | Write-up / code | Lean (kernel-checked) |
|---|---|---|---|---|
| **Knapsack (Grigoriev 2001)** | Symbolic-*n* SOS degree lower bound: the pseudoexpectation `E[x_S] = (r)_{\|S\|}/(n)_{\|S\|}` is a valid dual witness for `{xᵢ² = xᵢ, Σxᵢ = n/2}` for **every odd n and every degree simultaneously** — via a rank-one collapse of the harmonic blocks, `g_k = ∏(n−2j)/(2(n−2j−1))` | **Discharged** — 51 theorems, axioms clean; scalar layer + the d=4 Gram bridge (35 emitted identities); the harmonic-completeness layer is Python-pinned, stated honestly | [`WRITEUP.md`](../telperion/examples/knapsack_sos/WRITEUP.md) (the pipeline paper) · [`README.md`](../telperion/examples/knapsack_sos/README.md) · `knapsack_pseudoexpectation.py` | [`KnapsackSOS.lean`](../telperion/examples/g1_floors/lean/KnapsackSOS.lean), [`SumEqProd.lean`](../telperion/examples/g1_floors/lean/SumEqProd.lean), [`BridgeD4.lean`](../telperion/examples/g1_floors/lean/BridgeD4.lean) |
| **3XOR (Grigoriev / Schoenebeck)** | Per-instance certified SOS lower-bound machinery: closure-consistency ⟹ block-rank-one PSD (a GF(2) class-rank-1 consistency argument), with **Tseitin on the Petersen graph** (refutation width exactly 6) as the canonical fully-certified instance | Structure theorem kernel-checked (abstract partially-multiplicative-kernel PSD theorem); Petersen instance fully kernel-certified; the asymptotic expansion layer is not yet formalized | `xor3_pseudoexpectation.py`, `gen_petersen_cert.py` (same directory) | [`Xor3Structure.lean`](../telperion/examples/g1_floors/lean/Xor3Structure.lean), [`PetersenCertificate.lean`](../telperion/examples/g1_floors/lean/PetersenCertificate.lean) |
| **Next (planned)** | Duality layer; LRS; a generic 3XOR instance emitter; planted clique (W2) | open | — | — |

## What fed back into the engine

The arc crystallized three reusable Telperion emitter shapes (all
drift-gated production examples now):

- [`finite_decide`](../telperion/examples/finite_decide/) — guarded decidable
  facts over ℕ-bitmask/sign tables, closed by kernel `decide` (lesson learned
  the hard way: ℚ does **not** kernel-reduce; state tables in ℕ/ℤ and cast);
- [`fwd_telescope`](../telperion/examples/fwd_telescope/) — forward-difference
  telescoping (the W2 prover): a whole Lean induction certified by one
  polynomial contiguous relation;
- [`rational_identity`](../telperion/examples/rational_identity/) — rational
  function identities on a ray (the Gram-bridge shapes).

## Why the Lean lives where it does

The proof-complexity theorems compile inside the
[`g1_floors`](../telperion/examples/g1_floors/lean/) Lean package — originally
a BG artifact — because it is the repository's standalone pinned
Lean + Mathlib shell, and the CI compile gate already covers it. That is a
pragmatic co-location, not a conceptual one; if the arc keeps growing it
should get its own lake package (tracked as future cleanup, deliberately not
done while the formalization sessions are active in those files).

## Honest status

See [`PUBLICATION_LEDGER.md`](../PUBLICATION_LEDGER.md) rows 8–9 for the
conservative novelty positioning: the mathematics is Grigoriev / Laurent /
Kurpisz–Leppänen–Mastrolilli (knapsack) and Grigoriev / Schoenebeck (3XOR);
what is claimed is the certified pipeline and the machine-checked
symbolic-*n* statement — believed to be the first kernel-checked *asymptotic*
proof-complexity lower bound, pending a formalization-literature check.
