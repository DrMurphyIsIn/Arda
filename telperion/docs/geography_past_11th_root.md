# Geography of the Brualdi–Goldwasser Problem, Past the 11th Root

A structural map of the whole terrain, written after the correction of 2026-08-16 (the raw-ρ vs
rooted-Φ conflation). The organizing fact: **there are two different quantities on trees, with opposite
extremal structures, and the 11th-root benchmark is what selects between them.**

---

## 0. The fork — two quantities

| | raw `ρ(T)` | BG `Φ(T)` |
|---|---|---|
| definition | `per(L)/∏deg` | rooted branch model, **max over roots** |
| invariance | root-invariant (a matrix function) | rooted quantity; the invariant is `max_root` |
| formula | `Σ_matchings ∏_{matched} 1/deg` (monomer–dimer) | `a₁₁·(1+zS)¹¹·∏children`, `z=3/(3d+cr)` |
| rewards | **low degree** → balance | **rooted concentration** → one deep hub |
| maximizer / n | **balanced caterpillar** (e.g. `(3,4,3)` at n=23) | **near-star spider** `N(0,s)` |
| bound | grows without bound | **≤ 1** (the conjecture) |

Verified fork (n=23, two independent methods): `ρ(3,4,3)=951345/8192 > ρ(N(0,11))=59049/512`, but
`Φ(3,4,3)=0.63 < Φ(N(0,11))=0.76`. **The rankings are opposite.** BG is about the right-hand column.

> **Correction on record.** The session's competitor-extremality tooling (`matching_free_energy`,
> `CompetitorExtremalityCertificate`, `tree_search`, `IslandModel`) all compute **raw ρ** — the
> monomer–dimer problem, *not* BG. Raw-ρ "competitor extremality" (near-star maximal) is **false**
> (caterpillars win). BG competitor extremality (near-star maximizes rooted Φ) is **correct** but was
> only verified exhaustively n=7,9,11,13 in the right model.

---

## 1. The 11th root itself — the benchmark

`ρ_B = (621/64)^{1/11}`, i.e. `ρ_B¹¹ = 621/64 = 3³·23/2⁶`. This is the **per-branch** benchmark in the
rooted model; `Φ` is the branch value measured against it. The `11` is the vertex count of the extremal
tie; the `1/11` root clears it to the integer identity below.

The near-star's raw ratio is `ρ(N(0,s)) = (4/3)(3/2)^s` — **gauge-flat** (a pure geometric). All curvature
and all arithmetic live in the benchmark factor `B = Φ¹¹/ρ¹¹`, not in the Laplacian.

---

## 2. Past the 11th root — the arithmetic core

- **The tie.** Near-star rooted at the hub, `s=5`: `Φ¹¹ = 1`, the integer identity `64·243·23 = 621·576 =
  357696`. The 6 near-star ties (`c+k=5`, 11 vertices) form the equality variety.
- **The exceptional prime 23.** `621 = 3³·23`; it enters as `23²` per arm (`ρ_B²² = 3⁶·23²/2¹²`, one arm =
  2 vertices). 23 is *not* a growth-rate prime — those are **Pell** (`3,7,17,41,99,…`, from leg length).
  23 is the benchmark's characteristic prime, fixed by the (permanent, leg-2, 11-vertex) resonance.
- **Why it must be arithmetic.** The continuous relaxation of the near-star crossing exceeds 1 between
  integers (`≈1.0005`); the integer points straddle the dip. No smooth certificate can see this — the
  proof is 23-adic / integral.

---

## 3. The near-star's internal structure — the gauge tower

`Φ¹¹ = φ_arm^{#arms} · L`, with the **arm as the unit**:

- `φ_arm = Φ¹¹(one arm) = 486/529 = 2·3⁵/23²`; the near-star step-constant `529/486 = 1/φ_arm`.
- The **curvature quadratic** `q(s) = (s+1)(4s+7) = 4s²+11s+7` is a Laplacian 2×2 minor (degree × coupling).
- **Two ends of the tower** (dual):
  - *derivation* (finite differences): `q → 8s+15 → 8 → 0` terminates at jerk = 0 → unimodality (unique crossing).
  - *integration* (product): `1−1/q(t)` telescopes via shifted potentials `t+1, 4t+3` to `3(s+1)/(4s+3)` →
    closed form `R(s)` → resonance. They meet at the single integer identity.
- **Leg-length lemma** (exact): per-vertex leg total `t_L^{1/L}` (`t_L = P_L/2^{L-1}`, Pell) is uniquely
  maximized at `L=2` (`√(3/2)`) — legs "want" length 2.

---

## 4. Why the two quantities have opposite extremals — the theory

`Φ` is a **rooted branch** quantity: it views the tree from one vantage (the root), so the value is a
product of branch-contributions, maximized when *all* branches hang off a single deep hub — the near-star.
`ρ` is a **global matching sum** with no vantage; the `1/deg` weights reward many low-degree sites, i.e.
distributed balance — the caterpillar.

The benchmark `ρ_B` is **calibrated to the near-star-at-hub** (that is where `Φ=1`), so it re-weights the
raw matching sum to reward rooted concentration. The 11th-root benchmark is precisely the operator that
turns the caterpillar-extremal (raw ρ) into the spider-extremal (Φ). **Rooted concentration vs global
balance is a duality; the benchmark selects the rooted branch.**

---

## 5. The matrix-function / quantum-statistics layer — and its BG caveat

For a tree, every immanant is a matching sum reweighted by the character on involutions:
`imm_λ(L) = Σ_matchings χ_λ(σ_M) ∏_{unmatched} deg`. So **det = fermion** (signed, collapses to
spanning-tree count = 1), **per = boson** (unsigned, the hard end), **immanants = parastatistics**.
Permanental dominance `per(L) ≥ imm_λ(L)/χ_λ(1)` is **proved** for tree/forest Laplacians.

**Caveat.** This entire layer is about the **permanent / raw ρ**, whose extremal is the *caterpillar* —
so it is directly about the monomer–dimer problem, and only *indirectly* about BG (which is the rooted Φ).
The earlier "bosonic maximizer = BG maximizer" identification was part of the conflation and is withdrawn.

---

## 6. Proof-status map

| Claim | Status |
|---|---|
| Near-star family `Φ ≤ 1`, tie at `c+k=5` (23-adic) | **PROVED** (arithmetic, exact) |
| Permanent-of-Laplacian bridge (rec = per(L) elimination) | **PROVED** (Lean, acyclicity) |
| `phi_le_one` in the rooted Branch model | **PROVED** (Lean, unconditional) |
| Permanental dominance for tree/forest Laplacians | **PROVED** (this session; likely known) |
| Leg-length lemma (`t_L^{1/L}` max at L=2) | **PROVED** (exact) |
| **BG competitor extremality** (near-star maximizes rooted Φ over ALL trees) | **OPEN** — verified only n≤13; tooling must move from raw ρ to rooted Φ |
| Lieb permanental dominance (general PSD) | **OPEN** (untouched) |
| raw-ρ competitor extremality (near-star maximal) | **FALSE** (caterpillar wins) |

---

## 7. What to do next (honest)

1. **Re-point the tooling at rooted Φ (max over roots).** `matching_free_energy` and the search/island
   infrastructure measure raw ρ; BG needs the rooted branch value. Rebuild competitor-extremality on
   `max_root Φ` and re-run the at-scale mapping — the near-star should be the peak there (unlike raw ρ).
2. **The open crux is now sharp**: prove the near-star maximizes the rooted branch Φ over all trees, with
   the arithmetic endgame at the tie. The rooted-concentration theory (§4) is the mechanism to formalize.

`conjecture1_proved = False`.
