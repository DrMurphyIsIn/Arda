# Permanental dominance for tree (and forest) Laplacians

**Theorem.** Let `T` be a tree on `n` vertices with Laplacian `L = D − A`, and let `λ ⊢ n` be any
partition. Then the permanent dominates the normalized immanant:

    per(L)  ≥  d_λ(L) := imm_λ(L) / χ_λ(1).

Equivalently, on tree Laplacians the trivial (bosonic) character maximizes the normalized immanant.
This is Lieb's permanental dominance conjecture (open for general positive semidefinite Hermitian
matrices) in the tree-Laplacian case.

## Proof

**Step 1 — Matching expansion.**
For `σ ∈ S_n`, the term `∏_i L_{i,σ(i)}` is nonzero only if `L_{i,σ(i)} ≠ 0` for every `i`, i.e.
`σ(i) ∈ {i} ∪ N(i)`. Each cycle of `σ` is then a closed walk in `T`; since a tree is acyclic, every
cycle has length 1 or 2. Hence the only contributing permutations are **involutions**, each given by a
matching `M ⊆ E(T)` (the 2‑cycles), with the unmatched vertices as fixed points. For such `σ = σ_M`,

    ∏_i L_{i,σ_M(i)}
      = ∏_{v unmatched} L_{vv} · ∏_{(i,j)∈M} L_{ij} L_{ji}
      = ∏_{v unmatched} deg(v) · ∏_{(i,j)∈M} (−1)(−1)
      = w(M),   where  w(M) := ∏_{v unmatched} deg(v) > 0.

Therefore, for **every** `λ`,

    imm_λ(L) = Σ_{matchings M} χ_λ(σ_M) · w(M),        (σ_M has cycle type 2^{|M|} 1^{n−2|M|}).

Taking `λ = (n)` (trivial character, `χ ≡ 1`) gives `per(L) = Σ_M w(M)`.

**Step 2 — Normalized character bound.**
For an irreducible representation `ρ_λ` of `S_n`, `ρ_λ(σ)` is a unitary matrix of finite order, so its
eigenvalues are roots of unity. Its normalized trace is therefore an average of `dim(λ)` roots of
unity, giving

    | χ_λ(σ) / χ_λ(1) |  =  | (1/dim) tr ρ_λ(σ) |  ≤  1     for all σ.

In particular `χ̂_λ(σ_M) := χ_λ(σ_M)/χ_λ(1) ≤ 1`.

**Step 3 — Combine.**
Since `w(M) > 0` and `χ̂_λ(σ_M) ≤ 1` for every matching `M`,

    per(L) − d_λ(L)
      = Σ_M w(M)  −  Σ_M χ̂_λ(σ_M) w(M)
      = Σ_M ( 1 − χ̂_λ(σ_M) ) w(M)
      ≥ 0.                                              ∎

## Remarks

- **Equality.** `per(L) = d_λ(L)` iff `χ̂_λ(σ_M) = 1` for every matching `M` with `w(M) > 0`.
  For `λ = (n)` this is automatic; the gap grows with how far `λ` sits from the trivial character,
  which is exactly the monotone spider→star sweep observed numerically.

- **The proof does not use positive semidefiniteness.** It uses only three combinatorial facts about
  `L`: (i) the off-diagonal support is a **forest** (so the permutation expansion collapses to
  matchings), (ii) the diagonal is nonnegative, (iii) each edge product `L_{ij} L_{ji}` is nonnegative.
  Hence the statement holds verbatim for **forests**, and more generally for any Hermitian matrix whose
  off-diagonal pattern is a forest with nonnegative diagonal and nonnegative edge products. Lieb's PSD
  hypothesis is stronger than needed in this combinatorial regime.

- **Relation to the Brualdi–Goldwasser program.** This identifies the bosonic (permanent) end as the
  dominant one *per parastatistical degree of freedom*, with the near-star spider as the extremal tree —
  the same object at the center of the Brualdi–Goldwasser conjecture, which remains open.

## Machine verification

`telperion`'s `PermanentalDominanceCertificate` checks, for a given `n`: the matching expansion of
`imm_λ(L)` on every tree, the involution character bounds `χ_λ(2^k 1^{n−2k}) ≤ χ_λ(1)` (the finite
witnesses of Step 2), and the termwise nonnegativity of `per − d_λ`. The emitted Lean facts are the
integer character-bound inequalities `χ_λ(involution) ≤ dim(λ)`; the general result follows from these
witnesses plus Steps 1 and 3, which hold for all `n`.
