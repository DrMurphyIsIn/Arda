# Palomar sources for the Brualdi–Goldwasser work (2026-09-08)

Curated from the Palomar registry for the BG front (tree permanent-ratio conjecture
`Φ¹¹(T) ≤ 1`, `per(L(T))` cavity recursion, graph spectra, interlacing / log-concavity,
SOS/PSD positivity). Mined + maintained by `telperion palomar-mine --topic bg`. These are
leads — build + CI-verify; a registry entry is not a certificate.

## Permanent / matching (the BG cavity core — candidate NEW emitter shape)
- **`PALOMAR-2026-08-27-000019`** — `yuhangshi888/sun-cotangent-permanent-counterexample-lean`:
  exact evaluation of a normalized 14×14 cotangent **permanent** — a concrete permanent
  computation in Lean (11C20/15A15). Directly the `per(L)` object of the BG program.
- **`PALOMAR-2026-08-29-000006`** — `nimaanari/formalization-beyond-bethe`: **permanent**
  computation/approximation (Bethe approximation, 15A15/68W25) — permanent lower/upper bound
  machinery relevant to `per(L(T))` estimates.
- **`PALOMAR-2026-09-02-000010`** — Kőnig–Egerváry theorem on **matchings** and vertex covers
  in bipartite graphs (min–max duality) + Gallai identities. Matching-number machinery underlying
  matching-sum = `per(L)` for trees (the H1 bridge).
- **`PALOMAR-2026-08-31-000020`** — Friendship Windmill Structure Theorem (matching/spectral).

## Graph spectra / matrix inequalities (backs the linear-algebra layer)
- **`PALOMAR-2026-09-07-000002`** — Bollobás–Nikiforov conjecture: **Laplacian/adjacency
  eigenvalue** inequalities with a positive-semidefinite matrix theorem (05C50/15B48/15A18).
  Kin to the `RHLinalg` eigenvalue/PSD prelude; reusable for graph-spectral bounds.
- **`PALOMAR-2026-08-26-000001`** — Graham–Pollak theorem (edge partitions / addressing;
  a classic algebraic graph inequality, 05C50/15A03).
- **`PALOMAR-2026-09-02-000008`** — signed-circulant `C_n(1,2)` minimum disproof, at the
  matrix/eigenvalue level (SOS-shaped, 05C22/15A18).
- **`PALOMAR-2026-08-29-000017`** — ordered adjacency spectrum of prime-cover graphs.

## Riemann–Roch / chip-firing for graphs (the BG "tree" combinatorics kin)
- **`PALOMAR-2026-09-02-000013`** — Baker–Norine **Riemann–Roch for finite graphs** (chip-firing,
  05C57/14T20). The divisor/rank theory on graphs — adjacent to tree/spanning combinatorics.
- **`PALOMAR-2026-08-19-000003`** — Regts–Sevenster (graph-parameter edge-connection rank).

## Positivity / SOS backing (Telperion emitter families)
- **`PALOMAR-2026-08-20-000002`** — Low-Rank Univariate SOS (Legat–Yuan–Parrilo) → SOS/PSD emitters.
- **`PALOMAR-2026-09-02-000014`** — signature product rule (Sylvester inertia over ordered fields).

## Actions
1. Highest value: mine the two **permanent** entries for a `per(L)` / cavity-recursion emitter
   shape (the BG core `rational_identity` + cavity chain) — a candidate NEW shape.
2. Reuse Bollobás–Nikiforov + Graham–Pollak as graph-spectral / PSD prelude leads.
3. Kőnig–Egerváry underwrites the matching-sum = `per(L)` bridge for trees.
