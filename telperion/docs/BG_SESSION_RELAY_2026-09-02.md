# Relay to the BG proof session — new Telperion emitter skills (2026-09-02)

**Audience:** the Brualdi–Goldwasser (per(L)/∏deg maximizer) proof session.
**Purpose:** flag which of the 23 emitters shipped in the 2026-09-02 campaign are
usable on the *open BG endgame*, with the BG obligation each discharges and the
invocation recipe. Everything below is on `main` (default branch) of
DrMurphyIsIn/Arda under `telperion/`. `conjecture1_proved = False` throughout —
these are certificate *skills*, not progress on the conjecture.

Trust reminder: every emitter is UNTRUSTED. It emits Lean; the kernel is the sole
arbiter. A wrong certificate is a red `lake build`, never a false theorem. So you
lose nothing by trying one on a BG obligation — worst case it fails to compile.

---

## The two just-closed open fronts (build these into your endgame first)

### 1. `SeparableConvexExtremumEmitter` — `mode="max"` (vertex face)  ← **highest BG value**
This one PARAMETERIZES **your own proven lemma**: `proof/formalization/R3Cert/
VertexLemmaFull.lean` (`glemma_spread` / `glemma_push_to_bound` /
`sum_le_half_length` / `vertex_bound` / `vertex_bound_cons`). The emitter turns the
vertex bound

    Σ φ(xᵢ) ≤ (n−1)·φ(u) + φ(S − (n−1)u)     (convex even-degree-≤6 φ, uniform box)

into a fixed-`n` unrolled `nlinarith` push-chain, with `glemma` replaced by the
concrete convex `φ` you hand it. This is exactly the **spreading-exchange /
leaf-onto-higher-degree** move that appears in the BG competitor-extremality
argument (R7' / hSeam near-case): the extremum of a separable convex objective on a
fixed-sum box sits at a vertex. Where you were hand-rolling that push, you can now
emit it per instance and let the kernel check it.
- `mode="min"` (default) gives the dual homogeneous/Jensen face `n·φ(S/n) ≤ Σφ(xᵢ)`.
- Negative controls baked in: refuses a non-convex φ (max face) and a linear φ.
- Restriction: uniform box, even degree ≤ 6. The general list induction stays in
  the proven Lean (`vertex_bound_cons`); the emitter only unrolls fixed `n`.

### 2. `SymmetricQuadD2Emitter` (kind `symmetric_quad_d2`) — degree-2 moment PSD, symbolic in n
The d=2 sibling of `SymmetricQuadFormEmitter` (d=1). Proves the subset-indexed
knapsack moment form `Q₂(x;n) = Σ_{|S|,|T|≤2} x_S x_T f(n,|S∪T|) ≥ 0` **symbolically
in n** via the three-piece completing-the-square + centered-CS decomposition of
`examples/knapsack_sos/D2_CERTIFICATE.md`:

    Q₂ = (A + f₁s₁ + f₂s₂)² + (n/4(n−1))·(T₂ − s₁²/n) + μ₂·N₂,   μ₂ = n(n−2)/(16(n−3)(n−1))

The completing-the-square assembly is `field_simp; ring` symbolic-in-n; the two
association-scheme leaf facts (`s₁² ≤ n·T₂` centered-CS, and `0 ≤ N₂` the J(n,2)
projection positivity) enter as hypotheses at the SAME altitude as the d=1 emitter's
`X² ≤ n·Q`. **Relevance to BG:** this is the Johnson-scheme / knapsack moment-matrix
PSD engine. If any BG discharge routes through a level-2 moment positivity on the
subset lattice (the association-scheme orbit sums), this is the ready-made cert.

---

## Emitters mapped to standing BG obligations

| BG obligation (from your memory files) | Emitter to try | kind / entry |
|---|---|---|
| `bg_bulk_discharge`: φ_v ≤ F* on an h-box (box-positivity engine) | `PolytopeMaxMonotoneEmitter` (multi-affine corner max, d≤3 verified) + `BilinearCornerBoxEmitter` (worst-corner) | `polytope_max` / `bilinear_corner` |
| box-positivity as Positivstellensatz / Farkas | `HandelmanEmitter`, `ConstrainedSOSEmitter` (Putinar), `ConeFarkasEmitter` | `handelman` / `putinar` / `cone` |
| **621/64 = 27·23** integrality gate (the arithmetic Φ≤1 fact) | `IntegralityGateEmitter` (23-gate = p-adic valuation + finite `decide`) + `PadicValuationEmitter` | `integrality_gate` / `valuation` |
| domination `P/Q ≥ 1` on a multivariate corner | `RecursiveDominationRatioEmitter` | `domination_ratio` |
| near-star unimodal ratio `R(s+1)/R(s)` crosses 1 once | `SecondOrderRecurrenceEmitter` (3-term recurrence, two-step `Nat.le_induction`) + `UnimodalMaxEmitter` + `MonotoneRatioTailEmitter` | `second_order` / `unimodal` / `monotone_tail` |
| competitor extremality / spreading-exchange (R7' hSeam) | **`SeparableConvexExtremumEmitter` `mode="max"`** (above) | `separable_convex` |
| Johnson-scheme / knapsack level-≤2 moment PSD | **`SymmetricQuadD2Emitter`** (above) + `SymmetricQuadFormEmitter` (d=1) | `symmetric_quad_d2` / `symmetric_quad` |
| achievability / value-attained closure | `AchievabilityClosureEmitter` | `achievability` |
| √2 / algebraic-number brackets (e2_two_rhoB crux family) | `AlgebraicBracketEmitter`, `IntervalBracketEmitter` | `algebraic_bracket` / `bracket` |

## How to invoke (recipe)

Each emitter lives in `telperion/src/telperion/emit_<name>.py` and exports
`<Name>Emitter`, `<name>_certificate()`, `<name>_family()`. A worked end-to-end
generate→certify→emit→Lean example sits in `telperion/examples/<name>/` (copy its
`generate.py`). Registered kinds resolve through `certify._SPECIAL_DISPATCH`; the
emitter is passed EXPLICITLY to `emit()` from the example's `generate.py`.

Local kernel check (machine serviced — local builds RESTORED, ~4–40s/module,
mathlib cached):

    cd telperion/examples/<name>/lean
    PATH=$HOME/.elan/bin:$PATH lake exe cache get && lake build

Full emitter reference: `telperion/docs/NEW_EMITTERS_SUMMARY.md` (all 23, one-liners
+ Lean idiom each). README "Certificate shapes" table has the canonical row per
emitter.

## What is NOT covered (don't wait on these)

- The BG *crux itself* (Φ≤1 general-child case) stays open — no emitter closes it;
  these discharge the finite algebraic *islands* around it, not the tree→hub core.
- `mode="max"` is uniform-box + even-degree-≤6 only; a non-uniform or high-degree φ
  still needs the proven `vertex_bound_cons` list induction in Lean directly.
- Transcendental / spectral-radius limits (ρ(A)→1 accumulation) are not
  certificate-shaped; the arithmetic route (23-adic integrality gate) is.
