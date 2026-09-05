# BG frontier, consolidated + corrected (2026-09-04)

Cross-checking the full corpus with the AXLE-inspired tooling surfaced a **materially wrong
frontier framing** in some file comments (they call `phi_le_one` an unproven "capstone"). The
actual state: the *per-branch* half of classical Conjecture 1 is CLOSED — two independent ways —
and the H2 bridge carrying it into `per(L)/∏deg` is unconditional. The SOLE open half is the
tree-level extremality **assembly** (`Hnorm` + `Hdom`). `conjecture1_proved = False`.

## Half 1 — per-branch ceiling into `per(L)/∏deg`: CLOSED

| Piece | Statement | Status | Where |
|---|---|---|---|
| Classical potential route | `phi_le_one : logPhi b ≤ 0` | **PROVEN, unconditional** | `PotentialFinal.lean:49` (StarBound→DeficitNonneg→ValidPotentialPlain→phi_le_one, all `:=`, no sorry) |
| Additive-subaction route | `bg_ceiling : ∀ b, bell b ≤ 0` | **PROVEN, unconditional** (verified both trust halves 2026-09-04) | `BGSCLSubactionDispatch` via `isSubaction_ρwit` |
| H2 bridge (real graph) | `per(L(G_T))/∏deg = Ztot(litHub …)`, acyclicity discharged | **PROVEN, unconditional** | `BridgeStep4j` (`aGraph_realize_isAcyclic`, `pi_litHub'`, `amplitude_bridge_real'`) |
| Per-branch amplitude bound | `Ztot_litRealize_le_tie : Ztot(litRealize b) ≤ rhoB^(Vb b)` | **PROVEN** (from `phi_le_one`) | `BridgeStep4l:59` |

So: grafting ANY single branch `b` into the classical Brualdi–Goldwasser invariant yields amplitude
`≤ rhoB^(Vb b)` (the tie factor), as a closed theorem. Two independent proofs of the master
inequality (`logPhi` potential route AND `bell` subaction route) — robust.

**Note for maintainers:** the comments in `BridgeStep4k/4l` ("`phi_le_one` … CI-green but not proved",
"assumed from R3 master inequality") are STALE. `PotentialFinal.phi_le_one` discharges it
unconditionally. Worth a comment fix so the frontier isn't misread as open here.

## Half 2 — tree-level extremality assembly: THE open frontier

`R47TopCapstoneFixedN` is conditional on exactly two hypotheses, both genuinely open:

- **`Hnorm`** `: ∀ t, ∃ s, Balanced s ∧ Capped s ∧ stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)`
  — floor = the tree→hub reduction. Schema **proven** (`treeToHub_of_rewrite`, `R47R7TreeToHub.lean`,
  no sorry): a monotone, strictly-decreasing, progressing rewrite ⟹ every tree dominated by a
  hub-backbone. Isolates 3 obligations for the concrete Kelmans rewrite `R`: (R-mono) `Aobj`
  non-decreasing [the hard Kelmans node], (R-meas) decreasing measure [vertex budget], (R-prog)
  non-hub-form ⟹ a move exists. = the parallel session's **Obligation A** lane.
- **`Hdom`** `: ∀ s, Balanced s → Capped s → (merge-normal) → Aobj (backboneU s) ≤ Aobj (tie (stateSize s))`
  — merge layer / monotonicity / rooting all **proven** (`chain_to_normalForm`, `step_mono`,
  `rooting_identity`, arm-rate optimality, (2,2) tiebreak). Open core: multi-hub-stuck domination.

## The Telperion-shaped backing is GREEN (Kelmans all-nonneg certs)

`proof/verification/kelmans_vertex_budget.py`, reconfirmed 2026-09-04:
- `certify_two_hub_theorem` → **6 cells** (receiver load cA∈{0..5}): `pi(T) − pi(S2)`, after the
  shift `pA=1+x, pB=1+y`, is a rational function with an **all-nonnegative-coefficient numerator +
  strictly positive constant over a positive denominator** — a Positivstellensatz/Handelman witness,
  directly `nlinarith`/`polyrith`-liftable to Lean.
- `certify_assisted_merge_theorem` → **6 cells**, same all-nonneg shape (borrow-then-merge strictly
  raises `pi`; dissolves the two-hub stuck obstruction).
- `verify_two_hub_grid` → **1346-case** exact-grid domination cross-check.

These are the exact kernel-portable content for `Hdom`'s hardest node. **HONEST CAVEAT:** the
*m*-hub general case is NAMED-OPEN (the module reframes it as the *environment* version of two local
merge rules; 3-/4-hub probes pass with margins growing in m, ~9%/hub, but that is evidence, not proof).

## Recommended next brick (coordination-gated)

Port `certify_two_hub_theorem` (6 cells) to a kernel-verified Lean atom via Telperion (all-nonneg →
`nlinarith`), as the first verified brick on `Hdom`'s multi-hub node. **This touches the R47 tree that
the `bg/lean-tree-to-hub` lane owns** — coordinate before pushing (per the collision-guard). The
schema side (`treeToHub_of_rewrite`) is already proven; the value is discharging (R-mono)/(R-meas)
for the concrete Kelmans rewrite using these certs.
