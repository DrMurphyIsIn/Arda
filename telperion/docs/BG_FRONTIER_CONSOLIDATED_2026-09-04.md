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

## Next brick — DONE (collision-safe leaf): `R47R7KelmansTwoHubCert.lean`

Ported `certify_two_hub_theorem` (6 cells) to kernel-verified Lean atoms
`two_hub_gap_pos_c0..c5` (`R3Cert.Step3`): per receiver load `cA ∈ {0..5}`, the integer-cleared gap
numerator `pi(T)/V^K − pi(S2)/V^K` (over a positive denominator), in shifted arm counts
`x = pA−1, y = pB−1`, is a nonneg-coefficient polynomial with positive constant → `nlinarith` with
monomial-nonneg hints. Positivstellensatz witness that the single-hub template strictly dominates
every stuck two-hub config, all `pA,pB ≥ 1`.

**Collision-safe:** self-building leaf via the `R3Cert.+` glob, imported by nothing — CI builds +
kernel-verifies it, but it is NOT a dependency of the capstone and does NOT touch the
`bg/lean-tree-to-hub` / Obligation-A files. **To the BG session:** this brick is available to wire
into `Hdom`'s multi-hub-stuck elimination (base case of the vertex-budget domination / the
assisted-merge dissolution) whenever that lane reaches it — no coordination needed to *land* it (it
already stands alone); coordination is only needed if/when you *import* it into the capstone chain.

**Still open** (unchanged): the m-hub (m ≥ 3) general case; the concrete Kelmans rewrite's (R-mono)
`Aobj`-monotonicity for `treeToHub_of_rewrite` (= Obligation A). The two-hub cert is the proven base
case those build on.

## Update 2026-09-05 — the m-hub case is now (mostly) DONE: general-environment monotonicity

`R47R7KelmansGenEnvCert.lean` (100 theorems, collision-safe `R3Cert.+` leaf) ports
`certify_general_env_box` (`kelmans_mixed_load.py`) to the kernel: the adjacent hubward Kelmans
merge step (`da ≥ db ≥ 2`) on **any** loaded backbone whose environment neighbours satisfy
`z_x ≤ 3/23` is `per(L)/∏deg` **non-decreasing** for 25 of the 30 load cells — **all N, all m**. This
is the ENVIRONMENT version of the local merge rule, i.e. the actual m-hub generalization (not a
global 3-hub comparison): `Φ` is bilinear in the two marginal environment sums → min at a box corner;
the shift `da=2+v+u, db=2+v` (`u,v≥0`) makes each of the 4 corners/cell an all-nonneg numerator over a
positive denominator (`emit_nonneg_orthant`). **To the BG session:** this is the multi-hub-stuck
elimination for `Hdom`, kernel-verified as a standalone leaf — available to wire into the tree→hub /
Obligation-A chain whenever that lane reaches it.

**Residual (research-hard, do not rabbit-hole):** the 5 `cb`-heavy cells
`{(0,5),(1,4),(1,5),(2,5),(3,5)}` are NOT box-certifiable — even the refined `(db-2)·z1` sub-box + the
explicit C-mover term fails at its corner (`three_hub_residual_probe`: 0 real decreases, so they are
TRUE but need the *exact recursive* `z_C·ρ_C` hub-mover treatment). That is the sharp follow-up; a box
relaxation cannot close it.
