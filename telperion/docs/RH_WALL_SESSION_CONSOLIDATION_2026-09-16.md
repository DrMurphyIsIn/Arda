# RH-wall session consolidation — inventory, shape assessment, reusable capabilities

*Consolidation of the reflection/no-go-map session on `research/arithmetic-fq-membership-spec`.
`conjecture1_proved = False` throughout. Nothing here proves or approaches RH; it maps the wall
and hardens a small exact kernel core.*

## 1. Kernel artifacts produced (all `[propext, Classical.choice, Quot.sound]`, 0 sorry)

| File (`telperion/examples/.../lean/`) | Load-bearing theorems | Role |
|---|---|---|
| `reflection_forced/ReflectionForced.lean` | `functional_constant_on_reflection_pair`, `reflection_pair_offline_distinct` | FORCED-half (pointwise): a functional invariant under BOTH reflections is constant on `{ρ,1−conj ρ}` |
| `family_reflection_blind/FamilyReflectionBlind.lean` | `refl_involutive`, `reflectionPair_closed`, `symmetric_stat_reflection_blind` | AGGREGATE-half: symmetric statistics of the zero multiset are reflection-blind |
| `li_razor/LiRazor.lean` | `critical_line_iff_unit_normSq`, `left_of_line_iff_outside`, `offline_left_geometric_blowup` | RAZOR: on-line ⇔ Li-summand base on the unit circle; off-line ⇒ `rⁿ` blow-up |
| `ordinate_insensitivity/OrdinateInsensitivity.lean` | `completedZeta_zero_reflect`, `riemannZeta_zero_conj`, `offline_zero_has_distinct_partner` | reflection/conjugation symmetry of the actual zero set |
| `trivial_zero_localization/TrivialZeroLocalization.lean` | `trivial_zero_is_archimedean`, `trivial_zero_off_critical_line` | trivial zeros are an archimedean (Γℝ-pole) artifact |
| `multiplicative_nogo/MultiplicativeNoGo.lean` | `not_completelyMultiplicative_vonMangoldt` | guardrail: Λ is not completely multiplicative |
| `crystalline_substrate/CrystallineAlmostPeriodic.lean` | bricks 1–5 (Bohr almost-periodicity → pure tone) | AFQ substrate tower (Route A) |

Docs: `RH_WALL_FIVE_SWEEP_CAPSTONE_2026-09-16.md` (audited + corrected by sweep `w7m91imr9`),
plus the per-sweep map docs.

## 2. Telperion shape assessment (`shape_scout`, run on the 7 dirs above)

`covered = 0 · candidate = 11 · structural = 19`

**Verdict: this session added NO new Telperion emitter shape or skill.**

- The **19 structural** theorems (all the reflection / involution / `iff`-of-structures / razor
  cores) are the "needs human Lean" bucket by construction — Telperion's engine certifies
  *polynomial/rational* inequality & identity families, and these are symmetry statements over
  transcendental objects.
- The **11 candidates are textual false positives.** `shape_scout` matched `A = conj B` and bare
  `Prop` goals, but every one involves a transcendental head (`Gammaℝ`, `completedRiemannZeta`,
  `riemannZeta`, `vonMangoldt Λ`, `Complex.exp`) that the sympy `IdentityEmitter` /
  `DirectPolyaEmitter` cannot discharge. They are NOT emitter-reachable.

**Tool finding (recommendation, not implemented here):** `shape_scout`'s textual identity/polya
classifier over-proposes transcendental goals to the polynomial emitters (which would then refuse
them). A cheap fix is a transcendental-head denylist (`Gammaℝ`, `completedRiemannZeta`,
`riemannZeta`, `Λ`/`vonMangoldt`, `Complex.exp`, `IsAlmostPeriodic`, `RelativelyDense`) demoting
such matches from `candidate` to `structural`. Worth a follow-up PR to `telperion/tools/shape_scout.py`
with a unit test; flagged, not done, to keep this consolidation focused.

## 3. Reusable capabilities (non-emitter — the honest "new shapes")

None of these extend the sympy-certificate engine; they are human-Lean / operational patterns worth
reusing, and two serve the standing BG↔RH cross-pollination order.

1. **Reflection / obstruction no-go recipe** (structural, cross-pollinates to BG). Shape: *a real
   functional invariant under a symmetry group is constant on its orbits, hence cannot separate
   points in an orbit.* `functional_constant_on_reflection_pair` + `symmetric_stat_reflection_blind`
   are the RH instance; the identical pattern discharges "a symmetric objective cannot distinguish
   isomorphic BG configurations." A documented recipe, not an emitter (the group action is
   problem-specific).
2. **Warm-cache read-only Lean verification loop** (operational). Invoke the toolchain `lean`
   binary directly with a hand-assembled `LEAN_PATH` (toolchain-core `lib/lean` FIRST, then the
   sibling `quasicrystal/.lake/packages/*/.lake/build/lib{,/lean}`); `lake env` cannot spawn in this
   environment. Compiles + `#print axioms` a standalone `import Mathlib` brick against the warm
   Mathlib olean cache with no project build. Footgun logged: a `-/` digraph in prose (e.g.
   "one-/n-level") closes the block comment early.
3. **Multi-sweep + adversarial self-audit workflow** (research pattern). Sweep an obstruction from
   N coordinate axes → adversarially verify each finding → then a dedicated *self-audit* sweep whose
   job is to BREACH the synthesized claim. In this session the self-audit (`w7m91imr9`) correctly
   caught three prose overclaims a confirmatory sweep would have missed. The pattern belongs in the
   steward toolkit: never let a capstone stand unaudited.

## 4. Merge disposition
Branch `research/arithmetic-fq-membership-spec` → `main` via PR (maintainer admin-merge). The
artifacts are honest (no RH claim), kernel-clean, and self-contained (`import Mathlib` only; verified
out-of-band per the research-example house pattern — CI lean-e2e builds only `toy_box`). The three
capabilities above are captured here; the `shape_scout` fix is deferred to its own PR.
