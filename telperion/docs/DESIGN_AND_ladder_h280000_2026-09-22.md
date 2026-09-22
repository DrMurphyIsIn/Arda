# F4 instance factory: design memo for `AND_ladder_h280000`

*Authored 2026-09-22 for the anduril campaign. DESIGN ONLY: no Lean was written, no
registry command was run, the node stays `open`, and its statement file still ends in the
by-design placeholder (`by sorry`, no `sorry` anywhere in a proof term on the island).*
**`conjecture1_proved = False`. Nothing here proves RH.** The node is a finite Turing-style
verification to height 280000, a restriction of RH to one bounded window, and nothing in this
memo is evidence for or against the Riemann Hypothesis. RH-equivalent nodes (`RH_conjecture`,
`MM_zeta_comb_membership`) are out of scope and untouched.

This memo does six things: it gives the verdict and corrects the triage where the files
disagree with it (section 0), it fixes the exact theorem in the island's vocabulary in the
three shapes the lead can choose between (section 1), it fixes the mathematical route with
citations (section 2), it inventories what the pinned Mathlib and the two relevant islands
already supply (section 3), it names every obligation with an honest line estimate
(section 4), and it gives the compute plan, the trust seam and the registry decisions
(sections 5 to 7). Section 8 records the checks that were actually run.

---

## 0. Verdict, and four corrections to the triage

**Verdict: registry-shape mismatch, not a proof gap an agent can close.** The registered
statement is the hypothesis-free theorem

```
theorem all_nontrivial_zeros_up_to_height_280000 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → ρ.re = 1 / 2
```

(`missions/anduril/lean/Statements/AND_ladder_h280000.lean`). No theorem of that shape exists
on the `zeta_zero_localization` island, none is derivable from what is there, and none can be
written on the T5 machinery without adding an axiom (which `Guard_h*` / AxiomGuard would
reject). Every certified object on the ladder is conditional on Arb-class data by design: the
campaign's own trust-boundary text (`docs/MILLION_CAMPAIGN_2026-09-12.md`, "Trust boundary
(unchanged)") lists the on-line zeros `hLine`, the edge bundle, and the height floor `hγ` as
"documented hypotheses of every band theorem", and says outright that "the per-band listing is
documentary only; nothing is ever discharged in-kernel". The hypothesis-free registration is a
migration-era shape error (2026-09-14), not a planned deliverable. The lead has to pick a shape
(section 7); after that the existing artifact is linkable within one session.

Four points where the triage wording needs tightening, each verified in section 8:

1. **Band count.** The chain `AllZeros_h1000 .. AllZeros_h280000` imports **10,379 distinct**
   `RHInBoxT_*` band modules, not 11,200. There are 280 segments x 40 nominal band slots =
   11,200 slots, but the emitter reuses stretched boxes across neighbouring slots. Summed
   on-line zero counts `N` across those modules are 435,568 (overlaps in the stretched boxes
   count some zeros twice); the node title's 432,474 is the de-duplicated count and it matches
   the Riemann-von Mangoldt main term `N(280000) ~ 432,473.7` to within `S(T)`. Per band, `N`
   ranges from 7 to 45. Each band module carries **two** Arb-class binders (`hLine`, `hArbT`),
   so the artifact rests on **20,758 undischarged hypotheses**, packaged as 280 `BandHyp`
   predicates plus `hγ`.
2. **"No kernel path from Arb data to Lean" is true of this island, but not of the campaign.**
   The `zeta_reflection` island already holds a hypothesis-free, kernel-computed zeta zero
   (`ForgeFirstZeroKernel.first_zero_kernel`, node `AND_first_zero_kernel`, proved) and a
   `decide`-checked reflected band (`ReflectedBand_t14`, node `AND_g2_reflected_band`, proved,
   still taking three enclosure hypotheses). So route B below is not a blank slate for the
   `hLine` half: the on-line sign-change machinery has a working one-point prototype. What has
   **no** kernel route anywhere is the `hArbT` half: edge non-vanishing across the strip, the
   ball-confinement conjunct, and the five edge argument-change enclosures. Route B stays a
   multi-quarter program, and the campaign charter already parks it where it belongs
   (`AND_ladder_1e9` is titled "kernel-only (3-axiom decide) ... gated on the A3 Riemann-Siegel
   era").
3. **A conditional wrapper with the registered NAME would still fail the gate.** I ran
   `statement_matches` against a hypothetical
   `theorem all_nontrivial_zeros_up_to_height_280000 (hbands : ...) (hγ : ...) : ∀ ρ ...`:
   it returns `False`, because the normalized registered text is
   `theorem all_nontrivial_zeros_up_to_height_280000 : ∀ ρ : ℂ, ...` and binders sit between
   the name and the colon. Route A therefore means **re-registering the statement text with
   the binders in it**, not renaming the artifact.
4. **The `hγ` half of the "StripClear two-box glue" is already generic in the height.**
   `StripClear.height_floor_of_box_certs (T : ℝ)` (StripClear.lean:57) takes the two
   `NoZerosInBox` conclusions (`hleft`, `hband`, boxes of height `55/16`) and returns exactly
   the `hγ` binder of `all_nontrivial_zeros_up_to_height_280000_of_bands` at `T = 280000`. It
   is wired only at height 100 because nobody wrote the one-line instantiation, not because
   anything is missing. Instantiating it trades one `hγ` binder for the two `NoZerosInBox`
   bundles (`hwind`, `hArb`, both Arb-class), so it is a trust-neutral cosmetic move, offered
   below as shape A3.

Also noted: there is no `Guard_h280000` module (guards are emitted at 25,000-multiples as
block tops; `Guard_h275000`/`Guard_h300000` have no `.olean` in the built sibling either), so
the three-axiom battery for the h280000 capstone specifically has not been recorded. It is job
J1 below and takes minutes.

## 1. The theorem, in the island's vocabulary

All names are in `examples/zeta_zero_localization/lean/` unless stated. `AllZeros_h280000.lean`
(856 lines, emitted by `campaign.py emit_segment_file`) is byte-identical between this worktree
and `~/arda-million`, and `lake-manifest.json` matches package-for-package (Lean
`v4.32.0`, Mathlib `81a5d257c8`).

### 1.0 As registered (hypothesis-free): NOT provable on the T5 island

The statement in section 0. Nothing on the island concludes `ρ.re = 1/2` for a zeta zero
without an Arb-class antecedent; the only zero-location facts that are hypothesis-free are
`ZetaZeroConfinement.zeta_zero_re_mem_strip` (zeros with `Im ≠ 0` have `0 < Re < 1`),
`ZetaZeroConfinement.zero_in_band` (effective dVP: zeros up to `T` lie in `[a, 1-a]`), and the
reflection island's single zero in `(14, 15)`. None of them locates a zero **on** the line at
the heights in question.

### 1.1 Shape A1: the verbatim artifact (`_of_bands`)

`AllZeros_h280000.all_nontrivial_zeros_up_to_height_280000_of_bands` (line 287; 280 binders
`hbands_1000 .. hbands_279000 : AllZeros_h<k>.BandHyp`, `hbands : BandHyp`, and `hγ`):

```
theorem all_nontrivial_zeros_up_to_height_280000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    ...
    (hbands_279000 : AllZeros_h279000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → ρ.re = 1 / 2
```

with, per segment `[A, B]` of width 1000 split into 40 stretched boxes `[bLo i, bHi i]`,

```
def BandHyp : Prop :=
  ∀ i, i < 40 → ∀ ρ : ℂ, ((1 / 4000000 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2
```

(line 264). The proof is `AllZerosUpToHeight.height_chain 279000 280000` applied to the
h279000 capstone and `segment_279000_280000` (line 269), which is
`AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line` at `a = 1/4000000`, `n = 40`, with
`haC_280000` (`1/4000000 ≤ dlvpRateC / log 280000`, line 247) and `hcover` (line 241). This
shape is what the built `.olean` certifies. Registering it verbatim means a ~290-line
generated statement file; the gate passes by construction.

### 1.2 Shape A2: one indexed hypothesis (recommended)

A new emitted module `AllZeros_h280000_Indexed.lean` (or an extra block in the segment file
emitter), ~350 lines:

```
/-- Segment k covers [1000 k, 1000 (k+1)]; `SegBandHyp k` is that segment's `BandHyp`. -/
def SegBandHyp : ℕ → Prop := fun k => match k with
  | 0 => AllZeros_h1000.BandHyp
  | 1 => AllZeros_h2000.BandHyp
  ...
  | 279 => AllZeros_h280000.BandHyp
  | _ => True

theorem all_nontrivial_zeros_up_to_height_280000
    (hbands : ∀ k, k < 280 → SegBandHyp k)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → ρ.re = 1 / 2 :=
  all_nontrivial_zeros_up_to_height_280000_of_bands
    (hbands 0 (by norm_num)) (hbands 1 (by norm_num)) ... (hbands 279 (by norm_num)) hγ
```

The registered statement is then the `theorem ... (hbands ...) (hγ ...) : ∀ ρ ...` text
verbatim, the normalized-containment gate passes, and the same emitter produces the 1e6 form
(1000 arms) for `AND_ladder_1e6` with no new theory. Elaboration risk: a 280-arm `match` on
`ℕ` compiles fine (the island's `bndSeg`/`bLo`/`bHi` are 41-arm matches; `interval_cases`
with `maxHeartbeats 1600000` is used for 40 cases in `hcover`, but the wrapper needs no
`interval_cases`, only 280 `hbands k (by norm_num)` applications where each `SegBandHyp k`
reduces by `rfl`/`decide` on a literal). Budget: 5 to 10 minutes on one core once the
`.olean` closure is present.

### 1.3 Shape A3: `hγ` folded into the two low boxes (optional, trust-neutral)

Add ~40 lines `StripClear_h280000.lean`:

```
theorem all_nontrivial_zeros_up_to_height_280000_strip_cleared
    (hbands : ∀ k, k < 280 → SegBandHyp k)
    (hleft : ∀ ρ : ℂ, (0 ≤ ρ.re ∧ ρ.re ≤ 1/1000) → (0 ≤ ρ.im ∧ ρ.im ≤ 55/16) →
        riemannZeta ρ = 0 → False)
    (hband : ∀ ρ : ℂ, (1/1000 ≤ ρ.re ∧ ρ.re ≤ 999/1000) → (0 ≤ ρ.im ∧ ρ.im ≤ 55/16) →
        riemannZeta ρ = 0 → False) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → ρ.re = 1 / 2 :=
  all_nontrivial_zeros_up_to_height_280000 hbands
    (StripClear.height_floor_of_box_certs 280000 hleft hband)
```

(`hleft`/`hband` are the exact conclusion shapes of `NoZerosInBox_0_1d1000_0_55d16` and
`NoZerosInBox_1d1000_999d1000_0_55d16`, which themselves take `hwind` and `hArb`.) This is what
the node title calls "the StripClear two-box capstone"; it removes the `hγ` binder and adds two
Arb-class box binders. It changes nothing about trust and is worth doing only for uniformity
with `AllZeros_h100`.

## 2. Mathematical route, with citations

**What the ladder actually proves (T5, per band `[T0, T1]` of width 25, strip
`[1/4000000, 3999999/4000000]`).** Two counts of zeros are compared:

* *Total count* in the rectangle `[-1, 2] x [T0, T1]` by the argument principle in edge form.
  `DiffractionCore.zero_count_band_edge_decomp` (line 1641) writes
  `2π N_band = 2 AV(ζ, 2) + AH(ζ, T1) - AH(ζ, T0) + AV(Γℝ, -1) + AV(Γℝ, 2)`, the "RvM edge
  decomposition" (Riemann-von Mangoldt / Backlund: Backlund 1914, "Sur les zeros de la
  fonction zeta(s) de Riemann", C. R. Acad. Sci. Paris 158; Titchmarsh, *The theory of the
  Riemann zeta-function*, 2nd ed., section 9.3). `TuringBand.band_count_eq` (line 74) pins the
  integer `N` from rational enclosures of the five edge quantities and the Mathlib pi bounds
  `Real.pi_gt_d2` / `Real.pi_lt_d4`.
* *On-line count* by sign changes of the real function `gLine t = Re Λ(1/2 + it)`
  (`LambdaLineReal`), with the intermediate value theorem producing `N` strictly increasing
  zeros of `completedRiemannZeta` on the line, hence of `riemannZeta`
  (`BoxLocalization.line_zeta_zero_of_completed`, line 120). This is the Gram/Turing
  sign-change count without Turing's `S(T)` lemma (Turing 1953, "Some calculations of the
  Riemann zeta-function", Proc. LMS (3) 3; Lehman 1970, Math. Comp. 24; Brent 1979,
  Math. Comp. 33), because the rectangle count is obtained directly rather than through Gram
  blocks.
* *Exhaustion*: `TuringBand.turing_band_on_line` (line 148): if the on-line finset `T` has
  `card T = N` and all zeros of the rectangle lie in the ball, every zero in the strip box is
  on the line (the count-exhaustion core `RHInBoxCore`).

Then *confinement* moves from the strip box `[a, 1-a]` to the full critical strip:
`ZetaZeroConfinement.zero_in_band` (line 77) uses the effective de la Vallee Poussin region
`Re ρ ≥ 1 - dlvpRateC / log T` (de la Vallee Poussin 1899; explicit constants in the style of
Ford 2002 "Zero-free regions for the Riemann zeta function", and Mossinghoff-Trudgian 2015,
J. Number Theory 157; the island's constant is `ZeroFreeBridge.dlvpRateC = 1/(112 * 16 * K)`
with `dlvpRateC_lower : 9/1369088 ≤ dlvpRateC`, `DlvpZetaRateEffective.lean:28,294` on the
`li_positivity`/`zero_free_bridge` copies) plus the functional equation
(`riemannZeta_one_sub`) for the mirror edge. The height floor `hγ` (no zero below `55/16`)
enters only to keep the confinement argument away from the real axis.

Finally *tiling and chaining*: `RHInBoxBands.rh_box_of_bands` (line 70) tiles 40 boxes into one
segment, `AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line` (line 176) adds
confinement, and `AllZerosUpToHeight.height_chain` (line 196) folds segments; 280 folds reach
280000.

**Where the Arb data enters (the trust seam).** In every `RHInBoxT_*` module (e.g.
`RHInBoxT_1d4000000_3999999d4000000_279050_279075.lean:37`):

* `hLine`: a list of `N` strictly increasing reals in `[T0, T1]` at which
  `completedRiemannZeta (1/2 + t i) = 0`. Arb produces the sign-change grid; the module
  consumes the *existence* of the zeros as data.
* `hArbT`, nine conjuncts: `ζ ≠ 0` on the bottom edge, top edge and left edge (`σ = -1`) of the
  rectangle; every element of `RHInBoxAnalytic.zeroFinset cPB RPB` lies in the **open**
  rectangle (ball-confinement: the ball radius `sqrt(2537/16) ~ 12.593` barely exceeds the
  rectangle half-diagonal `~12.590`, so this conjunct asserts zero-freeness of thin caps of
  height `~0.09` inside the strip above and below the box); and rational interval enclosures
  of the five argument changes.

The literature route for making these rigorous *by computation* is Platt's: interval
arithmetic with rigorous error terms for `ζ` on the line and edges (Platt 2017, "Isolating
some non-trivial zeros of zeta", Math. Comp. 86; Platt-Trudgian 2021, "The Riemann hypothesis
is true up to 3 x 10^12", Bull. LMS 53). Arb (Johansson 2017, IEEE TC 66) implements exactly
this ball arithmetic; what the island lacks is a **kernel** replay of it.

**Route B, if the lead insists on the hypothesis-free shape.** Each Arb conjunct becomes a
kernel-verified interval computation:

* `hLine`: kernel enclosures of `gLine` on a grid with alternating signs, fed to
  `CheckBand.checkLine_correct` (`zeta_reflection/lean/CheckBand.lean:234`, node
  `AND_checkline_correct`, proved) by `decide`. The evaluator has to be a kernel-reducible
  rational/dyadic algorithm for `Λ(1/2+it)` with a proved error bound. At `t ~ 2.8e5` the
  K=1 Euler-Maclaurin form the reflection track has (`EMZetaComplex.em_zeta_strip`, line 732;
  `EMZetaTail.em_tail3_number`, line 469) needs `~t/(2π) ~ 4.5e4` terms per point, which is
  out of reach of kernel `decide`; the Riemann-Siegel formula with the Gabcke remainder
  (Gabcke 1979, Goettingen thesis; Edwards, *Riemann's zeta function*, ch. 7) needs
  `~sqrt(t/2π) ~ 211` terms and is the A3 era the charter already names.
* Edge non-vanishing on `σ = 2`: generic, no per-band data: `|ζ(2+it)| ≥ ζ(4)/ζ(2) > 0.65`
  from the Euler product (Titchmarsh 3.1). On `σ = -1`: the functional equation reflects to
  `σ = 2` with an explicit `|χ(-1+it)|` from Gamma modulus bounds (Stirling with remainder;
  `AND_stirling_binet_k1` proved, K=1). On the horizontal edges `t = T0, T1`, `σ ∈ [-1, 2]`
  crossing the strip: per-band interval evaluation (the same evaluator as `hLine`, now
  off-line, i.e. complex-valued Riemann-Siegel or Euler-Maclaurin with complex `s`).
* The five argument changes: `AV(Γℝ, σ)` reduces by
  `DiffractionCore.theta_eq_argChangeVert_gammaR` (line 1066) to `θ(T)`-type quantities, i.e.
  `Im log Γ(σ/2 + iT/2)`: Stirling with explicit remainder, generic formula, per-band rational
  evaluation. `AV(ζ, 2)`: `Im log ζ(2+it) = -Σ Λ(n) n^{-2} sin(t log n)/log n`, an absolutely
  convergent series with a rational tail bound, kernel-evaluable. The two horizontal `AH(ζ)`
  terms need *argument tracking*: a lemma that if `|ζ| ≥ m` on the edge and the grid spacing
  times a derivative bound is below `m`, then the continuous argument change equals a finite
  sum of principal-argument differences of grid enclosures. This lemma does not exist on
  either island or in Mathlib.
* Ball confinement (`hins`): zero-freeness of `ball \ open rectangle`. The parts outside the
  strip are free (`zeta_zero_re_mem_strip`); the two thin caps inside the strip need 2-D
  interval evaluation of `ζ` with a lower bound on `|ζ|` (or a second argument-principle
  count on a slightly larger rectangle whose difference is zero). Per-band numerics again.

## 3. Inventory: what is already available

**Pinned Mathlib** (`81a5d257c8`, present built under
`~/arda-million/.../zeta_zero_localization/lean/.lake/packages/mathlib`):
`riemannZeta_one_sub`, `completedRiemannZeta_one_sub` (NumberTheory/LSeries/RiemannZeta);
`riemannZetaZeros` closed, discrete, finite on compacts (NumberTheory/LSeries/ZetaZeros);
`riemannZeta_ne_zero_of_one_le_re` and the `1+it` nonvanishing (NumberTheory/LSeries/Nonvanishing);
`Complex.Gamma_ne_zero`, `Gamma_ne_zero_of_re_pos`; `Real.exp_bound`, `Complex.exp_bound`,
`Real.cos_bound` (order 4), `Real.pi_gt_d2`, `Real.pi_lt_d4`, `Real.pi_gt_d20`,
`Real.log_two_gt_d9`; real Stirling (Analysis/SpecialFunctions/Stirling); Hurwitz zeta.
**Missing from this Mathlib**: Euler-Maclaurin, complex Gamma modulus bounds, any explicit
zero-free region, Riemann-Siegel, any interval-arithmetic evaluator.

**`zeta_zero_localization` island** (source in this worktree; built in `~/arda-million`):
`AllZerosUpToHeight.{all_nontrivial_zeros_in_segment_on_line:176, height_chain:196}`;
`ZetaZeroConfinement.{zero_in_band:77, zeta_zero_re_mem_strip:131, no_low_zeros_of_strip_clear:162}`;
`StripClear.{hclear_low_of_box_certs:31, height_floor_of_box_certs:57, all_nontrivial_zeros_up_to_height_100_strip_cleared:70}`;
`TuringBand.{band_count_eq:74, turing_band_on_line:148}`;
`DiffractionCore.{left_edge_prime_reflection:867, argChangeVert:949, argChangeHoriz:954, zeta_total_argChange_eq_count:961, theta_eq_argChangeVert_gammaR:1066, zero_count_band_edge_decomp:1641}`;
`RHInBoxBands.rh_box_of_bands:70`; `BoxLocalization.line_zeta_zero_of_completed:120`;
`RHInBoxAnalytic.zeroFinset:310`; kernel enclosure kits `CosEnclosure` (double-angle
reduction on top of `Real.cos_bound`, error `< 1e-9` at `θ ≤ 68.5`) and
`ExpEnclosureInstances` (order-14 `exp` brackets); `campaign.py` emitters
`emit_segment_file:823`, `emit_guard_module:321`. 10,379 `RHInBoxT_*` modules with
`.olean`s in the sibling (25,711 band `.olean`s total, ladder built through h640000).

**`zeta_reflection` island** (the kernel-computation track): `CheckBand.checkLine_correct:234`
(`AND_checkline_correct`), `ReflectedBand_t14.{ok, pilot}` (`AND_g2_reflected_band`),
`EMZetaComplex.em_zeta_strip:732` (`AND_em_zeta_strip`), `EMZetaTail.em_tail3_number:469`
(`AND_em_tail3_number`), `ForgeFirstZeroKernel.first_zero_kernel:32` (`AND_first_zero_kernel`,
hypothesis-free zero in `(14, 15)`), `ThetaConverge.convergence_obligation:200`, dyadic
interval kit `DIntvDef`/`DIntvCorrect`, `ForgeThetaBox`, Stirling K=4 modules.

**Registry**: `AND_ladder_h280000` is `open`, depended on by `AND_ladder_1e6` (open) and the
draft goal `AND_ladder_1e13`; `AND_ladder_1e9` (open) already carries the kernel-only charter.

## 4. Named obligations with line estimates

### Route A (register the shape the island proves)

| id | obligation | lines | who |
|---|---|---|---|
| A-0 | Lead decision: shape A1 (verbatim), A2 (indexed, recommended) or A3 (A2 + `hγ` folded) | 0 | lead |
| A-1 | Re-register the statement file with the chosen binders (A1: ~290 generated lines; A2/A3: ~10 lines + the `SegBandHyp` name resolved by the artifact import) | 10 to 290 | lead (`mission add`/regenerate; the file header says DO NOT EDIT BY HAND) |
| A-2 | Emit `AllZeros_h280000_Indexed.lean`: `SegBandHyp` (282-line match) + wrapper theorem (~285 lines); extend `emit_segment_file` or add `emit_indexed_capstone(top)` (~60 lines of Python) | ~350 Lean + ~60 py | agent |
| A-3 | Optional `StripClear_h280000.lean` (shape A3) | ~40 | agent |
| A-4 | `Guard_h280000.lean` from `emit_guard_module(280000)` (or for the indexed name), run, record the three-axiom message | 7 | agent |
| A-5 | Retitle node and readback so the binders are described as the Arb trust boundary, not as glue; new `attempts.jsonl` row; blind audit; `link`; `grant` | 0 Lean | lead |

Total agent work: one session, gated on A-0.

### Route B (keep the hypothesis-free form; kernel discharge of every Arb input)

| id | obligation | new theory (lines) | notes |
|---|---|---|---|
| B-1 | Riemann-Siegel formula with Gabcke remainder, formalized and reflected into a kernel-reducible dyadic evaluator for `Λ(1/2+it)` and for complex `ζ(σ+it)`, `σ ∈ [-1,2]`, `t ≤ 2.8e5` | 4000 to 8000 | the A3 era of the charter; first formalization anywhere; the EM route (`em_zeta_strip`) is not viable at `t/(2π) ~ 4.5e4` terms per point inside `decide` |
| B-2 | Per-band `hLine` by `checkLine` reflection over B-1 output | ~200 (glue) | theory exists (`checkLine_correct`); cost is compute |
| B-3 | Generic edge non-vanishing at `σ = 2` (Euler product lower bound) and `σ = -1` (functional equation + complex Gamma modulus, Stirling K=4) | ~800 | no per-band data; complex Gamma modulus bounds are absent from Mathlib |
| B-4 | Horizontal-edge non-vanishing and the two horizontal argument changes: the arg-tracking lemma (grid enclosures + Lipschitz bound imply the continuous argument change) plus a derivative bound for `ζ` on the edge | 1000 to 1500 | not in Mathlib or either island |
| B-5 | `AV(ζ, 2)` via the absolutely convergent `Λ(n) n^{-2}` series with tail bound; `AV(Γℝ, σ)` via `theta_eq_argChangeVert_gammaR` + Stirling with remainder | ~600 | generic formulas, per-band rational evaluation |
| B-6 | Ball-confinement caps: 2-D interval lower bound on `ζ` over the two thin caps, or a second argument-principle count | ~400 + per-band compute | the least studied conjunct; nothing on either island addresses 2-D enclosures |
| B-7 | Emitter rewrite: every `RHInBoxT_*` re-emitted with data certificates discharged by `decide` instead of binders; 10,379 bands re-checked | ~800 py | plus the compute in section 5 |

Total: 8,000 to 12,000 lines of new theory, plus an unmeasured kernel-compute campaign. Not one
session, not one quarter. This is precisely `AND_ladder_1e9`'s stated gate and should be
authored as that node's `depends_on` bricks (the wall map's op R8), not attached to h280000.

## 5. Compute plan

Machine: this host, 32 cores, 96 GB (measured `hw.ncpu`, `hw.memsize`). House rule: only one
`lake build` per island at a time; none of J0 to J4 needs a `lake build` at all.

| job | inputs | command shape | wall-clock / cores | emits | composes into |
|---|---|---|---|---|---|
| J0 bring-up | `~/arda-million/telperion/examples/zeta_zero_localization/lean/.lake` (25 GB; manifest match verified; `AllZeros_h280000.lean` and `StripClear.lean` byte-identical) | `cp -Rc` (APFS reflink) into `examples/zeta_zero_localization/lean/.lake` in this worktree | seconds to a few minutes, 1 core, ~0 extra disk | the built closure of 25,711 band `.olean`s + `AllZeros_h280000.olean` | prerequisite for J1 to J3 |
| J1 axiom battery | `Guard_h280000.lean` (7 lines, from `emit_guard_module(280000)`) | `lake env lean Guard_h280000.lean` (no build) | 2 to 10 min, 1 core (import closure of ~10.4k modules; a few GB RSS) | the `#guard_msgs` pass: `depends on axioms: [propext, Classical.choice, Quot.sound]` | the grant's kernel-clean evidence for shape A1 |
| J2 indexed wrapper (A2) | `AllZeros_h280000_Indexed.lean` from the new emitter | `lake env lean AllZeros_h280000_Indexed.lean`, then `#print axioms` on the new name | 5 to 10 min, 1 core; risk is a slow 280-arm `match` reduction, mitigated by `rfl`-by-literal arms | `.olean` with `theorem all_nontrivial_zeros_up_to_height_280000 (hbands ...) (hγ ...) : ...` | the registered statement text for shape A2 |
| J3 StripClear glue (A3) | `StripClear_h280000.lean` | `lake env lean` | ~1 min, 1 core | `_strip_cleared` theorem | shape A3 statement |
| J4 registry | J1 (and J2/J3) logs, artifact path | `mission link` / `attempt` / `grant` after a blind audit | minutes | registry rows | node `proved` in the chosen conditional shape |
| J5 calibration (optional, no Lean) | the 10,379 band `N` values | sum per segment, compare with `N(T)` from Riemann-von Mangoldt and with an independent zero table (Odlyzko / LMFDB) | seconds | a ledger row: 432,474 vs `432,473.7 + S(T)` | falsifiability note in the readback; no trust change |

Route B compute (for the record, not scheduled): the on-line grid alone is ~2 to 4 points per
zero, ~1 to 2 million `Λ(1/2+it)` evaluations, each a Riemann-Siegel sum of ~200 terms with
40-digit dyadic `cos`/`sqrt` enclosures, inside kernel `decide`; the horizontal edges and caps
add a comparable off-line load. The reflection island's `first_zero_kernel` is the only
timing anchor (two points), and its wall time is not recorded in the node; a one-band pilot at
`T ~ 1000` must be timed before any plan is written. Order-of-magnitude guess `10^3` to `10^4`
core-hours; treat as unmeasured.

## 6. Trust seam: what the node would and would not establish

**Under shape A1/A2/A3 the kernel establishes**: the *composition* is correct. If the 10,379
band data sets are what Arb says they are (for each band: the `N` on-line sign-change zeros
exist, `ζ` does not vanish on three edges, no zero sits in the ball caps, and the five edge
argument changes lie in the stated rational intervals), and if no zero lies below height
`55/16` (or, under A3, if the two low boxes are empty as their `hwind`/`hArb` data say), then
every zero of `riemannZeta` with `0 < Im ≤ 280000` has `Re = 1/2`. Everything that is
mathematics rather than arithmetic (dVP confinement, functional equation, argument principle
in edge form, IVT on the line, count exhaustion, tiling, chaining) is kernel-checked with
axioms `[propext, Classical.choice, Quot.sound]` (to be recorded by J1).

**Remaining hypotheses (the seam), counted**: 280 `SegBandHyp` predicates = 10,379 band
modules x (`hLine` + `hArbT`) = 20,758 Arb-class binders, each conjunct a finite numerical
claim checked by Arb ball arithmetic outside the kernel; plus `hγ` (or the two `NoZerosInBox`
bundles). None of these is a mathematical conjecture; all are replayable by any interval
package; none is checked by Lean.

**What the node would NOT establish**, under any shape: anything about zeros above 280000;
anything about RH (`conjecture1_proved = False`); under shapes A, anything at all without the
Arb premise. The hypothesis-free statement as currently registered is not established by the
island and will not be until route B lands, which the charter places at the `AND_ladder_1e9`
horizon.

## 7. Registry decisions for the lead

1. **Choose the shape.** Recommendation: **A2** (indexed) for `AND_ladder_h280000` and, by
   the same emitter, for `AND_ladder_1e6`; keep the hypothesis-free/kernel-only form where the
   charter already puts it, `AND_ladder_1e9` and above. This makes the F4 row of the wall map
   read as it should: honest, finite, conditional-on-data at 1e6 and below; kernel-only from
   1e9 by the A3 bricks.
2. **Re-register the statement file** with the binders (the gate cannot be satisfied
   otherwise, section 0 item 3). The verbatim `_of_bands` text (A1) is the zero-design option
   if the lead prefers no new Lean at all; it is linkable today from the built sibling.
3. **Retitle and re-read-back.** The current title calls the binders "artifact-side discharge
   glue" and the readback says each `BandHyp` "is discharged by the kernel-checked RHInBoxT
   band modules". Neither is right: the band modules *consume* Arb data, they do not discharge
   it. The `WALL_BACKLOG_MAP_2026-09-18` row 70 ("hypothesis-discharge blocker, not compute")
   should say "registry-shape blocker; the hypotheses are the Arb trust boundary and are not
   dischargeable on T5".
4. **Branch reconcile.** The Lean source for h280000 is present and byte-identical in this
   worktree; only the build closure lives in `~/arda-million`. Whether the registry-side
   precondition "rh/million-turing -> main" still applies is a lead call; it is not a
   technical blocker for J0 to J3.
5. **Author the A3-era bricks as draft nodes** under `AND_ladder_1e9` (RS main sum, theta
   branch, Gabcke remainder, arg-tracking lemma, complex Gamma modulus), so that route B has a
   home in the DAG and h280000 stops carrying it.

## 8. Checks actually run (2026-09-22, this worktree, read-only)

* `missions/anduril/nodes/AND_ladder_h280000.toml`, its statement file and both
  `attempts.jsonl` rows read; `mission status anduril` run (node `open`, dependents
  `AND_ladder_1e6`, `AND_ladder_1e13`).
* `AllZeros_h280000.lean`: 856 lines; `BandHyp` at 264, `segment_279000_280000` at 269,
  `_of_bands` at 287 with exactly 280 `hbands` binders (grep count) plus `hγ`.
* `grep -l ': BandHyp :=' AllZeros_h*.lean` over all 642 files: **0** discharges.
* `grep -rln '^axiom\|native_decide'` over the island: none.
* Distinct `RHInBoxT_*` imports across `AllZeros_h1000..h280000`: **10,379**; per-module `N`
  from the headers: min 7, max 45, sum 435,568. Riemann-von Mangoldt main term at 280000:
  432,473.7 (matches the title's 432,474).
* `RHInBoxT_1d4000000_3999999d4000000_279050_279075.lean:37`: `hLine` (43 zeros) and
  nine-conjunct `hArbT` as documented Arb inputs; `TuringBand.turing_band_on_line:148`
  consumes them.
* `StripClear.lean`: `height_floor_of_box_certs (T : ℝ)` at 57 is generic in `T`; the
  height-100 wrapper at 70 is the only instantiation. `NoZerosInBox_*` (2 modules) take
  `hwind` and `hArb`.
* `src/telperion/missions/verify.py:185 statement_matches` executed in Python against the
  artifact (`False`) and against a hypothetical same-name conditional wrapper (`False`).
* Built sibling `~/arda-million/.../zeta_zero_localization/lean/.lake`: 25 GB;
  `AllZeros_h280000.olean` (2.77 MB, 2026-09-14), `StripClear.olean` present; 25,711
  `RHInBoxT_*.olean`; 642 `AllZeros_h*.olean` through h640000; zero `Guard_h*.olean`;
  `lake-manifest.json` identical to this worktree's; `AllZeros_h280000.lean` and
  `StripClear.lean` byte-identical (`cmp`).
* Pinned Mathlib inventory by file presence and `grep` (section 3); Lean toolchain
  `leanprover/lean4:v4.32.0`.
* `zeta_reflection` island: `first_zero_kernel:32` hypothesis-free; `ReflectedBand_t14.ok`
  by `decide`, `pilot` with three `hmem` binders; node TOMLs for the five proved
  reflection-track nodes read.
* `docs/MILLION_CAMPAIGN_2026-09-12.md` "Trust boundary (unchanged)" and the "documentary
  only; nothing is ever discharged in-kernel" sentence; `docs/WALL_BACKLOG_MAP_2026-09-18.md`
  row 70.
* Host: 32 cores, 96 GB. No git command, no registry mutation, no `lake build` was run.

`conjecture1_proved = False`. Nothing in this memo proves RH.
