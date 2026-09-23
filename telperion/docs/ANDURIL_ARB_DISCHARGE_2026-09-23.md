# ANDURIL Arb discharge: inventory, pilot, kernel economics and the Riemann-Siegel route (2026-09-23)

conjecture1_proved = False. Everything in this memo concerns finite verification of zeta zeros
up to a fixed height. Interval arithmetic plus the intermediate value theorem at finitely many
points says nothing about the Riemann Hypothesis.

## 0. Preamble

**Question.** ANDURIL's artifacts rest on inputs computed outside Lean: Arb enclosures and
other numerical oracles, fed in as hypotheses. Which inputs are they? Can the Lean kernel
recompute them itself, using plain kernel reduction on GMP-accelerated `Nat` literals with
no `native_decide`, `ofReduceBool` or new axioms? What would that cost at the two ladder
heights that matter next, 280000 and 10^6?

**Method.** One inventory pass and three seats, each checked by a skeptic.
- **Pilot:** discharge the one proved node that still takes Arb hypotheses, `AND_g2_reflected_band`.
- **Economics:** measure kernel cost per term of a certified zeta evaluator at four heights and extrapolate.
- **RS design:** design the Riemann-Siegel route, and prove its theta brick.

The skeptics did not refute the pilot or the economics seat. The RS-design seat's skeptic verdict
did not reach this memo because the orchestrator's input was truncated. To cover that, this author
re-elaborated its Lean file independently; see section 4.0 and section 6.

**Location.** Worktree `/Users/peterwmurphy/arda-cl-arb`, branch `cl/arb-discharge` on
`ci/hardening`.
- Island: `telperion/examples/zeta_reflection/lean`, Lean and Mathlib v4.32.0.
- Machine: 32 cores, 96 GB RAM, about 42 GB of free disk.
- All heavy Lean ran through `scratchpad/leanlock.sh`.

**Rules held.**
- No git writes.
- No edits under `telperion/missions/`. Every registry operation below is a proposal.
- The only tracked file changed is `zeta_reflection/lean/lakefile.toml`, by the pilot seat: it
  added `ReflectedBand_t14_Kernel` to `defaultTargets` plus lean_lib entries (42 insertions).

**Headline.**
1. **G2 has a hypothesis-free companion, but the node as registered is unchanged.** The conclusion
   of the G2 pilot, two zeros of `completedRiemannZeta` on the line in [14, 22], is now proved with
   no hypotheses and the three standard axioms. Wide, kernel-proved boxes replace the tight Arb boxes.
   The registered statement still carries `hmem0/1/2`, so it stays closure-unclean. Only a new
   companion node, or a statement strengthening the owner approves, turns this into a
   hypothesis-free registry entry.
2. **The existing EM machinery cannot carry the h280000 seam.** Measured kernel cost is about 230 µs
   per Dirichlet term. With the island's order-3 Euler-Maclaurin that puts h280000 at about 5 months
   on 32 cores plus about 13 TB of oleans, and 10^6 at about 200 core-years.
   - EM of order up to 13 (K ≤ 6) brings h280000 to about 6 days of compute.
   - Riemann-Siegel brings it under an hour of compute, but depends on theory that is not yet
     formalized (sections 3 and 4).
3. **Theta is done; the RS remainder is now the long pole.** The theta brick of the RS route
   (`AND_theta_branch`) is proved for all t > 0. The long pole is the explicit RS remainder
   (Hankel representation plus saddle bound, 5,000 to 11,000 lines), together with the off-line
   evaluator that the 93,411 `hArbT` conjuncts need.

---

## 1. Arb-input inventory

The inventory is read-only. A script ran over all 10,379 `RHInBoxT_*` modules that
`AllZeros_h1000 .. AllZeros_h280000` import (in `zeta_zero_localization/lean`). Numerical margins
come from mpmath at dps 20 to 120.

### 1.1 By node

| node | status | Arb or numerical-oracle hypotheses in the artifact |
|---|---|---|
| AND_first_zero_kernel | proved | None. The theorem takes no arguments. Its zeta boxes (`ForgeZeta14/15`: EM order 3, N = 50, tail at most 13/10000) and theta boxes (`ForgeThetaBox`: Euler route, n0 = 200) are kernel-proved. |
| AND_em_zeta_strip, AND_em_tail3_number, AND_stirling_binet_k1 | proved | None. The `hanchor` binders are discharged by `ZeroFreeBridge.tendsto_digamma_sub_log` (needs Re at least 2). |
| AND_checkline_correct | proved | None. `hmem` is a parameter of a general theorem, not a trust input. |
| AND_g2_reflected_band | proved, closure_clean = false | **G2:** `hmem0/1/2 : DIntv.memR (gLine t) (d.boxes.get i)` at t = 14, 15, 22. |
| AND_ladder_h280000 | open | Registered with no hypotheses. The artifact takes `hbands` (280 `SegBandHyp`) and `hγ`; see 1.2. |
| AND_ladder_1e6 | open, no artifact | Planned artifact has the same shape: about 41.7k bands and about 83k Arb binders. 27,503 bands exist up to 680000. |
| AND_ladder_1e9, AND_ladder_1e13 | open / draft, no artifact | Nothing to inventory yet. |

### 1.2 The h280000 capstone

The capstone is `all_nontrivial_zeros_up_to_height_280000 (hbands : ∀ k, k < 280 → SegBandHyp k)
(hγ : ...)` in `AllZeros_h280000_Indexed.lean`. `Guard_h280000.lean` asserts its axioms are
[propext, Classical.choice, Quot.sound].

**Structure.**
- Each `SegBandHyp k` bundles the box claims of one segment. Each box claim is the conclusion of
  `RHInBoxT_*.rh_in_box_*`, which takes two binders, `hLine` and `hArbT`.
- The box claims are **assumed, not composed**: the segment files import the band modules but
  never call them.

**Per-band statistics.**
- On-line zero count N per band: 7 to 45, summing to 435,568 (overlaps included; 432,474 after
  de-duplication).
- Box widths: 25 to 40.25.
- Distinct edge heights: 13,235.
- Ball caps: 0.057 to 0.092.
- Every enclosure is 1e-12 or 2e-12 wide.

**Pin slack.** The smallest lower slack is 6.28 rad and the smallest upper slack is 6.14 rad.
So the five-term argument sum only needs about 6 rad of total error, and the Arb precision
exceeds what the pin needs by about 12 orders of magnitude.

| id | Lean form (per band [T0,T1]) | count | precision actually needed | discharging lemmas |
|---|---|---|---|---|
| H1 `hLine` | N increasing on-line zeros of `completedRiemannZeta` in [T0,T1] | 10,379 binders, at least 445,947 sign evaluations | sign of Z(t); margins down to 2.0e-4 (see 4.2) | K4 + evaluator + theta |
| H2a `hnzb`, `hnzt` | ζ(x+Ti) ≠ 0, x ∈ [-1,2], T ∈ {T0,T1} | 20,758 | only x ∈ (0,1) needs numbers | K1 + E(T) |
| H2b `hnzl` | ζ(-1+yi) ≠ 0 | 10,379 | **none**: follows from `zeta_zero_re_mem_strip` | K1 glue only (dischargeable today) |
| H2c `hins` | zeros in the ball lie in the open rectangle | 10,379 | no zero in (0,1) x caps of height ≤ 0.093 | K1 + K2 + off-line evaluator |
| H2d `hAV2` | `argChangeVert ζ 2 T0 T1 ∈ Icc a b` | 10,379 | a generic bound, at most 2 log ζ(2) < 0.996, fits the pin | K6a (generic) |
| H2e `hAHt`, `hAHb` | horizontal argument changes of ζ | 20,758 (13,235 distinct T) | about ±1 rad | K6c (+K6d) + off-line evaluator |
| H2f `hAG1`, `hAG2` | `argChangeVert Gammaℝ σ T0 T1`, σ ∈ {-1,2} | 20,758 | about ±1 rad | K6b via `lam_bracket` + T6 |
| H3 `hγ` | no zero with 0 < Im < 55/16 | 1 (valid at every height) | min abs((s-1)ζ) = 0.730 on [1/2,1] x [0,55/16] | K2 + small-t evaluator |
| G2 `hmem0/1/2` | `memR (gLine t) box`, t = 14, 15, 22 | 3 | relative width about 1e-75 (about 250 bits of ζ and of the abs(Γℝ)) | not dischargeable as registered; pilot route (section 2) |

**Seam totals.**
- 10,379 `hLine` binders.
- 93,411 `hArbT` conjuncts: 31,137 nonvanishing, 10,379 confinement and 51,895 enclosures.
- One `hγ`.

### 1.3 The kernel lemmas named in the inventory

- **K0** `segBandHyp_of_bands`: glue that builds `SegBandHyp k` from the `rh_in_box_*` theorems.
  Needed on every route.
- **K1** `hArbT_nonvanishing_of_edge_clear`: from `zeta_zero_re_mem_strip`, the ball geometry and
  edge-clearance facts E(T0, δ), E(T1, δ), derives `hnzb`, `hnzt`, `hnzl` and `hins`.
- **K2** `nonvanishing_of_approx_grid`: a variant of `nonvanishing_of_grid` that works with an
  approximant.
- **K3**: a computable evaluator for EM zeta. The economics seat built a Nat-only version (section 3).
- **K4** `signLine_correct` (= `checkBandRS_correct` in RS form): consumes sign boxes of
  S(t) = cos φ Re ζ − sin φ Im ζ and avoids abs(Γℝ) altogether.
- **K5**: complex Stirling. For the imaginary part of log Γ it is now largely superseded by
  `lam_bracket` (section 4.0).
- **K6a–K6d**: argument changes.
  - K6a: the σ = 2 vertical, via the Λ(n) series.
  - K6b: the Γℝ verticals.
  - K6c: piecewise half-plane tracking.
  - K6d: horizontal edges folded through the functional equation.

---

## 2. Pilot outcome: G2 (VERIFIED; the skeptic did not refute it)

**Result.** Theorem `ReflectedBand_t14_Kernel.pilot_kernel` takes no hypotheses and uses
axioms [propext, Classical.choice, Quot.sound]:

```
∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧
  (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)
```

**How it is proved.**
- `dK` holds three sign-definite dyadic gLine boxes: [-1/2, -2^-37], [2^-37, 4] and [-8, -2^-55].
- `okK : checkLine dK.boxes = true` is proved by `decide`, with axioms [propext] only.
- The unchanged `CheckBand.checkLine_correct` and `ReflectedBand_t14.grid` carry this to the conclusion.
- The skeptic confirmed by its own MetaM check that the conclusion is syntactically identical to
  that of `ReflectedBand_t14.pilot` with its three binders stripped.

**New island modules** (untracked): `KernelGammaEnvelope`, `KernelBandEnclosures`, `ForgeZ22Terms`,
`ForgeZeta22`, `ForgePhi22`, `ReflectedBand_t14_Kernel` and `AxiomGuardArbKernel`. The Python
drivers are `forge_band22_zeta.py` and `forge_band22_phi.py`.

**What was new.**
1. **`KernelGammaEnvelope`: the island's first kernel magnitude bound on Γ.**
   - Bounds: abs(Γ(s)) ≤ Γ(Re s); Γ(1/4) ≤ 4; and (9/4) e^{-π|y|} ≤ abs(Γ(1/4+iy)) ≤ 4, from the reflection formula.
   - Consequence: gLine t = M(t) S(t), with (3/4) e^{-π|t|/2} ≤ M ≤ 4.
   - The lower bound is crude, loose by 1e4 to 4e7, but sign boxes only need it positive. The
     inner edges of the boxes clear by factors of 2.59, 3.94 and 4.16.
2. **New numerics were needed only at t = 22.**
   - Zeta: EM order 3 at N = 10, with tail bound 0.214.
   - Theta: Euler route at n0 = 128, width 0.27 rad; 129 arctan terms reduced to arguments ≤ 0.41.
   - t = 14 and t = 15 reuse `ForgeZeta14/15` and `ForgeThetaBox`.
3. **Kernel re-check time** (replayed with `addDeclCore`):
   - t = 14: about 11.4 s. t = 15: about 8.9 s. t = 22: about 2.3 s.
   - `okK`: 1.1 ms. `pilot_kernel`: 20 ms.
   - The skeptic's replay agreed to within 25 percent on every row.
4. **Negative controls.**
   - A wrong-sign box at t = 22 is rejected by `decide`.
   - A box at t = 15 that straddles 0 is rejected by `decide`.
   - The wrong-sign claim `2^-55 ≤ gLine 22` fails `linarith`.

**Registry gate.**
- `statement_matches` returns True for the proposed companion statement span (`dK`, `okK`,
  `pilot_kernel`).
- It returns False for the *registered* `AND_g2_reflected_band` statement against the new artifact,
  as it must: the two are different statements.
- `artifact_incompleteness_markers` returns [] on all six new files.

**What stays conditional.** The registered tight-box `pilot` still takes `hmem0/1/2`, and its
`closure_clean = false` remains correct. Discharging those boxes at their registered width would
need about 250-bit zeta and abs(Γℝ). With order-3 EM that means about 1e33 terms, so order-K EM
plus a sharp Stirling magnitude bound would be needed. That buys nothing: the conclusion is already
hypothesis-free.

**CI gap.** `telperion-zeta-reflection.yml` does not build or guard the new modules, and the mission
description records that this island has no working CI (`CLOSURE_RUN_2026-09-22.md`).

---

## 3. Kernel economics (VERIFIED; the skeptic did not refute it) and verdicts

### 3.1 What was measured

The seat built a Nat-only kernel evaluator for the order-3 EM Dirichlet sum of ζ(1/2+it) and
proved it sound. Every theorem is hypothesis-free with the three standard axioms, and every chunk
check runs under `decide +kernel`. The files are in `Probes/`, which is not yet a lean_lib:
`ArbEconomics_Eval` (226 lines), `_Sound` (1,114), `_Zeta` (286), plus instance files. The
certified values are enclosures of Re and Im of ζ(1/2+it) of width about 2e-3; each mpmath value
lies inside its interval.

| t | N (EM order 3, ε ≈ 1e-3) | kernel time | µs/term | peak RSS (part / assembly) |
|---|---|---|---|---|
| 100 | 500 | 0.15 s | 297 | 0.45 / 3.0 GB |
| 1000 | 8,000 | 2.04 s | 256 | 1.04 / 2.99 GB |
| 10000 | 125,500 | 29.4 s | 234 | 1.82 / 3.02 GB |
| 30000 | 470,000 | 106.6 s | 227 | 1.82 / 3.09 GB |

**Per-term breakdown.**
- cos/sin of t log n: 107 µs.
- √n: 26 µs.
- log increment: 17 µs.
- Assembly and accumulation: about 75 µs.

**Kernel facts that constrain certificate design.**
- The kernel runs about 6.5e5 primitive `Nat` ops per second.
- `Int` is 21x slower. Typeclass notation costs another 4x.
- `brecOn` recursion is 5x slower than raw `Nat.rec`.
- `Bool ==` costs about 13 µs per use.
- The kernel retains about 4 KB per reduction step inside one declaration, so the work must be
  chunked (500 terms per chunk).
- A single file gets no intra-file parallelism. RSS grows about 36 MB per chunk theorem, which
  caps a file at about 40 chunks.
- Olean output is about 23 bytes per kernel-evaluated term.

**RS main-sum benchmark** (RS-design seat; timing probes only, with no soundness claim). A 211-term
RS main sum at t = 280000 costs 21.6 ms of kernel time at 64 bits (cos only), or 37 ms at 128 bits
(cos and sin plus a radius accumulator).

### 3.2 Cost model

**Formula.**

```
kernel_seconds ≈ c_term × (terms per evaluation) × (evaluations), summed over the seam
c_term ≈ 2.3e-4 s at P = 64 bits (measured; 3.8e-4 at P = 128; 5.9e-4 at P = 256)
EM order 3:   terms(t, ε) = ⌈(abs(s(s+1)(s+2)) / (180 ε))^{2/5}⌉  ≈ t^1.2 ε^-0.4
              (predicted 108 s at t = 30000; measured 106.6 s)
EM order 2K+1: remainder ~ 2ζ(2K)/(2π)^{2K} · abs((s)_{2K}) · N^{-(2K-1/2)}; K ≤ 6 cuts N 20-56x
Riemann-Siegel: terms(t) = ⌊√(t/2π)⌋ (211 at 2.8e5, 399 at 1e6), about 0.1-0.2 ms/term measured
```

**Evaluation counts.**
- On-line: at least one sign point per zero; 445,947 at h280000, about 1.75e6 at 10^6.
- Off-line (edges and caps): 60 to 100 evaluations per distinct edge height (80 in the headline);
  13,235 heights at h280000 and 44,537 at 10^6.
- Off-line work comes to about 2 to 3 times the on-line work.

### 3.3 Verdicts

Figures assume 32 cores at 90 percent parallel efficiency and ε = 1e-2.

| height | method | H1 (on-line) | full seam | verdict |
|---|---|---|---|---|
| h280000 | order-3 EM (exists) | 3.7e4 core-h ≈ 54 days (≈ 17 with the unproven rotor) | ≈ 1.3e5 core-h ≈ **5 months** (4-7); **13 TB of oleans for H1 alone** vs 42 GB free | **INFEASIBLE** on this machine (disk alone rules it out) |
| h280000 | EM order ≤ 13 (K ≤ 6) | 1.8 days | **6.2 days** (4.9 with rotor); about 1.5 TB of oleans at 500-term chunks | **DAYS of compute**, gated on unformalized theory (order-K EM identity, off-line FE-reflected evaluator, K6c, K2) and on a larger-chunk certificate format for disk |
| h280000 | Riemann-Siegel | 3-9 core-h | **under 1 hour** on 32 cores (on-line); off-line needs B6 | **DAYS end to end once the bricks exist**; compute is negligible, theory is the gate (section 4) |
| 10^6 | order-3 EM | 6.8e5 core-h (78 core-years) | 190-260 core-years | **INFEASIBLE** |
| 10^6 | EM order ≤ 13 | 27 days | 79 days (60 with rotor; 55 at K ≤ 12) | **WEEKS to months (about 11 weeks)**; marginal |
| 10^6 | Riemann-Siegel | about 1 core-h | **3-4 hours** | **DAYS end to end** after the bricks, plus the 8 remaining T5 driver legs to produce the band list (about 2 days wall per `COMPUTE_PLAN_AND_ladder_1e6`) |
| 10^9 | Riemann-Siegel, pure kernel | about 200-300 core-years | | **INFEASIBLE** kernel-only; the A0 verdict (kernel spot checks, native bulk) stands, and native bulk is a trust input this program does not accept |

**Skeptic caveats.**
1. P = 64 will not hold at the top for order-3 EM at ε = 1e-3. The extrapolated radius is about
   2e-2, so P = 128 is needed, which makes the order-3 figures about 1.4x too low. The verdict is
   unchanged.
2. The rotor (shared partial sums across the grid points of a band) is a cost proxy only; its error
   analysis is not formalized. At G = 8 it underestimates by 1.3x.
3. The order-K EM and RS rows rest on remainder bounds that are not yet formalized.

---

## 4. The Riemann-Siegel route

### 4.0 Brick B0, theta: DONE

**File.** `Probes/RSDesign_theta.lean` (652 lines). This author re-elaborated it independently:
`lake env lean`, 42 s wall. It printed seven axiom lines, each exactly
[propext, Classical.choice, Quot.sound]. A forbidden-token scan found only the header phrase
"no `sorry`".

**Headline theorems.**

- `lam_bracket`: an elementary convex-trapezoid bracket for the Gauss branch of Im log Γ, for any
  base x > 0 and any start index n0. The remainder is at most y/(4(x²+y²)).
- `theta_bracket (t > 0)`: thetaS t − 1/(2t) ≤ Λ − (t/2) log π ≤ thetaS t.
- `gaussBranch_theta_sub_thetaMain_le {t} (ht : 0 < t)`: there is a Λ, the limit of
  `imLnVal (1/4) (t/2)`, with abs(Λ − (t/2) log π − ZeroFreeBridge.thetaMain t) ≤ 1/t. This is
  the DESIGN_AND_ladder_1e9 section 3.3 statement with t ≥ 200 weakened to t > 0. The memo wrote
  `ZetaReflection.imLnVal`; the actual constant is `ThetaGap.imLnVal`.
- `theta_280000_box`: phase width 1.8e-6. The mpmath value 2.2434215934 lies inside it. A negative
  control that sets the upper endpoint below the true value fails `linarith`.

**Budget comparison.** The 1e9 memo budgeted steps T1 to T5 at 1,700 to 2,800 lines and 3 to 5
agent-weeks. They took about 600 lines. T6 is still open, but only the counting side needs it
(the Γℝ verticals). The sign side does not.

**Consequence for K5.** The Γℝ vertical enclosures (H2f) follow pointwise from `lam_bracket`:
- at σ = 2, use x = 1;
- at σ = −1, shift Γ(z) = Γ(z+1)/z, then use x = 1/2.

Complex Stirling is therefore not on the critical path for H1 or H2f. It is still needed only if
the off-line evaluator reflects through the functional equation (the χ factor); `lam_bracket`
covers its imaginary part there too.

### 4.1 Constants

| quantity | value | source | status |
|---|---|---|---|
| Gabcke K = 0, C0 kept | abs(R0) < 0.127 t^{-3/4}, t ≥ 200 | Hiary arXiv 1507.01261 eq. (11); Gabcke 1979 | literature |
| Gabcke K = 1 | abs(R1) < 0.053 t^{-5/4}, t ≥ 200 | Bober-Hiary arXiv 1607.00709; Pugh thesis | literature |
| Charter text "0.053 t^{-3/4}" | pairs the K = 1 constant with the K = 0 exponent | PROGRAM_ANDURIL A3 | **needs correction** (proposed op O-3) |
| Titchmarsh | (3/2)(t/2π)^{-3/4} = 5.95 t^{-3/4}, for t/2π > 125 | Titchmarsh section 15.4 / 1935 Thm 2 | fails 11 bands to 280000 |
| max abs(C0) | cos(π/8) < 0.93 | Gabcke p. 65 | any bound without C0 certifies at most 58 percent of bands |
| theta | abs(φ − thetaMain) ≤ 1/t; bracket width 1/(2t) | `RSDesign_theta` | **kernel-proved** |
| worst gap margins (max abs(Z) between consecutive zeros) | < 200: 0.257; [200, 1e3): 0.081; [1e3, 1e4): 3.97e-3 (Lehmer pair, 7005.08); [1e4, 1e5): 5.44e-4 (71732.909); [1e5, 2.8e5): 2.006e-4 (hidden pair at 273193.666) | float64 RS scan (2.79e7 points) plus mpmath refinement | untrusted; design only |

### 4.2 The remainder budget: take c = 2, not 2.4

The RS-design seat reports that "any c t^{-3/4} with c ≤ 2.4 certifies 100 percent" of bands. That
figure compares c t^{-3/4} with the gap margin alone. This author checked the two binding gaps
with mpmath, adding the theta error in the form Z = 2(cos θ A + sin θ B) with the midpoint of
`theta_bracket`, which enters as 2(abs(A)+abs(B))/(4t):

| t (gap maximum) | margin | 2 t^{-3/4} | 2.4 t^{-3/4} | theta error term |
|---|---|---|---|---|
| 273193.666 | 2.006e-4 | 1.67e-4 | 2.01e-4 | 2.2e-7 (abs(A)+abs(B) = 0.12) |
| 71732.909 | 5.437e-4 | 4.56e-4 | 5.48e-4 | 2.9e-6 (abs(A)+abs(B) = 0.42) |

**Findings.**
- c = 2.4 is **not** safe. At 71732.909 it exceeds the margin before any theta or evaluator error,
  and at 273193.666 it has no room left for them.
- c = 2 leaves 16 to 17 percent headroom at both points.
- **The registered Prop should say c = 2.** Gabcke's 0.127 implies it with 15.7x slack.
- The evaluator must use the A/B form, not the worst-case 4√N δ theta bound. The worst-case form
  costs 5.3e-5, which would consume the c = 2 headroom at the hidden pair.
- The grid must be adaptive. At the hidden pair, abs(Z) exceeds 1.67e-4 only on a subinterval of
  a gap 0.0057 wide.

Scripts: `scratchpad/abcheck.py` and `scratchpad/abcheck2.py`.

### 4.3 Bricks, with line estimates

| brick | content | lines | status / dependency |
|---|---|---|---|
| B0 theta | `lam_bracket`, `theta_bracket`, `gaussBranch_theta_sub_thetaMain_le` | about 600 | **DONE** (probe; needs promotion to `RSTheta.lean`) |
| T6 bridge | Gauss-branch Λ equals an analytic branch with deriv = logDeriv Γℝ, so `lam_bracket` serves `argChangeVert Gammaℝ` (H2f) | 800-1,500 | staffable now |
| B1 RS vocabulary | rsN via an integer-sqrt certificate, rsP, A(t), B(t), C0 term, `rsZ0`, and ONE named Prop `RSRemainder c t0` | 200-400 | staffable now |
| B4 numeric bridge | Nat-only fixed-point RS main-sum evaluator plus soundness: log n table (n ≤ 211; ≤ 399 at 10^6), reduction mod 2π with Mathlib d20 π (enough to about 1e6), general-order Horner via `Complex.exp_bound`, invSqrt, C0 kept away from p = 1/4, 3/4, theta via `theta_bracket` | 1,000-2,000 (about 1,600 reusable from ArbEcon Eval/Sound) | staffable now |
| B5 checkBandRS | `checkBandRS_correct (hRS : RSRemainder 2 200)`, returning the TuringBand `hLine` shape via `gLine_sign_decomp_t` and the IVT; this is K4 | 600-1,000 | after B1, B4 |
| B2 RS representation | Riemann's Hankel contour plus pole crossing (Titchmarsh 2.10 / 4.16). The Mathlib pin has rectangle Cauchy and Gaussian Fourier, but no Hankel contour and no residue API | 3,000-6,000 | research; first of its kind |
| B3 saddle bound | explicit abs(R0) ≤ 2 t^{-3/4} for t ≥ 200: model integral for C0, Taylor-remainder inequalities, exponential tails (Titchmarsh 1935 Thm 2 template with the constant tightened from 5.95 to 2; or Arias de Reyna 2011 Part I; **not** the Part II lemmas, which were checked only by plots) | 2,000-5,000 | after B2 |
| B6 off-line evaluator | general-σ RS (or FE-reflected EM at low t) for H2c caps and H2e horizontal edges; on-line RS discharges none of the 93,411 `hArbT` conjuncts | +50-100 percent of B2+B3 (about 2,500-11,000) | after B2; parallel to B3 |
| generic hArbT bricks | K0, K1, K2, K6a, K6c (+K6d) | about 2,500-3,500 (B-3..B-6 of the h280000 memo, less what `lam_bracket` removes) | K0/K1/K6a staffable now |
| emitter rewrite | re-emit 10,379 (then about 41.7k) bands with kernel certificates in place of binders | about 800 py | after B5, B6 |

**Totals.** About 12,000 to 30,000 lines of new Lean. The low end assumes B6 reuses most of B2 and
B3 through a general-σ statement from the start.

### 4.4 Critical path

```
now ── B1 ─┬─ B4 ─┬─ B5 ──> RS-conditional hLine for all 10,379 bands (trust: RSRemainder 2 200)   [4-7 aw]
           │      │
T6 ────────┴──────┴──> H2f kernel                                                              [parallel]
K0, K1, K6a, H3(K2 + small-t evaluator) ──> generic hArbT families + hγ                          [parallel, 2-4 aw]

B2 (Hankel) ──> B3 (c = 2) ──> RSRemainder discharged                                          [8-16 aw: LONG POLE]
       └──────> B6 (general σ) + K2 + K6c ──> H2c, H2e                                          [+4-10 aw]

all of the above ──> emitter rewrite ──> h280000 compute (hours) ──> 1e6 driver legs (about 2 days) + compute (hours)
```

**Timing.**
- Two lanes are long poles:
  - B2 → B3, which discharges RSRemainder;
  - B2 → B6, which covers the off-line families.
- Everything else fits inside them.
- Critical-path estimate with parallel staffing: about 12 to 23 agent-weeks (B2, then B3 or B6),
  with compute measured in hours.

**Pivot if B3 stalls.**
- With Titchmarsh's constant (c = 5.95), 11 bands fail; with c = 10, 25 fail.
- Those bands can fall back to order-K EM at the hard points: about 75 points at about 15 s each,
  once order-K EM exists.

---

## 5. The ordered plan to make every ANDURIL node hypothesis-free

In this section, "hypothesis-free" means a proved artifact whose closure has no Arb or oracle
binder, with axioms [propext, Classical.choice, Quot.sound].

**Owner approval.**
- **Any change to a registered statement needs the owner's approval.** That includes a
  strengthening, a weakening and a re-registration.
- Ops that only add draft nodes, links, attempts or readback notes do not need it.
- Every grant follows a blind adversarial audit.

### Step 1: register what is already proved (no new math)

- **O-1** `mission add anduril AND_g2_reflected_band_kernel`.
  - kind "milestone"; `depends_on = ["AND_checkline_correct", "AND_em_tail3_number", "AND_first_zero_kernel"]`.
  - `statement_module = "Statements.AND_g2_reflected_band_kernel"`.
  - Statement file: the verbatim span `namespace ReflectedBand_t14_Kernel` / `def dK` / `theorem okK` /
    `theorem pilot_kernel` (pre-flight `statement_matches` = True).
  - Then `mission link` with artifact `../../examples/zeta_reflection/lean/ReflectedBand_t14_Kernel.lean`,
    `artifact_kind = "lean_module"`, `via = "direct"`, `closure_clean = true`.
  - Append an attempts.jsonl row (verdict Proved, session pilot-discharge-2026-09-23).
  - Blind audit, then `grant`.
  - *No approval needed.*
- **O-2** Append to the `AND_g2_reflected_band` readback: "[2026-09-23] Hypothesis-free companion
  AND_g2_reflected_band_kernel proves the same conclusion without hmem binders; the tight Arb boxes
  of d remain undischarged." Leave its statement and `closure_clean = false` as they are.
  - **Alternative (OWNER APPROVAL, strengthening):** re-point `AND_g2_reflected_band`'s statement to
    the `dK`/`pilot_kernel` span. This is a strengthening, because the hypothesis-free conclusion
    implies the conditional one. Afterwards the node itself is closure-clean. Recommended: the
    companion, because it keeps the historical Arb pilot visible.
- **O-3** Correct the charter text in PROGRAM_ANDURIL A3 (a docs edit, not a registry op): "0.053 t^-3/4"
  becomes "abs(R0) < 0.127 t^-3/4 (C0 kept) or abs(R1) < 0.053 t^-5/4, t ≥ 200".
- **O-4** Promote `Probes/RSDesign_theta.lean` to `RSTheta.lean`, adding a lean_lib, AxiomGuard lines and CI.
  Then `mission add anduril AND_theta_branch`: kind "lemma", `depends_on = ["AND_stirling_binet_k1",
  "AND_first_zero_kernel"]`, with statement

  ```
  theorem gaussBranch_theta_sub_thetaMain_le {t : ℝ} (ht : 0 < t) :
      ∃ Λ : ℝ, Filter.Tendsto (ThetaGap.imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
        |Λ - t / 2 * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t
  ```

  Then link, audit and grant.
  - **OWNER APPROVAL:** the 1e9 memo proposed `200 ≤ t` and `ZetaReflection.imLnVal`. Registering
    with `0 < t` is a strengthening, and the namespace is a correction. Registering the memo's
    `200 ≤ t` form would need no approval, and the artifact proves it too.
- **O-5** Promote `Probes/ArbEconomics_{Eval,Sound,Zeta,T*}` to a lean_lib. This is a lakefile
  decision for the lead. Then add `AND_em_zeta_kernel_eval`, kind "lemma",
  `depends_on = ["AND_em_tail3_number", "AND_em_zeta_strip"]`, with anchors `ArbEcon.I_T30000.zeta_re/zeta_im`
  and `ArbEcon.chunk_sound`. Link, audit and grant.
- **O-6** CI: add `KernelBandEnclosures`, `ReflectedBand_t14_Kernel`, `AxiomGuardArbKernel`, `RSTheta`
  and the ArbEcon lib to `telperion-zeta-reflection.yml`. This is a lead or infra op, and no grant
  should rely on CI until it is done.

**After step 1**, all six proved nodes plus the two or three new ones are hypothesis-free, except
`AND_g2_reflected_band` if the companion route is chosen.

### Step 2: draft the bricks (op R8, widened)

**New draft nodes** (no approval needed; each takes the standard by-design placeholder):

| node | kind | depends_on | content |
|---|---|---|---|
| `AND_band_glue` | lemma | — | K0 |
| `AND_edge_clear_glue` | lemma | — | K1; H2b is dischargeable at once |
| `AND_height_floor_kernel` | lemma | `AND_em_zeta_kernel_eval` | H3: no zero with 0 < Im < 55/16, hypothesis-free; K2 plus the small-t evaluator; removes `hγ` at every height |
| `AND_argchange_generic` | lemma | `AND_theta_branch` | K6a (σ = 2 via the Λ(n) series) + K6b (Γℝ verticals via `lam_bracket` + T6) |
| `AND_argchange_halfplane` | lemma | — | K6c |
| `AND_rs_remainder_c0` | lemma | `AND_rs_representation` | `RSRemainder 2 200` (see 4.2); B3 |
| `AND_rs_representation` | lemma | — | B2 |
| `AND_rs_main_sum_eval` | lemma | `AND_theta_branch`, `AND_em_zeta_kernel_eval` | B4 |
| `AND_checkband_rs` | lemma | `AND_rs_main_sum_eval`, `AND_checkline_correct` | B5 |
| `AND_rs_offline_edge` | lemma | `AND_rs_representation` | B6 |
| `AND_em_zeta_orderK` | lemma | `AND_em_tail3_number` | optional fallback lane |

**Dependency edits** (no approval needed; they change the DAG, not a statement):
- **R8 as widened:** `AND_ladder_1e9.depends_on += [AND_theta_branch, AND_rs_remainder_c0,
  AND_rs_main_sum_eval, AND_checkband_rs, AND_rs_offline_edge]`.
- `AND_ladder_h280000.depends_on += [AND_band_glue, AND_edge_clear_glue, AND_height_floor_kernel,
  AND_argchange_generic, AND_argchange_halfplane, AND_checkband_rs, AND_rs_remainder_c0,
  AND_rs_offline_edge]`. These are the route-B prerequisites for the hypothesis-free statement as
  registered.
- `AND_ladder_1e6` inherits them through its existing `depends_on AND_ladder_h280000`.

**Retitle and readback** for `AND_ladder_h280000` (title and readback only, no statement change):
- Replace the claim that each BandHyp "is discharged by the kernel-checked RHInBoxT band modules".
- The replacement says that the band modules consume Arb data, and that the hypothesis-free statement
  waits on the route-B bricks listed above.

### Step 3: the generic families (short, parallel)

1. Prove `AND_band_glue` and `AND_edge_clear_glue`. With `zeta_zero_re_mem_strip` this discharges
   H2b: 10,379 binders, with no numerics.
2. Prove `AND_height_floor_kernel` with the ArbEcon evaluator at t ≤ 3.44. It needs about 10^2 to
   10^4 net points at N = 10 to 20; min abs((s−1)ζ) = 0.730 gives the slack. This removes `hγ` at
   every height.
3. Prove `AND_argchange_generic` (H2d, H2f) and `AND_argchange_halfplane` (the lemma for H2e; the
   per-edge numerics come in step 5).

### Step 4: the RS-conditional ladder (4 to 7 agent-weeks)

1. Build B1, then B4 and B5 in parallel.
2. Re-emit the bands with kernel-checked sign certificates. All 10,379 `hLine` binders then reduce
   to the single Prop `RSRemainder 2 200`.
3. **Registry side (optional; OWNER APPROVAL, a statement change):** register an intermediate node
   `AND_ladder_h280000_rs` whose statement carries `(hRS : RSRemainder 2 200)` plus the remaining
   off-line binders. It would make the ladder's residual trust a single literature-backed Prop.
   Nothing about `AND_ladder_h280000` itself changes.

### Step 5: the long poles

1. B2, then B3, discharges `AND_rs_remainder_c0`.
2. B6 together with K2 and K6c discharges H2a, H2c and H2e at 13,235 edge heights.
3. Emit h280000 band certificates with no binders. The compute is hours.
4. Build the indexed capstone with `hbands` and `hγ` discharged, which is the **registered
   hypothesis-free statement**. Link, audit and grant `AND_ladder_h280000`. No approval is needed,
   because the statement is unchanged.

### Step 6: 1e6

1. Run the 8 remaining T5 driver legs (about 2 days wall) to fix the band list up to 10^6.
2. Emit with the same machinery. RS compute is 3 to 4 hours; the off-line compute grows
   proportionally.
3. Grant `AND_ladder_1e6` under its registered hypothesis-free statement.

### Step 7: 1e9 and 1e13

Under the measured economics these nodes **cannot be made hypothesis-free kernel-only**. The kernel
cost is about 200 to 300 core-years at 1e9 and more at 1e13. They stay open. Any re-scope is an
**OWNER decision**. Admitting `native_decide` would add a trust input, which this program's rule
excludes. Record this in their readbacks (no approval needed for a readback note).

### Where route A stands

The h280000 design memo's route A, re-registering h280000 with binders (shape A2), is a **weakening
and needs OWNER APPROVAL**. It does not advance the hypothesis-free goal. It remains a legitimate
interim honesty fix if the owner wants a grantable conditional node now. If so, it should be a
separate node, for example `AND_ladder_h280000_cond`, rather than an edit of the hypothesis-free
target.

---

## 6. What was not checked

**Checked by the skeptics, not by this author.**
- The pilot and economics builds, axiom guards, negative controls and timings. The skeptics re-ran
  them; this author did not.
- The RS-design skeptic's verdict never reached this memo. For that seat this author re-elaborated
  `Probes/RSDesign_theta.lean` only (seven axiom lines clean, token scan clean). This author did not:
  - re-run its negative control;
  - re-run its benchmarks;
  - re-run its 2.79e7-point Z scan, the hidden-pair refinement or the band classification.

**Literature and untrusted numerics.**
- The RS constants (0.127, 0.053, 5.95) were taken from the cited secondary sources. Nobody checked
  them against Gabcke's thesis.
- `RSRemainder 2 200` is justified by Gabcke's published theorem. It is not formalized, and its truth
  is not kernel-checked.
- All margin, gap and scan statistics are float64 or mpmath. They are untrusted and serve design only.
- The section 4.2 check covers two gaps only. It does not include evaluator rounding or the
  C0-term error.

**Projections, not measurements.**
- The order-K EM and RS compute rows are projected from remainder bounds times the measured per-term
  cost.
- No kernel run exceeded t = 30000 for EM. The RS figure at 280000 is a timing probe without
  soundness.
- The rotor speedup is unproved.
- The P = 64 → P = 128 transition was extrapolated.
- The edge and cap workload (80 evaluations per edge height) comes from a 16-edge mpmath sample.

**Not checked or not run.**
- No registry op was run, and no `statement_matches` pre-flight was run for any proposed node except
  `AND_g2_reflected_band_kernel`.
- The `Guard_h280000` axiom battery was not re-run here.
- CI does not cover any new module. The island has no working CI.
- The `lakefile.toml` diff (42 lines, from the pilot seat) was not reviewed line by line in this memo.
- Lines, agent-week and calendar estimates for B2, B3 and B6 are design estimates. No part of B2 or
  B3 has been attempted.
- Disk footprint was not checked for a larger-chunk certificate format. It is the binding constraint
  for any EM route and still matters (about 1.4 GB) for RS at h280000.
- Whether the off-line families can use FE-reflected EM, rather than general-σ RS, at heights above
  1e4 was not measured.

conjecture1_proved = False.
