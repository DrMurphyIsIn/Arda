# AND_ladder_1e9 (G4, zeta zeros to height 10^9, kernel-only): design memo for the A3 Riemann-Siegel era

*Authored 2026-09-22 for the anduril campaign. Triage and design only: no Lean proof was attempted,
no island was built, no registry mutation was made (the lead owns add/link/grant/attempt). The node
stays `open`, its statement file ends in the by-design placeholder (the file contains no proof; the
CI sorry-scan convention is "no `sorry`" in prose), and nothing in this memo is evidence for or
against the Riemann Hypothesis. Every height-bounded statement discussed here is a finite
verification target.*
**`conjecture1_proved = False`. Nothing here proves RH. RH-equivalent nodes are out of scope.**

Cross-references: `PROGRAM_ANDURIL_2026-09-12.md` (A3 charter note), `ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md`
(G4 row), `WALL_BACKLOG_MAP_2026-09-18.md` (op R8), `RH_ASCENT_PLAN_2026-09-18.md` (F5-4 "Do not staff"),
`REFLECTION_TRACK_DESIGN.md` (sections 2 and 5), `A0_SPIKE_REPORT.md` (measured kernel throughput).

---

## 0. Verdict in one paragraph

`AND_ladder_1e9` is not a proof item this session, not a compute item, and not RH-equivalent. It is a
milestone whose statement is correct (blind-audited clean 2026-09-14, single audit-only `NoGo` attempt
entry, no proof artifact, not grantable) and whose registered gate is wrong: `depends_on` lists only
`AND_ladder_1e6` and `AND_checkline_correct`, while its own title says it is gated on the unauthored
A3 Riemann-Siegel era. The only honest action is `WALL_BACKLOG_MAP` op **R8**: the lead authors three
`draft` brick nodes (`AND_theta_branch`, `AND_rs_main_sum`, `AND_gabcke_c0`) and adds them to
`AND_ladder_1e9.depends_on`, so the DAG stops understating the gate. This memo supplies what R8 needs:
the exact statements in the island's vocabulary, the mathematical route with citations, the substrate
that exists, the obligations with honest line estimates, and a post-A3 compute plan with its trust
seam. Two findings go beyond the charter text and are flagged for the lead in section 7: (a) a
**fourth** gating brick the charter does not name (the two horizontal zeta edges of every band at
height ~10^9 need an off-line evaluator, which neither the theta branch nor the on-line RS formula
supplies), and (b) the measured kernel throughput in `A0_SPIKE_REPORT.md` means the node's title
("3-axiom kernel-only decide") cannot be met at 10^9 by any known certificate economics; the honest
reading, already recorded by A0, is "kernel-only spot-checkable, `native_decide` bulk".

---

## 1. The node as registered

File `missions/anduril/nodes/AND_ladder_1e9.toml`: kind `milestone`, status `open`, created 2026-09-14,
`depends_on = ["AND_ladder_1e6", "AND_checkline_correct"]`. Statement
`missions/anduril/lean/Statements/AND_ladder_1e9.lean`:

```lean
theorem all_nontrivial_zeros_up_to_height_1e9 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000000 → ρ.re = 1 / 2
```

This is the conclusion type of `AllZeros_h280000.all_nontrivial_zeros_up_to_height_280000_of_bands`
(`examples/zeta_zero_localization/lean/AllZeros_h280000.lean:569`) with the height literal at 10^9 and
the ~280 per-segment `BandHyp` binders plus the `hγ` height-floor hypothesis removed. Registry state on
2026-09-22 (`mission status anduril`, read-only): 6 proved (`checkline_correct`, `em_tail3_number`,
`em_zeta_strip`, `first_zero_kernel`, `g2_reflected_band`, `stirling_binet_k1`), 3 open
(`ladder_h280000`, `ladder_1e6`, `ladder_1e9`), 1 draft goal (`ladder_1e13`). Attempts ledger: one
entry for this node, `NoGo`, "Audit only".

Why each of the three usual routes is closed:

* **Not a proof route.** No proof artifact exists in any worktree. Reaching 10^9 needs the
  Riemann-Siegel evaluation era, for which no Lean (or Isabelle, or Coq) formalization exists anywhere
  (`PROGRAM_ANDURIL` finding 3, re-checked by grep over `examples/`: hits are only the theta/Stirling
  substrate in `li_positivity`, `zeta_reflection/StirlingBinet.lean`, and `DlvpTheta`). The charter
  estimate is 12-20 agent-weeks for the three named bricks alone.
* **Not a compute route.** The current T5/EM machinery cannot scale: `REFLECTION_TRACK_DESIGN.md`
  section 2 quantifies kernel-decide Euler-Maclaurin economics as ending at t ~ 1-3*10^4
  (~4*10^9 Int-ops per band at t = 10^5). Wall-clock on the existing route does not reach 10^9 at all;
  the route itself must change (RS main sum is sqrt(t/2pi) terms, EM is ~t terms).
* **Not RH-equivalent.** Finite height; the `nogo` category for RH-equivalent nodes does not apply.
  The predecessor `AND_ladder_1e6` is itself open (current certified height 280,000 with per-segment
  `BandHyp` binders; the hypothesis-free `StripClear` two-box capstone glue is not landed), so even
  the DAG's stated dependencies are undischarged.

---

## 2. What "kernel-only to 10^9" means in the island's vocabulary

The ladder is a fold of `AllZerosUpToHeight.height_chain`
(`examples/zeta_zero_localization/lean/AllZerosUpToHeight.lean:196`):

```lean
theorem height_chain (A B : ℝ)
    (hupA : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ A → ρ.re = 1 / 2)
    (hseg : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → A ≤ ρ.im → ρ.im ≤ B → ρ.re = 1 / 2) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ B → ρ.re = 1 / 2
```

Each segment comes from `all_nontrivial_zeros_in_segment_on_line` (same file, line 176), which needs
(i) `ZetaZeroConfinement.zero_in_band` (zeros of height <= B lie in `a <= Re <= 1 - a` with
`a <= dlvpRateC / log B`, plus the `hγ` floor `55/16 <= |Im|`), and (ii) one band certificate per
tile. Today a band certificate has the T5 shape `TuringBand.BandStatement`
(`examples/zeta_zero_localization/lean/TuringBand.lean:49-66`), which consumes, at band `[T0, T1]`:

* **hLine**: `n` on-line zeros as a strictly increasing list of `t` with
  `completedRiemannZeta (1/2 + t*I) = 0`, produced from `n+1` alternating sign boxes of
  `XiLineZeros.gLine t = (completedRiemannZeta (1/2 + t*I)).re` by the IVT
  (`SignChain.exists_zero_of_sign_change`, `XiLineZeros`).
* **Five edge argument changes** (the RvM edge decomposition,
  `DiffractionCore.zero_count_band_edge_decomp`, `DiffractionCore.lean:1641`):
  `2*pi*N_band = 2*AV(zeta, 2) + AH(zeta, T1, 2, -1) - AH(zeta, T0, 2, -1) + AV(Gamma_R, -1) + AV(Gamma_R, 2)`,
  where `argChangeVert f σ T0 T1 = (∫ y in T0..T1, logDeriv f (σ + y*I)).re` and
  `argChangeHoriz f T x0 x1 = (∫ x in x0..x1, logDeriv f (x + T*I)).im` (lines 949-955).
* **Non-vanishing** of zeta on the two horizontal edges (`σ ∈ [-1, 2]`) and the left edge
  (`Re = -1`), and **confinement** of the ball's zero finset to the open box.

The reflected shape (`ReflectedBand.Statement d`, `CheckBand.lean`; G2 landed as
`AND_g2_reflected_band`) proves the conclusion outright from Int-literal `BandData` checked by
`checkLine` under `decide`, and the height chain consumes both shapes interchangeably. So "kernel-only
to 10^9" means: for every band up to 10^9, all of the above must be established from Int literals by
a once-proven checker, with no `hArbT`-class numeric hypotheses. At t ~ 10^9 that requires, per band:

| quantity | today's discharge (t <= ~10^4) | needed at t ~ 10^9 | gating brick |
|---|---|---|---|
| gLine sign boxes (hLine) | EM zeta on the line x Stirling/Euler-route phase (G2 route B1: `ZeroSignDecomp_t14.gLine_sign_decomp_t`) | Hardy Z via RS main sum + theta | `AND_theta_branch`, `AND_rs_main_sum`, `AND_gabcke_c0` |
| AV(zeta, 2) | prime-power log series (`LogZetaSeries`), height-independent cost | same | none (exists) |
| AH(zeta, T0/T1, 2, -1) | interval-sigma EM Backlund cells (E-track) | an OFF-LINE evaluator at height 10^9 | **unnamed fourth brick** (section 7a) |
| AV(Gamma_R, -1), AV(Gamma_R, 2) | Stirling/Binet K=1 + shift (`StirlingBinet.logDeriv_gammaR_enclosure`) via `LogBranches.argChangeVert_eq_im_log_sub` | height-aware Stirling remainder (the theta-branch lemma at σ = -1, 2) | `AND_theta_branch` (generalized in σ) |
| edge non-vanishing, confinement | `riemannZeta_ne_zero_of_one_le_re`, FE reflection, `ZetaZeroConfinement` | same, but the horizontal-edge non-vanishing again needs the off-line evaluator | fourth brick |

---

## 3. Brick 1: `AND_theta_branch` (the Riemann-Siegel theta on the line, height-uniform)

### 3.1 What exists

The corpus has two representations of theta and no lemma identifying them at general `t`:

* **Integral form** (`ZeroFreeBridge`, `examples/li_positivity/lean/RvMDlvpTheta.lean:82`, mirrored in
  the `zero_free_bridge` island consumed by `zeta_zero_localization`):
  `riemannSiegelTheta t := ∫ u in 0..t, thetaIntegrand u`, with
  `thetaIntegrand u = (1/2) * (digamma (1/4 + (u/2) I)).re - (1/2) * log pi`, plus
  `thetaMain t := t/2 * log t - t/2 * log (2 pi) - t/2 - pi/8` (line 243) with `thetaMain_eq`,
  `thetaMain_hasDerivAt`, and the bridge
  `DiffractionCore.theta_eq_argChangeVert_gammaR : riemannSiegelTheta T = argChangeVert Gammaℝ (1/2) 0 T`
  (`DiffractionCore.lean:1066`). There is **no** bound relating `riemannSiegelTheta` to `thetaMain`.
* **Gauss-product branch** (`zeta_reflection/lean/ThetaValue.lean`, `ThetaConverge.lean`): the
  continuous branch of `Im log Gamma(1/4 + i t/2)` as `Λ(t) = lim_n imLnVal (1/4) (t/2) n` with
  `imLnVal x y n = y log n - Σ_{k<=n} arctan (y/(x+k))` (`imLn_formula`, `exp_Ln_eq_gammaSeq`, both
  proved), boxed at `t = 14` only (`theta_14_box`, rate `C ~ 246`). The sign bridge
  `ZeroSignDecomp_t14.gLine_sign_decomp_t (t) (ht : t ≠ 0) : ∃ Λ M, 0 < M ∧ Tendsto (imLnVal (1/4) (t/2)) atTop (nhds Λ) ∧ gLine t = M * (cos (Λ - (t/2) log pi) * (ζ(1/2+it)).re - sin (Λ - (t/2) log pi) * (ζ(1/2+it)).im)`
  is proved for all `t ≠ 0`; this is exactly `gLine t = M(t) * Z(t)` with `Z` the Hardy function and
  `M(t) = pi^{-1/4} |Gamma(1/4 + it/2)| > 0`, so the hLine side needs only the SIGN of `Z`.
* **Stirling/Binet substrate** (`StirlingBinet.lean`, `AND_stirling_binet_k1` proved):
  `logDeriv_gammaR_stirling`, the shift trick, the K=1 envelope `‖binetRem w‖ <= 1/(Re w - 1)` for
  `Re w >= 2` (modulo the anchor, discharged on the reals), `theta_integrand_enclosure` (line 259).
  **Height blind spot**: this envelope is `O(1/Re w)`, not `O(1/|w|)`; at `w = 1/8 + i t/4 + m` it
  needs `m ~ t` shifts to reach `1/t` accuracy, i.e. it is useless at `t = 10^9`.
  `StirlingK4.binetTail_height_norm_le` keeps the `Im w` contribution per term
  (`‖binetTail w k‖ <= (3/2) / ((Re w + k)^2 + (Im w)^2)`), but the K >= 2 digamma-level peel is
  BLOCKED by a Mathlib gap (no polygamma series, `StirlingK4.lean` header; `StirlingBinetWip.lean`
  carries three placeholders and is not guard-imported).

### 3.2 The design decision: state theta at the log-Gamma level, not the digamma level

At `t = 10^9` the classical expansion `theta(t) = thetaMain(t) + 1/(48 t) + 7/(5760 t^3) + ...` has
`1/(48 t) ~ 2*10^-11`. For sign boxes of `Z` we need `theta mod 2pi` to roughly `10^-6` (Lehmer-like
pairs up to 10^9 have `|Z|` maxima above ~`10^-4`; margin is cheap). So the **K = 1 log-Gamma-level
Stirling remainder** suffices for the whole climb, and the polygamma gap that blocks `StirlingK4` is
irrelevant here: the log-Gamma remainder needs only the order-2 Euler-Maclaurin tail with
`sawBernoulli 2`, which is the `EMZeta`/`EMZetaTail` engine (`AND_em_tail3_number`,
`AND_em_zeta_strip` proved) applied to `f(x) = log (z + x)` instead of `x^{-s}`.

Route (all steps have substrate):

1. `log Gamma(z) = lim_n [ z log n + log n! - Σ_{k=0}^{n} log (z + k) ]` on the continuous branch:
   Mathlib `Complex.GammaSeq_tendsto_Gamma` (`Gamma/Beta.lean:335`) plus the corpus's
   `exp_Ln_eq_gammaSeq`, `imLn_formula`.
2. Euler-Maclaurin (order 2) on `Σ_{k=0}^{n} log (z + k)`:
   `Σ = ∫_0^n log(z+x) dx + (log z + log(z+n))/2 + (1/12)(1/(z+n) - 1/z) - ∫_0^n sawBernoulli 2 (x) / (2 (z+x)^2) dx`
   (the `em_zeta_strip` proof pattern with `sawBernoulli`, `bernoulliFun`).
3. `n -> ∞` with Mathlib Stirling for `log n!`: `Stirling.log_stirlingSeq_formula`,
   `Stirling.tendsto_stirlingSeq_sqrt_pi` (`Analysis/SpecialFunctions/Stirling.lean:67, 239`).
   Result: `log Gamma(z) = (z - 1/2) log z - z + (1/2) log (2 pi) + R(z)`,
   `R(z) = -∫_0^∞ sawBernoulli 2 (x) / (2 (z+x)^2) dx`.
4. **Height-aware remainder**: `|sawBernoulli 2| <= 1/6` gives
   `|R(z)| <= (1/12) ∫_0^∞ dx / |z + x|^2 = (1/12) * (pi/2 - arctan (Re z / Im z)) / Im z <= pi / (24 Im z)`
   for `Re z >= 0, Im z > 0` (Mathlib `integral_inv_one_add_sq` after the substitution). At
   `z = 1/4 + i t/2`: `|R| <= pi / (12 t) < 0.27 / t`.
5. Elementary closed form of `Im [(z - 1/2) log z - z]` at `z = 1/4 + i t/2` against `thetaMain`:
   `arg z = arctan (2t)` (`ThetaValue.arg_eq_arctan_of_re_pos`), `log |z| = log (t/2) + (1/2) log (1 + 1/(4t^2))`,
   difference `<= 3/(16 t) + O(1/t^3)`. Combined with step 4: `|theta(t) - thetaMain t| <= 1/t` for
   `t >= 200`, with room to spare (true value `~ 1/(48 t)`).
6. **Identification of the two thetas** (needed by the counting side, which consumes
   `argChangeVert Gammaℝ` through `theta_eq_argChangeVert_gammaR`): apply
   `LogBranches.argChangeVert_eq_im_log_sub` (`zeta_reflection/lean/LogBranches.lean:43`) with `L` the
   Gauss-product branch of `log Gammaℝ`. Its hypotheses are `AnalyticOnNhd ℂ L S` and
   `deriv L = logDeriv Gammaℝ` on an open `S` containing the segment: the branch must be shown analytic
   with the right derivative, i.e. locally uniform convergence of `L_n` (not just pointwise
   `GammaSeq_tendsto_Gamma`). This is the hardest sub-obligation of the brick.

### 3.3 Proposed registered statement (island vocabulary, `ZeroFreeBridge` namespace via `ANDDefs`)

Statement only; the registered file ends in the standard by-design placeholder.

```lean
-- Hypothesis-free, height-uniform: the Riemann-Siegel theta equals its Stirling main term
-- to within 1/t for t >= 200.  Serves hLine (through gLine_sign_decomp_t) and the Gamma_R edges.
theorem riemannSiegelTheta_sub_thetaMain_le {t : ℝ} (ht : 200 ≤ t) :
    |ZeroFreeBridge.riemannSiegelTheta t - ZeroFreeBridge.thetaMain t| ≤ 1 / t
```

and, so that the on-line consumer does not need step 6 first, a companion in the `Λ` vocabulary:

```lean
theorem gaussBranch_theta_sub_thetaMain_le {t : ℝ} (ht : 200 ≤ t) :
    ∃ Λ : ℝ, Filter.Tendsto (ZetaReflection.imLnVal (1/4) (t/2)) Filter.atTop (nhds Λ) ∧
      |Λ - (t/2) * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t
```

Vocabulary to add to `Statements/ANDDefs.lean` (verbatim copies, per its header discipline):
`ZeroFreeBridge.thetaRay`, `thetaIntegrand`, `riemannSiegelTheta`, `thetaMain`
(`RvMDlvpTheta.lean:30, 69, 82, 243`) and `ZetaReflection.imLnVal` (`ThetaValue.lean:180`).

### 3.4 Obligations and estimates (Lean lines, agent-weeks)

| id | obligation | substrate | est. |
|---|---|---|---|
| T1 | `Λ(t)` exists for all `t` (generalize `ThetaConverge` from `t = 14` to a rate uniform in `t`) | `ThetaConverge.lean`, `ArctanTaylor` | 300-500 lines |
| T2 | order-2 EM identity for `Σ_{k<=n} log (z+k)`, `Re z > 0` | `EMZeta.lean`, `EMZetaTail.lean` (proof pattern of `em_zeta_strip`) | 600-900 |
| T3 | `n -> ∞` limit with Mathlib Stirling; the constant `(1/2) log (2 pi)` | `Stirling.tendsto_stirlingSeq_sqrt_pi`, `GammaSeq_tendsto_Gamma` | 300-500 |
| T4 | height-aware bound `|R(z)| <= pi/(24 Im z)` | `integral_inv_one_add_sq`, `sawBernoulli` bounds (`EMZetaTail`) | 200-400 |
| T5 | closed form vs `thetaMain`, `<= 1/t` for `t >= 200` | `arg_eq_arctan_of_re_pos`, `thetaMain_eq` | 300-500 |
| T6 | the two thetas coincide: branch analytic, `deriv L = logDeriv Gammaℝ`, then `argChangeVert_eq_im_log_sub` and `theta_eq_argChangeVert_gammaR` | `LogBranches.lean`, `DiffractionCore.lean:1066` | 800-1500 |
| T7 | the same enclosure at `σ = -1` and `σ = 2` for `AV(Gammaℝ, ·)` (note `Re (z/2) = -1/2 < 1/4` at `σ = -1`: use `Gamma` reflection or one shift, then T4) | `StirlingBinet.logDeriv_gammaR_stirling_shift` | 300-600 |

Total ~2,800-4,900 lines, **3-5 aw**. Mathlib gaps: none hard (no polygamma needed at this level);
the analytic-branch lemma T6 is the one genuinely delicate piece.

---

## 4. Brick 2: `AND_rs_main_sum` (the Riemann-Siegel formula on the line) and Brick 3: `AND_gabcke_c0`

### 4.1 Statement shape

Vocabulary (to be added to `ANDDefs.lean` as AUTHORED definitions, since none exist on any island):

```lean
namespace ZetaReflection
/-- Hardy's Z as the corpus already sees it: the real part of e^{i theta} zeta(1/2+it).
    (That this is the whole of e^{i theta} zeta on the line is a separate fact, not needed
    for signs: gLine t = M t * hardyZ t with M t > 0 is ZeroSignDecomp_t14.gLine_sign_decomp_t.) -/
noncomputable def hardyZ (t : ℝ) : ℝ :=
  Real.cos (ZeroFreeBridge.riemannSiegelTheta t) * (riemannZeta (1/2 + (t:ℂ) * Complex.I)).re
  - Real.sin (ZeroFreeBridge.riemannSiegelTheta t) * (riemannZeta (1/2 + (t:ℂ) * Complex.I)).im
noncomputable def rsN (t : ℝ) : ℕ := ⌊Real.sqrt (t / (2 * Real.pi))⌋₊
noncomputable def rsP (t : ℝ) : ℝ := Real.sqrt (t / (2 * Real.pi)) - rsN t
noncomputable def rsMainSum (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 (rsN t), (n : ℝ) ^ (-(1/2 : ℝ)) *
    Real.cos (ZeroFreeBridge.riemannSiegelTheta t - t * Real.log n)
/-- Gabcke's C0, in the form regular at p = 1/4, 3/4 (the cos/cos quotient has removable
    singularities there; the registered def must use the regularized form or the Taylor series
    in (p - 1/2), else the statement is false at those p). -/
noncomputable def gabckeC0 (p : ℝ) : ℝ := Real.cos (2 * Real.pi * (p^2 - p - 1/16)) / Real.cos (2 * Real.pi * p)
noncomputable def rsCorr0 (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (rsN t - 1) * (t / (2 * Real.pi)) ^ (-(1/4 : ℝ)) * gabckeC0 (rsP t)
end ZetaReflection
```

Registered statements (statement only, placeholder-terminated in the node files):

```lean
-- AND_rs_main_sum: the RS formula with a remainder that is o(1) in t (the summit's structural half).
theorem hardyZ_eq_rsMainSum_add {t : ℝ} (ht : 200 ≤ t) :
    ∃ R : ℝ, ZetaReflection.hardyZ t = ZetaReflection.rsMainSum t + ZetaReflection.rsCorr0 t + R
      ∧ |R| ≤ ZetaReflection.gabckeBound0 t          -- gabckeBound0 t := c0 * t ^ (-(3/4 : ℝ))

-- AND_gabcke_c0: the explicit constant.  See 4.3 on the literal before registering.
theorem gabcke_c0_remainder {t : ℝ} (ht : 200 ≤ t) :
    |ZetaReflection.hardyZ t - ZetaReflection.rsMainSum t - ZetaReflection.rsCorr0 t|
      ≤ (127 / 1000) * t ^ (-(3/4 : ℝ))
```

Splitting the two nodes this way keeps the charter's pivot ladder addressable: if the explicit
Gabcke constant does not land, `AND_rs_main_sum` can be re-pointed at an explicit-constant AFE with a
weaker remainder (section 4.4) without touching the theta or numeric-bridge work.

### 4.2 Mathematical route and citations

* Siegel, "Uber Riemanns Nachlass zur analytischen Zahlentheorie" (1932); Edwards, *Riemann's Zeta
  Function*, ch. 7 (the integral `ζ(s) = ... ∫_{0↙1} e^{iπx^2} x^{-s} / (e^{iπx} - e^{-iπx}) dx`
  and the saddle-point evaluation); Gabcke, *Neue Herleitung und explizite Restabschatzung der
  Riemann-Siegel-Formel*, Dissertation Gottingen 1979 (the explicit bounds `|R_K(t)| <= c_K t^{-(2K+3)/4}`,
  `t >= 200`); Berry, "The Riemann-Siegel expansion for the zeta function: high orders and remainders",
  Proc. R. Soc. A 450 (1995); Arias de Reyna, "High precision computation of Riemann's zeta function
  by the Riemann-Siegel formula, I", Math. Comp. 80 (2011) 995-1009 (a modern, general-`s` derivation
  with explicit remainder bounds, the natural template for a formalization and the source for the
  off-line evaluator of section 7a); Odlyzko-Schonhage, "Fast algorithms for multiple evaluations of
  the Riemann zeta function", Trans. AMS 309 (1988) (only relevant to the untrusted producer);
  Platt, "Isolating some non-trivial zeros of zeta", Math. Comp. 86 (2017); Platt-Trudgian, "The
  Riemann hypothesis is true up to 3*10^12", Bull. LMS 53 (2021) (state of the art for the
  *unverified-kernel* computation; their sign-box discipline is what the certificate emitter should
  mimic).
* The proof has three layers, and the corpus has prior art only for the third:
  (R2) the exact integral representation (contour through the saddle at `x = sqrt(t/2pi)`): needs
  Cauchy's theorem on a strip with Gaussian decay at both ends; Mathlib has rectangle Cauchy
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) and the corpus's `RHInBoxAnalytic`
  argument-principle layer, but no shifting-of-contours-to-infinity lemma library. (R3) the
  asymptotic evaluation of the remainder integral to order 0 with an explicit constant: Gabcke's
  thesis is ~150 pages of explicit estimates; Arias de Reyna's derivation is shorter and cleaner but
  still delivers its bounds through auxiliary functions defined by their own integrals. (R4) the
  numeric bridge from the analytic statement to Int-literal boxes, which is the reflection track's
  home ground (`TrigReduce`, `TaylorKernels`, `CertVerify`, `ArctanTaylor`, `DIntv`).

### 4.3 The constant literal (flag for the lead before any registration)

The charter text (`PROGRAM_ANDURIL` A3, `REFLECTION_TRACK_DESIGN` section 5) quotes the C0-only
remainder as `|R| <= 0.053 * t^{-3/4}, t >= 200`. As this author recalls Gabcke's table, `0.127` is the
K = 0 constant (exponent `-3/4`) and `0.053` is the K = 1 constant (exponent `-5/4`); the charter line
appears to pair the K = 1 constant with the K = 0 exponent. Either literal is far more than sufficient
at `t = 10^9` (`0.127 * t^{-3/4} ~ 2*10^-8`), but a registered statement with the wrong literal would
be false, so the lead should resolve it against the thesis (or Arias de Reyna 2011, Theorem 4.2 and
the table following it) before the `draft` node's statement file is generated. The proposed
statement above uses `127/1000` pending that check.

### 4.4 The pivot ladder (kill criteria as in `REFLECTION_TRACK_DESIGN` section 5)

1. **Gabcke C0** (target). Two monthly reviews without the saddle/contour layer (R2) landing =>
2. **Explicit-constant approximate functional equation** (Hardy-Littlewood; Titchmarsh 2nd ed.
   Thm 4.13 / 4.16). With `x = y = sqrt(t/2pi)` the error is `O(t^{-1/4})`, i.e. ~`5*10^-3` at
   `10^9`. Two honest caveats: (i) the constants in the textbook proofs are not explicit and would
   have to be extracted (this author knows no citable explicit-constant AFE at the accuracy needed);
   (ii) `5*10^-3` is NOT enough near Lehmer-like pairs, so an AFE-only era leaves a residue of sign
   boxes that cannot be closed, and those bands would carry hypotheses again. The AFE is a partial
   fallback, not a full one.
3. **EM-era-only reflection** (terminal): kernel-checked bands to t ~ 10^4 only; `AND_ladder_1e9`
   stays open permanently on the kernel-only route and G4 is re-scoped (section 7b).

### 4.5 Obligations and estimates

| id | obligation | substrate | est. |
|---|---|---|---|
| R1 | definitions `hardyZ`, `rsN`, `rsP`, `rsMainSum`, `gabckeC0` (regularized), `rsCorr0`; `gLine t = M t * hardyZ t` re-expressed with `riemannSiegelTheta` (needs T6 or the `Λ`-form statement) | `ZeroSignDecomp_t14` | 200-400 lines |
| R2 | the RS integral representation of `ζ(1/2+it)` (Siegel's contour formula), including the functional-equation half and the Gaussian-decay contour shifts | Mathlib rectangle Cauchy, `RHInBoxAnalytic`, `riemannZeta_one_sub` (`RiemannZeta.lean:178`), `completedRiemannZeta_one_sub` | 3,000-6,000 lines, 4-8 aw |
| R3 | order-0 saddle-point evaluation with Gabcke's explicit constant | none in any assistant | 2,000-5,000 lines, 4-8 aw |
| R4 | numeric bridge: `log n` dyadic certificates (verify-not-compute, `exp` brackets), exact integer `⌊sqrt(t/2pi)⌋` with `pi` to ~40 digits (Machin via `ArctanTaylor`; Mathlib's `Real.pi_gt_3141592` is 6 digits, not enough for mod-2pi at `t = 10^9`), `cos` after reduction (`TrigReduce`), `gabckeC0` near `p = 1/4, 3/4` via its Taylor form | `TrigReduce`, `TaylorKernels`, `CertVerify`, `DIntv` | 1,500-3,000 lines, 2-3 aw |
| R5 | `checkBand` extension: an RS-era `BandData` (per grid point: the boxes of `theta`, of each `cos` term or of the folded sum) and the once-proven `checkBandRS_correct` in the `ReflectedBand.Statement d` shape so the chain consumes it unchanged | `CheckBand.lean`, `FullyReflectedBand_t14.checkBandFull_correct` | 600-1,000 lines, 1-2 aw |

Total for bricks 2 and 3: ~7,300-15,400 lines, **11-21 aw**. Together with the theta branch the
charter's 12-20 aw is at the optimistic end; **15-26 aw** is the honest range for the three named
bricks, before the fourth (section 7a).

---

## 5. After A3: the compute plan for the climb (D3) and its trust seam

This section exists so that the lead can see that "cluster weekend, kernel-only decide" in
`PROGRAM_ANDURIL` WS-D was written before `A0_SPIKE_REPORT.md` measured the kernel, and what the
measured numbers imply. Nothing here is actionable until A3 lands.

**Sizes.** `N(10^9) ~ (T/2pi) log(T/(2pi e)) ~ 2.85*10^9` zeros (vs 432,474 certified today at
280,000 and ~1.8*10^6 at 10^6). Band width 40 (today's tiling) gives ~`2.5*10^7` bands; at the top
each holds ~120 zeros (density `log(t/2pi)/(2pi) ~ 3` per unit height). The RS main sum has
`rsN(10^9) = 12,615` terms.

**Jobs.**

| job | input | output (certificate shape) | composes into |
|---|---|---|---|
| J1 producer (untrusted) | band `[T0,T1]`; Arb/FLINT `acb_dirichlet_hardy_z_zeros` (`src/telperion/arb_platt.py:150`) and `acb_dirichlet_hardy_z` for grid points | candidate grid `t_0 < ... < t_n` with alternating `Z` signs, dyadic candidate boxes for `theta(t_i)`, each `log n`, `pi`, and the folded sum | J2 input; never trusted |
| J2 RS-era `BandData` file | J1 output | Int-literal `BandData` + `theorem ok : checkBandRS d = true := by decide` (kernel island) or `native_decide` (flagged sibling island) + `band := checkBandRS_correct d ok : ReflectedBand.Statement d` | one `hbands` conjunct of a segment |
| J3 horizontal edges | J1-style candidates for `ζ(σ + iT)` cells over `σ ∈ [-1,2]` at `T0`, `T1` | Backlund-cell boxes checked by the off-line evaluator's checker (fourth brick) | the `AH` conjuncts and edge non-vanishing |
| J4 Gamma_R and Re=2 edges | Stirling main term + T4 bound; prime-power series | Int-literal `Im L` differences | the `AV` conjuncts |
| J5 segment glue | 25 bands | `segment_A_B` via `all_nontrivial_zeros_in_segment_on_line` | `height_chain` fold |
| J6 capstone | all segments | `all_nontrivial_zeros_up_to_height_1e9` (hypothesis-free requires the `StripClear` `hγ` discharge, the same glue `AND_ladder_h280000` is waiting on) | the node |

**Cost.** Per grid point at the top: 12,615 terms x ~60 Int-ops (reduction + `cos` Taylor + mul/add)
~ `7.5*10^5` Int-ops; ~150 points per band => ~`1.1*10^8`; plus two horizontal edges at ~30 cells x
`~10^6` => ~`6*10^7`; call it `~2*10^8` Int-ops per band at the top, `~10^8` averaged over the climb,
`~2.5*10^15` Int-ops total. At the **measured** pure-kernel `~1.5*10^4` Int-ops/s (A0 report):
`~1.7*10^11` core-seconds, i.e. **thousands of core-years**; pure `decide` at 10^9 is out by three to
four orders of magnitude, and no certificate trick removes the sum (a sum's cheapest certificate is
the sum). At `native_decide` speeds (`10^7-10^8` Int-ops/s, compiled GMP Int): `~1-8` core-years,
which is a **32-core month to a 32-core year**, or a large-cluster weekend only at the top of that
range. Disk is the second binding constraint (F5-2 records the 280,000 monolith at 117 GB of
`.lake`, B2 sharding at ~16 GB after prune); `2.5*10^7` band files of ~100 KB each is ~2.5 TB of Lean
source before oleans, so the B2/B3 sharding and single-fold chain are prerequisites of the climb,
not optimizations.

**Trust seam after A3.** Kernel: `checkBandRS_correct`, `checkBand_correct` for edges, the RS/Gabcke/
theta theorems, the RvM edge decomposition, `height_chain`, Mathlib. Remaining hypotheses: none per
band on the reflected route (that is the point of G4); the capstone's `hγ` floor until `StripClear`
lands; and, if the hybrid charter's `native_decide` is used for bulk bands, `Lean.ofReduceBool` on
those bands with the documented random kernel-only spot-check protocol (charter decision 1). The
node's title ("3-axiom kernel-only") is met only by the spot-checked bands.

---

## 6. What the node would and would not establish

Would: every zero of `riemannZeta` with `0 < Im ρ <= 10^9` has `Re ρ = 1/2`, as a Lean theorem whose
axioms are `propext`, `Classical.choice`, `Quot.sound` on the spot-checked bands and additionally
`Lean.ofReduceBool` on `native_decide` bands (an `AxiomGuard` file per block, as today). Trivial zeros
have `Im = 0` and are excluded by the hypothesis. The count `N(10^9)` would be an in-kernel integer.

Would not: anything about zeros above `10^9`; anything about RH (`RH_ASCENT_PLAN` F5 standing label:
"instrumentation, not evidence"; certified prefixes are morally forced by on-line verification and
were already known to `3*10^12` by Platt-Trudgian 2021 without kernel checking); anything about the
`AND_ladder_1e13` goal, which the charter routes through a flagged `native_decide` island and external
compute regardless. `conjecture1_proved = False` before, during and after.

---

## 7. Flags for the lead (beyond op R8 as written)

**7a. A fourth gating brick the charter does not name.** Every T5/reflected band at height `T` needs
`argChangeHoriz riemannZeta T 2 (-1)` at `T = T0, T1` and non-vanishing of `ζ` on those edges
(`TuringBand.lean:55-56, 61-62`). The theta branch and the on-line RS formula say nothing about
`ζ(σ + iT)` for `σ ≠ 1/2`; at `T ~ 10^9` the E-track's interval-sigma EM is exactly the machinery
the charter says dies at `10^4`. Two closures, both unauthored:

* **General-`s` Riemann-Siegel with explicit remainder** (Arias de Reyna 2011 covers `σ` in a range
  including `[1/2, 2]`; the `σ < 1/2` half of the edge reflects through `riemannZeta_one_sub`). Same
  architecture as R2/R3, roughly +50-100 % of their cost; keeps the RvM box chain unchanged. This is
  the recommended closure: it reuses everything and touches no chain glue.
* **Turing's method** (Turing 1953; Lehman 1970; Trudgian, "Improvements to Turing's method",
  Math. Comp. 80 (2011): `|∫_{t1}^{t2} S(t) dt| <= 2.067 + 0.059 log(t2/2pi)` for `t2 > t1 > 168 pi`).
  Needs only on-line `Z` and theta, but formalizing Littlewood's lemma plus explicit `|ζ|` bounds in
  the strip and the Gram-block counting argument is its own 6-10 aw, and it replaces
  `TuringBand.BandStatement` (which despite its name is an RvM box, not Turing's method) with a new
  segment shape and new chain glue.

Suggested registry op: either author a fourth `draft` node `AND_rs_offline_edge` (title recording the
Arias de Reyna route and the Turing alternative) as a dependency of `AND_ladder_1e9`, or widen
`AND_rs_main_sum`'s statement to general `s` from the start. The lead decides; this memo registers
nothing.

**7b. The title's "3-axiom kernel-only decide" vs the measured kernel.** `A0_SPIKE_REPORT.md`
already concluded "the 10^9 kernel-only milestone (G4) as literally pure `decide` is not supported by
these numbers; G4 should be read as kernel-only-spot-checkable". Section 5's arithmetic agrees by
three to four orders of magnitude. The node title should be amended when R8 is executed, so the
registry does not carry a milestone whose literal reading no plan can meet. This is a title edit,
not a statement edit: the Lean statement is axiom-agnostic and stays as registered.

**7c. Sequencing.** `ROADMAP` G4 row: staff A3 only after the E-track lands, because the EM tail
engine is A3's substrate. `AND_em_zeta_strip` and `AND_em_tail3_number` are proved, so the
theta-branch brick (section 3) is staffable now at 3-5 aw and is the cheapest, least speculative
piece; it also pays off inside the EM era (the Gamma_R edges at every height). Bricks 2-3 and the
fourth brick remain "Do not staff" per `RH_ASCENT_PLAN` F5-4 until an operator re-charters a
quarter-scale effort or an external RS formalization appears (`RH_ASCENT_PLAN` trigger 3).

**7d. Dependencies to record on the three drafts.** `AND_theta_branch` depends on
`AND_stirling_binet_k1`, `AND_em_tail3_number`; `AND_rs_main_sum` depends on `AND_theta_branch`;
`AND_gabcke_c0` depends on `AND_rs_main_sum`; `AND_ladder_1e9` gains all three (and the fourth if
authored). `AND_ladder_1e13` already lists `AND_ladder_1e9` and inherits the gate.

---

## 8. Environment notes (for whoever eventually builds)

Islands built in this worktree: `rvm_bridge`, `li_positivity` only. Built copies of
`zeta_zero_localization` and `zeta_reflection` exist in `~/arda-million` and `~/arda-anduril-mod2pi`
(both at Mathlib rev `81a5d257c8`, toolchain v4.32.0; reflink with `cp -Rc`, then diff
`lake-manifest.json` package revs before trusting). One `lake build` per island at a time. None of
this was exercised for this memo, because no proof is attemptable at this node.

`conjecture1_proved = False`.
