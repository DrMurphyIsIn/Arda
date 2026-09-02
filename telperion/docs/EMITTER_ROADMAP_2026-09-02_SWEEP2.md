# Telperion emitter roadmap — SECOND SWEEP of the RH + BG corpora (2026-09-02)

A second, deeper pass over the Riemann-zeta / Borel–Carathéodory (`examples/zero_free_bridge`,
`examples/borel_caratheodory`) and Brualdi–Goldwasser / P=NP (`examples/{bg_*, g1_floors,
knapsack_sos, lorentzian, mconvex, matching_free_energy, gauge_lift, …}`) Lean corpora, after the
**8 sweep-1 candidates all shipped** (`EMITTER_ROADMAP_2026-09-02_RH_CROSSCUT.md`; the README table
now lists all 46 built emitter modules).

**Honest headline: the corpus is mature.** Sweep 1 crystallized every obvious finitely-certifiable
positivity core and linear-arithmetic assembly. Sweep 2's yield is **2 solid + 2 defensible** new
candidates — all sitting at the finite-data boundary the existing emitters already patrol — plus a
rigorous confirmation that the remaining recurring shapes are already covered, decorative
(`norm_num`-only), inherently analytic (Mathlib's job), or already-roadmapped fold-ins. This
near-emptiness is itself a useful finding: the certificate surface of these two campaigns is close to
saturated.

The emitter criterion applied throughout: **an emitter needs an untrusted deterministic computation
guarded by an exact anti-phantom gate** (a rational inequality/identity re-checked in exact
arithmetic), then emits a *parameterized copy* of a fixed skeleton. A rigid universally-quantified
analytic statement with no finite data to re-verify is a Mathlib lemma, not an emitter.

`conjecture1_proved = False` throughout — classical-analysis / proof-complexity tooling, not progress
on RH, BG, or P vs NP.

## SHIPPED (2026-09-02) — all 4 candidates below are now built + kernel-verified
Every candidate in this sweep has been implemented, registered (`certify.py` +
`__init__.py`), documented in the README shape table, and its emitted Lean **kernel-verified**
(local `lake build` green, Mathlib v4.32.0, axiom-clean `[propext, Classical.choice, Quot.sound]`) with
a per-emitter CI job: **S1** `PseudoExpectationDualityEmitter` (folds in the bool + parity multilinear
kills; PSD leaf threaded as a hypothesis, self-contained), **S2** `OrderBalanceEmitter`, **S3**
`LFunctionProductEmitter` (emits the (3,4,1) instance faithfully — Mathlib's
`norm_LFunction_product_ge_one` hardcodes that triple; the value-add is the Fejér-admissibility gate),
**S4** `ParametricHolomorphyEmitter` (shipped for completeness but **honestly thin** — heavy fixed
skeleton, `c≥1` restriction to stay faithful; its natural home is the `RayPowerEstimate` lemma pack).
The fold-in dispositions below (Lorentzian→`psd_form`, DiscreteConcavity→`logconcave`) remain sub-mode
work, not built.

---

## New candidates

| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| S1 | **PseudoExpectationDualityEmitter** (`emit_pe_duality`) | "**no degree-`d` SoS refutation** of `{gᵢ = 0}` exists" (feasibility of the moment relaxation): exhibit a pseudo-expectation functional `E` with `E 1 = 1`, `E(s²) ≥ 0` (deg `s ≤ d`), `E(p·gᵢ) = 0`; applying `E` to a would-be `−1 = Σsⱼ² + Σpᵢgᵢ` gives `−1 = (≥0)+0`, contradiction. The **duality complement** of `InfeasibilityEmitter`/`SOSRefutationEmitter` (which prove NO solution; this proves NO low-degree refutation) | `g1_floors/Duality.lean` (`no_refutation`, `pe`, `knapsack_no_refutation`), `Xor3Duality.lean`, `HeawoodDuality.lean` — **3 live instances** + the ad-hoc `knapsack_sos/gen_xor3_duality.py` generator begging to be first-classed (the 08-21 roadmap's P2) | reusable `no_refutation` (`map_add`/`map_sum`/`map_neg` + `Finset.sum_nonneg` + `linarith`) + per-instance `pe` functional (`Finsupp.linearCombination`) + ideal-kills (`MvPolynomial.induction_on'` + support/parity `omega`); the PSD leaf `E(s²)≥0` delegated to `Xor3MomentPSDEmitter`/`psd_form` | M–H | sympy + exact ℤ |
| S2 | **OrderBalanceEmitter** (`emit_order_balance`) | the **integer zero/pole-order hinge** at the 1-line: nonneg-cosine weights `{aⱼ}` and orders `{nⱼ ∈ ℤ}` at `{s₀ + i·cⱼ·t}` (pole at `s=1` gives `n=−1`, zeros give `kⱼ ≥ 0`); the residue-limit combination forces `a₀ ≥ a₁k + a₂k'`, violated for `k ≥ 1` ⟹ **no zero on `Re = 1`**. Distinct from `logderiv_region` (which handles the *continuous* `1/(σ−β)` gap, not the discrete boundary order-balance) | `ZeroFreeBridge.lean:zeta_boundary_contradiction` (the `3·1 − 4k − k' ≥ 0` hinge); the residue *limits* supplied as hypotheses (from `residue_logDeriv`, kept as a Mathlib lemma) | a `(aⱼ,cⱼ,nⱼ)`-parameterized copy reducing to `linarith`/`omega` on the integer residue-limit combination — same exact-ℤ discipline as the shipped `FiniteArgmaxMarginEmitter` | S | exact ℤ |
| S3 | **LFunctionProductEmitter** (`emit_lfunction_product`) | nonneg-cosine tuple `(a₀,…,a_m)` (`aₖ ≥ 0`, Fejér-admissible so `Σ aₖcos kθ ≥ 0`) ⟹ the L-product lower bound `∏ₖ ‖L(σ + i·k·t)‖^{aₖ} ≥ 1` for `Re s > 1`; **names the coupling** of the nonneg-cosine cone to Mathlib's L-function nonvanishing + the admissibility gate (the trig kernel itself is already `zero_free_cosine`) | `ZeroFreeElementary.lean:zeta_norm_product_ge_one` (the fixed 3-4-1 wrapper) | a `(aₖ)`-parameterized copy of `DirichletCharacter.norm_LFunction_product_ge_one` + `LFunction_modOne_eq` + `norm_mul`/`norm_pow`; positivity from the Mertens SOS delegated to `zero_free_cosine`; refuses an inadmissible triple | S–M | sympy |
| S4 | **ParametricHolomorphyEmitter** (`emit_parametric_holomorphy`) — BORDERLINE | `DifferentiableAt ℂ (fun w => ∫ x in Ioi c, b(w,x)/(x:ℂ)^{p(w)}) z` for `Re z > 0`, gated by the exact decay inequalities `−σ₀−1 < −1` (and the log-corrected companion); "analyticity in the parameter of a tail integral", distinct from `dominated_integrability` (which proves the integral merely *exists*) | `StripReprR2.lean:differentiableAt_fractIntegral` | a `(c,σ₀,b-shape)`-parameterized copy of the `hasDerivAt_integral_of_dominated_loc_of_lip` skeleton (7 sub-obligations; Lipschitz-on-convex; `HasDerivAt.const_cpow`) | M–HEAVY | sympy |

**S4 caveat.** Only **one** integrand instance exists (the fract integrand). Per the 2026-09-01 rule
("genuine one-off analytic lemmas → upstream Mathlib PR, not a Telperion shape"), S4 is the thin/heavy
outlier: build it only if a *second* distinct L-function tail-integral instance appears; a lone
instance is better left in the `RayPowerEstimate` lemma pack. Lowest confidence of the four.

## Fold-ins (sub-modes of existing emitters — confirmed, not standalone)
- **Lorentzian / Hodge–Riemann** (`examples/lorentzian`, `(vᵀHw)²−(vᵀHv)(wᵀHw)≥0`) → a
  **signature-`(1,n−1)` input mode of `PSDFormEmitter`** (Schur-complement reduction to a
  completing-the-square Gram; the indefinite `H` never reaches the emitted Lean).
- **DiscreteConcavity** (`bg_caterpillar_concavity`, integer argmax from rational *enclosures* via a
  second-difference sign) → an **enclosure mode of `LogConcaveSinglePointEmitter`**.
- **MultilinearKill** (`E((Xᵢ²−Xᵢ)p)=0` Boolean / `E((Xᵢ²−1)p)=0` ±1) → the **ideal-kill sub-mode of
  S1 `emit_pe_duality`** (never independently stated).

## Examined and confirmed ALREADY COVERED / not-certificate-shaped (with evidence)
- **Full Borel–Carathéodory value/deriv** (`borel_caratheodory_value/_deriv`) — rigid Möbius–Schwarz–
  max-modulus skeleton, no finite data; its constant is already `cauchy_deriv`, its positivity core
  already `halfplane_disk`. Mathlib-lemma territory.
- **Schwarz / max-modulus** (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`,
  `Complex.norm_le_of_forall_mem_frontier_norm_le`) — one-line invocations → the `RayPowerEstimate`
  lemma pack, not emitters.
- **Jensen / Nevanlinna log-counting** (`Σ_ρ Re(1/(s−ρ)) ≤ O(log|t|)`) — the unbuilt dVP crux; an
  inherently analytic estimate Mathlib must supply. Its downstream consumer (the `A/L/−k` gap) is
  already `logderiv_region`.
- **Analytic-continuation identity theorem** (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) —
  rigid; its finite ingredient (preconnectedness) is already `preconnected_cover`, its seed already
  `dirichlet_repr`.
- **M-convexity** (`mconvex`) — decorative (`norm_num`-only rational `≤`; no exchange structure in the
  Lean). **Bregman–Minc / matching free energy** (`entropy`, `matching_free_energy`) → `ExactFact` /
  the shipped `FiniteArgmaxMargin`. **Gauge / benchmark / telescope-product tower** → `RationalIdentity`
  + `ExactFact` + `MonotoneRatioTail` + `TelescopingPotential`. **interp_lemma, rigidity,
  flag_discharge, sos_sdp, putinar, tax_growth, armrate_resize, legs_certs** — all map onto existing
  emitters (evidence: each reduces to `field_simp;ring` / `norm_num` / `positivity` / an existing
  Gram-SOS or Putinar script).
- Prior-roadmap backlog (`SymmetricQuadForm`, `XorClosureStructure` (⊂ S1), `PolytopeMaxMonotone`,
  `SecondOrderRecurrence`, `SingularPSD`, `SeparableConvexExtremum`, `IntegralityGate`,
  `RecursiveDominationRatio`, `AchievabilityClosure`) remains valid and un-duplicated by this sweep.

## Suggested build order
1. **S1 PseudoExpectationDualityEmitter** — highest leverage: 3 live instances, an ad-hoc generator to
   retire, composes with the shipped PSD emitters, and is the marquee P=NP-adjacent shape (subsumes the
   backlog's P2). Low math risk (proofs already kernel-green); the work is API parameterization.
2. **S2 OrderBalanceEmitter** — smallest, pure exact-ℤ, closes the sharp boundary case `logderiv_region`
   doesn't (`ζ(1+it) ≠ 0`); same discipline as the shipped `finite_argmax`.
3. **S3 LFunctionProductEmitter** — thin but clean; first-classes the cosine→L-product coupling for
   sharper zero-free constants and Dirichlet-L analogues.
4. **S4 ParametricHolomorphyEmitter** — defer until a second tail-integral instance justifies it.

Every item discharges a recurring step in the RH/BG/P=NP proof state; none duplicates a shipped
emitter (checked against the 53-row README table + both prior roadmaps). The kernel (local `lake build`
+ CI) remains the sole gate — a wrong certificate is a compile error, never a false theorem.
