# Stage S4 notes: the jump lemma (CC Thm 3.6 via Rem 3.7) (2026-10-11)

Branch `mm/arch-s4`, island `telperion/examples/rvm_bridge/lean`.
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, sections 1 (row 4), 2.3, 4 (rows S4, S4').
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes were touched.

## 1. The statement, derived before proving

### Which function plays ξ

CC Thm 3.6 is about D∘Q(ξ∗ξ*), with Q acting on the convolution square f = ξ∗ξ*.
In our variable the pole-free tests are g = h' − h/2 (S2, `poleFree_iff_exists_lift`).
The convolution square of g is
  autocorr g = −(autocorr h)'' + ¼·autocorr h,
because the cross terms −½(h'⋆h̃ + h⋆h̃') cancel by integration by parts, and h'⋆h̃' = −(h⋆h̃)''.
So autocorr g = Q₊(autocorr h) with CC's Q₊ = −∂² + ¼, and **ξ = h**, the S2 lift, not g.
(On the Fourier side this is S2's `hsq_lift`: |ĝ|² = (r² + ¼)|ĥ|².)
The sign of the lift (CC use h/2 − h') is invisible: autocorr(−g) = autocorr g.

### Which δ, in which variable

CC (48)/(49): for ρ ≥ 1, δ(ρ) = 4ρ^{1/2}∫₀¹cos(2πρt)cos(2πt)(−log t)dt
= 2ρ^{1/2}[Si(2π(1+ρ))/(2π(1+ρ)) + Si(2π(ρ−1))/(2π(ρ−1))].
Mathlib has no Si, and no smoothness theory for parametric integrals.  So S4 uses
  S(a) := ∫∫_{[0,1]²} cos(a·s·r) ds dr   (= Si(a)/a for a ≠ 0, = 1 at a = 0),
which is CC's ∫₀¹cos(at)(−log t)dt after integrating out the product s·r = t.
It is smooth in a with bounded derivatives, by differentiation under a finite-measure integral.
  Φ(x) := 2e^{x/2}[S(2π(1+eˣ)) + S(2π(eˣ − 1))]   (all x ∈ ℝ; smooth),
  δ(e^{|x|}) = Φ(|x|)                               (CC's D₊ kernel; the kink is at x = 0).
Φ is the smooth extension of x ↦ δ(eˣ) from x ≥ 0 across 0.  For x < 0 it is NOT δ(e^{|x|}).
Two facts carry the whole lemma:
  Φ(0) = 2(S(4π) + 1) = 2.2374848…  (CC (50))   and   Φ'(0) = 1  (CC: δ' jumps from −1 to +1).
Φ'(0) = 1 is exact: Φ'(0) = S(4π) + 1 + 4π S'(4π) + 4π S'(0), S'(0) = 0, and
S(a) + a S'(a) = ∫₀¹cos(as)ds, which is 0 at a = 4π.

### The kernel K^δ_I (normalisation and interval)

  κ(x) := −Φ''(|x|) + ¼Φ(|x|)     (CC: (Q₊δ)(e^{|x|}), the even extension of the x > 0 values)
  K^δ(v, w) := κ(v − w)            on I × I, I = [−L, L] (the h-interval = the g-interval)
No normalising factor: the operator is ⟨ξ, K ξ⟩ = ∫∫ conj ξ(v) K(v,w) ξ(w) dv dw on L²(I, du).
CC's L²(√I, d*ρ) is our L²([−L, L], du) under ρ = eᵘ (d*ρ = du).

### The jump lemma (target)

For IsWeilTest h with g = h' − h/2 (equivalently: g pole-free, tsupport g ⊆ [−L, L], h = qLift g L):
  D(autocorr g) := ∫ autocorr g(u)·Φ(|u|) du
                 = −2·Φ'(0)·∫|h|² + ∫ autocorr h(u)·κ(u) du
                 = −2‖h‖² + ⟨h, K^δ_I h⟩.
The general form (any C² Φ, Rem 3.7) keeps Φ'(0) as the jump coefficient; δ's Φ'(0) = 1 gives −2.

## 2. What is proved

All declarations are kernel-checked with axioms exactly `[propext, Classical.choice, Quot.sound]`.
Check: `lake build ArchS4_Rung && lake env lean ArchS4_Guard.lean` (79 `#print axioms` lines, all standard).
No `sorry`, no `axiom`, no warnings in the S4 modules.

| file | lines | content |
|---|---|---|
| `ArchS4_Delta.lean` | 270 | the square moments, `ccS`, `deltaE`, smoothness, Φ(0), Φ'(0) = 1 |
| `ArchS4_Jump.lean` | 475 | autocorr of the lift, Remark 3.7, the jump lemma, the kernel K^δ_I and its properties |
| `ArchS4_Rung.lean` | 284 | S4' pipeline test: closed form of κ, sup bound, D∘Q ≤ 0, conditional positivity |
| `ArchS4_Guard.lean` | 83 | `#print axioms` for all 79 top-level declarations |

Build time on the loaded machine: about 40 s per module.

### The δ kernel (`ArchS4_Delta`)

```lean
def sq : Measure (ℝ × ℝ) := (volume.restrict (Icc 0 1)).prod (volume.restrict (Icc 0 1))
def mom (φ : ℝ → ℝ) (k : ℕ) (a : ℝ) : ℝ := ∫ p, (p.1 * p.2) ^ k * φ (a * (p.1 * p.2)) ∂sq
def Cm k a := mom Real.cos k a        def Sm k a := mom Real.sin k a
def ccS (a : ℝ) : ℝ := Cm 0 a         -- CC's Si(a)/a = ∫₀¹ cos(at)(−log t) dt
def deltaE (x : ℝ) : ℝ :=
  2 * Real.exp (x / 2) * (ccS (2 * π * (1 + Real.exp x)) + ccS (2 * π * (Real.exp x - 1)))

theorem contDiff_deltaE : ContDiff ℝ ⊤ deltaE
theorem ccS_zero : ccS 0 = 1
theorem ccS_add_mul_deriv (a : ℝ) : ccS a + a * deriv ccS a = ∫ s in (0:ℝ)..1, Real.cos (a * s)
theorem integral_cos_mul_eq_sinc (a : ℝ) : ∫ s in (0:ℝ)..1, Real.cos (a * s) = Real.sinc a
theorem deltaE_zero : deltaE 0 = 2 * (ccS (4 * π) + 1)               -- CC (50)
theorem deriv_deltaE_zero : deriv deltaE 0 = 1                        -- the jump
```
The last two identities together say (a·ccS)' = sinc, i.e. a·ccS(a) = Si(a); Mathlib has no `Si`, so this is not stated.

### The jump lemma (`ArchS4_Jump`)

```lean
theorem autocorr_lift (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    autocorr g = fun x => -deriv (deriv (autocorr h)) x + autocorr h x / 4
theorem mass_lift (hh : IsWeilTest h) (hgh : ...) : mass g = mass (deriv h) + mass h / 4   -- S2 open item
theorem jump_ibp {A : ℝ → ℂ} (hA : ContDiff ℝ 2 A) (hAc : HasCompactSupport A)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) :
    ∫ u, deriv (deriv A) u * (Φ |u| : ℂ)
      = 2 * ((deriv Φ 0 : ℝ) : ℂ) * A 0 + ∫ u, A u * ((deriv (deriv Φ) |u| : ℝ) : ℂ)   -- CC Rem 3.7
theorem jump_lemma_general (hh) (hgh) {Φ} (hΦ : ContDiff ℝ 2 Φ) :
    ∫ u, autocorr g u * (Φ |u| : ℂ)
      = -2 * ((deriv Φ 0 : ℝ) : ℂ) * (mass h : ℂ)
        + ∫ u, autocorr h u * ((-deriv (deriv Φ) |u| + Φ |u| / 4 : ℝ) : ℂ)

def kappaD (x : ℝ) : ℝ := -deriv (deriv deltaE) |x| + deltaE |x| / 4    -- CC (Q₊δ)(e^{|x|})
def KdeltaI (v w : ℝ) : ℝ := kappaD (v - w)
abbrev boxI (L : ℝ) : Set (ℝ × ℝ) := Icc (-L) L ×ˢ Icc (-L) L

theorem jump_lemma (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ) = -2 * (mass h : ℂ) + ∫ u, autocorr h u * (kappaD u : ℂ)
theorem jump_lemma_window (hh) (hgh) (hsupp : tsupport h ⊆ Icc (-L) L) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ)
      = -2 * (mass h : ℂ) + ∫ p in boxI L, conj (h p.1) * (KdeltaI p.1 p.2 : ℂ) * h p.2
theorem jump_lemma_poleFree (hg : IsWeilTest g) (hsupp : tsupport g ⊆ Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    ∫ u, autocorr g u * (deltaE |u| : ℂ)
      = -2 * (mass (ArchS2.qLift g L) : ℂ)
        + ∫ p in boxI L, conj (ArchS2.qLift g L p.1) * (KdeltaI p.1 p.2 : ℂ) * ArchS2.qLift g L p.2
```
Kernel facts for S5 (K^δ is ℝ-valued by its type):
```lean
theorem KdeltaI_symm (v w : ℝ) : KdeltaI v w = KdeltaI w v
theorem continuous_KdeltaI : Continuous fun p : ℝ × ℝ => KdeltaI p.1 p.2
theorem memLp_KdeltaI (L : ℝ) : MemLp (fun p : ℝ × ℝ => KdeltaI p.1 p.2) 2 (volume.restrict (boxI L))
theorem integrable_sq_KdeltaI (L : ℝ) :
    Integrable (fun p : ℝ × ℝ => KdeltaI p.1 p.2 ^ 2) (volume.restrict (boxI L))
theorem autocorr_pairing_eq_box (hh) (hsupp) {k : ℝ → ℝ} (hk : Continuous k) (hev : ∀ x, k (-x) = k x) :
    ∫ u, autocorr h u * (k u : ℂ) = ∫ p in boxI L, conj (h p.1) * (k (p.1 - p.2) : ℂ) * h p.2
```
`autocorr_pairing_eq_box` holds for any even continuous kernel, so S8 can reuse it for K_I with χ.

### S4': the δ rung, a pipeline test (`ArchS4_Rung`)

```lean
theorem kappaD_eq (x : ℝ) : kappaD x = -2 * Real.exp (|x| / 2) * (FE1 |x| + FE2 |x|)
theorem abs_kappaD_le {x : ℝ} (hx : |x| ≤ 1 / 40) : |kappaD x| ≤ 35
theorem norm_autocorr_le (hh : IsWeilTest h) (u : ℝ) : ‖autocorr h u‖ ≤ mass h
def Dfun (f : ℝ → ℂ) : ℂ := ∫ u, f u * (deltaE |u| : ℂ)
theorem DQ_nonpos (hh) (hgh) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80) (hsupp : tsupport h ⊆ Icc (-L) L) :
    (Dfun (autocorr g)).re ≤ 0
theorem DQ_nonpos_poleFree (hg) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80) (hsupp) (h0 : paperFT g (I / 2) = 0) :
    (Dfun (autocorr g)).re ≤ 0
theorem weil_nonneg_of_CC_cor23 (hg) (hL0) (hL : L ≤ 1 / 80) (hsupp) (h0)
    (hCC : 0 ≤ (archSide (autocorr g)).re + (Dfun (autocorr g)).re) :
    0 ≤ (weilForm (autocorr g)).re
```
The closed form: the ¼Φ terms cancel, so κ(x) = 2e^{y/2}[4πe^y(S₁(α)+S₁(β)) + 4π²e^{2y}(C₂(α)+C₂(β))], y = |x|.
It matches mpmath to 20 digits (κ(0) = 8.39172…, κ(0.3) = 13.1424…).
The bounds |S₁| ≤ 1/4 and |C₂| ≤ 1/9 come from the square moments ∫∫(sr)^k = 1/(k+1)².

## 3. Open items

* **S3 is a hypothesis, not a theorem.**  `weil_nonneg_of_CC_cor23` assumes CC Cor 2.3 as `hCC`.
  The form of `hCC` (archSide = W∞ on the pole-free class, D = `Dfun`) must be checked against S3's statement at merge.
  If S3 defines δ another way (Si, or the −log t weight), an identification lemma with `deltaE` is needed.
* **The window of S4' is crude.**  It is L ≤ 1/80 = 0.0125, from a sup bound on κ.
  CC's 0.0488 needs a certified ∫₀^{2L}|κ| (piecewise enclosures of S₁, C₂), and 0.0933 needs λ_max(K^δ_I) ≤ 2.
  Both are below the proved L ≤ 1/10.  The rung is a pipeline test only.
* **Smooth tests only.**  The jump lemma is stated for IsWeilTest h, not for every ξ ∈ L²(I) as in CC.
  Extending it by density needs S5's operator bounds.
* **No operator yet.**  K^δ_I is given as a kernel with the properties S5 asked for.  It is not packaged as an operator on L²(I); that is S5's API.
* **Wiring left to the coordinator.**  `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched.
  `ArchS4_Delta`, `ArchS4_Jump`, `ArchS4_Rung` and `ArchS4_Guard` are registered as `lean_lib`s at the end of `lakefile.toml`.

## 4. Lean footguns met

* **Integral binder scope.**  `-∫ u, X u + Y / 4` parses as `-∫ u, (X u + Y / 4)`.  Parenthesise: `-(∫ u, X u) + Y / 4`.
  The pretty-printer hides this, and the symptom is a `rw` that "does not find" an identical-looking term.
* **Casts of `deriv`.**  For Φ : ℝ → ℝ, `(deriv Φ 0 : ℂ)` elaborates `deriv` at the wrong type.  Write `((deriv Φ 0 : ℝ) : ℂ)`.
* **No `HasDerivAt.comp_neg`.**  Use `(hf (-u)).scomp u (hasDerivAt_neg u)`.
* **`rw [h.deriv]` with Pi products.**  `.mul` produces the function `f * g`, which does not match `fun x => f x * g x` syntactically.  State the `HasDerivAt` with an explicit lambda first.
* **`rw [sq]` fails** with "equation theorems"; use `pow_two`.
* **`2 ≤ ↑⊤` in `WithTop ℕ∞`.**  `exact_mod_cast le_top` fails.  Use `by exact_mod_cast contDiff_infty.1 h 2`.
* **`integral_add` after `.neg`.**  Pass `(f := …) (g := …)` explicitly; otherwise the pattern contains `(-fun u => …) a`.
* **`HasCompactSupport.comp_left (g := …) (by simp)` inline** hit a `whnf` heartbeat timeout once.  State the composed function `(fun z => ‖z‖ ^ 2) ∘ h` in a `have` first.
* **Parametric smoothness.**  Mathlib has no `contDiff_parametric_integral` and no `contDiff_sinc`.  Integrating over the unit square with the finite measure `sq` and constant domination by 1 makes `hasDerivAt_integral_of_dominated_loc_of_deriv_le` a one-liner per derivative.

## 5. Bridge to S3 (`ArchS4_Bridge.lean`, 79 lines, added after merging mm/archimedean-rung)

S3's δ and S4's δ are the same function.  The guard now has 85 lines, all `[propext, Classical.choice, Quot.sound]`.
```lean
theorem ccS_eq_sincInt (a : ℝ) : ccS a = ArchS3.sincInt a
theorem deltaK_eq_deltaE (u : ℝ) : ArchS3.deltaK u = deltaE |u|
theorem S3_Dfun_eq (g : ℝ → ℂ) : ArchS3.Dfun g = (Dfun (autocorr g)).re
theorem S3_Dfun_nonpos_poleFree (hg : IsWeilTest g) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 80)
    (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0) : ArchS3.Dfun g ≤ 0
theorem weil_nonneg_of_Lfun_nonneg (hg) (hL0) (hL : L ≤ 1 / 80) (hsupp) (h0)
    (hLf : 0 ≤ ArchS3.Lfun g) : 0 ≤ (weilForm (autocorr g)).re
theorem weil_nonneg_of_ell_nonneg (hell : ∀ r, 0 ≤ ArchS3.ell r) (hg) (hL0) (hL : L ≤ 1 / 80)
    (hsupp) (h0) : 0 ≤ (weilForm (autocorr g)).re
```
Once S3's M3 proves `∀ r, 0 ≤ ArchS3.ell r`, one application of `weil_nonneg_of_ell_nonneg` makes the L ≤ 1/80 rung unconditional.
Open item 1 of section 3 is now closed on the definitional side.  The remaining dependence is S3's M3.
