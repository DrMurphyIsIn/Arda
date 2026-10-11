# Stage S8 notes: the E∘Q kernel, abstract form (2026-10-11)

Branch `mm/arch-s8`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 1 rows 9-14 and section 4 row S8.
Source: Connes-Consani arXiv:2006.13771 ("CC"), sections 4-5 and Appendix F, read from the PDF text.
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes were touched.

## What S8 proves

All 82 top-level theorems print exactly `[propext, Classical.choice, Quot.sound]`.
Check with `lake build ArchS8_Kernel && lake env lean ArchS8_Guard.lean`.
There is no `sorry` and no `axiom`.

| file | lines | content |
|---|---|---|
| `ArchS8_Volterra.lean` | 393 | the Volterra rule; CC Lemma 5.2 (96); the core of Lemma 5.1 |
| `ArchS8_ProlateData.lean` | 419 | the interface; ε (84); Prop 5.3 (97)/(99); Lemma 5.4; Rem 5.6 |
| `ArchS8_Kernel.lean` | 575 | CC (102); Lemma 5.1 (correlation form); Prop 5.5; χ(0) = 0; the S2 bridge |
| `ArchS8_Guard.lean` | 96 | `#print axioms` for all 82 theorems |

Each module builds in about 33 s on the loaded machine.

### The idea that makes it cheap

Everything is done in the additive variable t = log ρ, so ρ∂_ρ is ∂_t and CC's Q = −(ρ∂_ρ)² + 1/4 is Q₊ = −∂_t² + 1/4.
CC's matrix coefficient for ρ ≥ 1 is
k(ρ) = ⟨ξ | ϑ(ρ⁻¹) ζ⟩ = ρ^{1/2} ∫_{ρ⁻¹}^1 ξ(x) ζ(ρx) dx.
The substitution x = e^{−s} turns it into a truncated (Volterra) convolution:
k(e^t) = ∫_0^t a(s) b(t − s) ds, with a(s) = e^{−s/2} ξ(e^{−s}) and b(u) = e^{u/2} ζ(e^u).
This is `volt_aOf_bOf`.

CC's boundary terms are then just the Volterra rule (volt F G)' = F(t)G(0) + volt F G'.
The two ways of differentiating volt a b agree, and that agreement is CC's integration by parts.
No differentiation of improper integrals over (0, ∞) is needed anywhere.

The function ε is smooth on (−T, T) as a function of t.
Its even extension ε(|t|) has the derivative jump of CC Lemma 5.4.
So ε'(1⁺) is an honest two-sided derivative of the smooth branch at t = 0.
Remark 3.7 is two integrations by parts on [0, R] and on [−R, 0].

### Statements (namespace `ArchS8`)

**Lemma 5.2, CC (96) at ρ = e^t.**  This holds for every real t, and for C¹ real ξ and ζ on ℝ.
```lean
def kM (ξ ζ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * ∫ x in (Real.exp (-t))..1, ξ x * ζ (Real.exp t * x)
def Du (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x
theorem lemma52 {ξ ζ : ℝ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hζ : ContDiff ℝ 1 ζ) (t : ℝ) :
    HasDerivAt (kM ξ ζ) (kM1 ξ ζ t) t ∧ HasDerivAt (kM1 ξ ζ) (kM2 ξ ζ t) t ∧
      -(kM2 ξ ζ t) + kM ξ ζ t / 4
        = kM (Du ξ) (Du ζ) t + Real.exp (-t / 2) * Du ξ (Real.exp (-t)) * ζ 1
          - Real.exp (t / 2) * ξ 1 * Du ζ (Real.exp t)
```
`kM1` and `kM2` are the explicit first and second t-derivatives.
`lemma52_additive` states the same identity for a general Volterra convolution.

**Lemma 5.1.**  There are two forms.
* `lemma51_scaling` is the pointwise core: (−∂_t² + 1/4)(e^{t/2} ξ(e^t x)) = −e^{t/2} (Dξ)(e^t x), with (Dξ)(y) = y²ξ''(y) + 2yξ'(y).
* `lemma51_corr` is the integrated additive form: Q₊(η* ∗ ξ) = η* ∗ (Q₊ ξ).

**The interface.**
```lean
structure ProlateData where
  lam : ℕ → ℝ
  lam_sq_lt_one : ∀ n, lam n ^ 2 < 1
  phi : ℕ → ℝ → ℝ                         -- ξ_n^an
  phi_contDiff : ∀ n, ContDiff ℝ 1 (phi n)
  T : ℝ
  T_pos : 0 < T
  M : ℕ → ℝ
  N : ℕ → ℝ
  bound_inner : ∀ n, ∀ x ∈ Icc (Real.exp (-T)) 1, |phi n x| ≤ M n ∧ |deriv (phi n) x| ≤ M n
  bound_outer : ∀ n, ∀ x ∈ Icc 1 (Real.exp T), |phi n x| ≤ N n ∧ |deriv (phi n) x| ≤ N n
  summable_wMN : Summable fun n => lam n ^ 2 / (1 - lam n ^ 2) * (M n * N n)
```

**Definitions over `D : ProlateData`.**  Here t = log ρ.
* `w n = λ²/(1 − λ²)`.
* `kn n = kM (phi n) (phi n)`.
* `eps t = ∑' n, w n * kn n t`.  This is CC's ε for ρ ≥ 1, in the form used in the proof of Lemma 5.4.
* `eps1` and `eps2` are the termwise first and second derivatives.
* `Qeps t = -eps2 t + eps t / 4`.
* `Cn n t` is CC (99) verbatim.
* `epsMul ρ = eps |log ρ|` is CC's ε on ℝ*₊.
* `Eplus f = ∫ f v * eps |v|` is CC (101).
* `chi v = Qeps |v| / (2 * eps1 0)` is the kernel of K_I.
* `corr η ξ v = ∫ conj (η x) * ξ (x + v)` is CC's η* ∗ ξ (103).

**Prop 5.3, Lemma 5.4, Rem 5.6** (namespace `ArchS8.ProlateData`):
```lean
theorem prop53 {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) :
    HasDerivAt D.eps (D.eps1 t) t ∧ HasDerivAt D.eps1 (D.eps2 t) t ∧
      D.Qeps t = ∑' n, D.w n * D.Cn n t
theorem lemma54 : HasDerivAt D.eps (∑' n, D.w n * D.phi n 1 ^ 2) 0
theorem epsMul_hasDerivWithinAt : HasDerivWithinAt D.epsMul (D.eps1 0) (Ici 1) 1
theorem Qeps_zero : D.Qeps 0 = 0
theorem epsMul_eq {ρ : ℝ} (hρ : 1 ≤ ρ) :
    D.epsMul ρ = ∑' n, D.w n * (Real.sqrt ρ * ∫ x in ρ⁻¹..1, D.phi n x * D.phi n (ρ * x))
theorem cc84_term (n : ℕ) (t : ℝ) :
    D.lam n / Real.sqrt (1 - D.lam n ^ 2)
        * kM (D.phi n) (fun x => D.lam n / Real.sqrt (1 - D.lam n ^ 2) * D.phi n x) t
      = D.w n * D.kn n t
```
* `cc84_term` is the link to CC (84).  CC's ζ_n is λ/√(1 − λ²)·ξ_n^an on [1, ∞) (after their (98)).
  So the n-th term of (84) is w_n·kn_n.
* `eps1_zero_nonneg` gives ε'(1⁺) ≥ 0.
* `eps1_zero_pos` gives ε'(1⁺) > 0 once one term w_n ξ_n(1)² is positive.
* `eps_zero` gives ε(1) = 0.

**CC (102), Remark 3.7 without distributions** (`eq102`).
Take f ∈ C² with f, f', f'' vanishing for |v| ≥ R, where R < T.  Then
E₊(Q₊ f) = −2 ε'(1⁺) f(0) + ∫_0^R (f(v) + f(−v)) (Qε)(v) dv.

**Prop 5.5** (namespace `ArchS8.ProlateData`):
```lean
theorem prop55 {η ξ : ℝ → ℂ} {α ℓ : ℝ} (hℓ : ℓ < D.T) (hη : Continuous η)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hηs : tsupport η ⊆ Icc α (α + ℓ)) (hξs : tsupport ξ ⊆ Icc α (α + ℓ)) :
    D.Eplus (fun v => -(deriv (deriv (corr η ξ)) v) + corr η ξ v / 4)
      = -2 * (D.eps1 0 : ℂ) * (∫ x, conj (η x) * ξ x)
        + ∫ x, ∫ y, conj (η x) * ξ y * (D.Qeps |y - x| : ℂ)
theorem prop55_KI ... (hε : D.eps1 0 ≠ 0) :
    D.Eplus (fun v => -(deriv (deriv (corr η ξ)) v) + corr η ξ v / 4)
      = -2 * (D.eps1 0 : ℂ) * ((∫ x, conj (η x) * ξ x)
          - ∫ x, ∫ y, conj (η x) * ξ y * (D.chi (y - x) : ℂ))
theorem chi_zero : D.chi 0 = 0
```
This is N_I = −2ε'(1⁺)(Id − K_I) as an identity of sesquilinear forms.
η is only required to be continuous, and ξ smooth, both supported in an interval of length ℓ < T.
CC's |I| ≤ log 2 becomes ℓ < T.
`chi_zero` is CC Rem 5.6: the kernel vanishes on the diagonal, "Tr K_I = 0".

**The S2 bridge, the S12-facing form.**
```lean
theorem corr_lift (hh : ContDiff ℝ ⊤ h) (hs : tsupport h ⊆ Icc α (α + ℓ)) (v : ℝ) :
    corr (fun u => deriv h u - h u / 2) (fun u => deriv h u - h u / 2) v
      = -corr h (deriv (deriv h)) v + corr h h v / 4
theorem corr_self_eq_autocorr (h : ℝ → ℂ) : corr h h = WeilExplicit.autocorr h
theorem prop55_lift {h : ℝ → ℂ} (hh : WeilExplicit.IsWeilTest h) {α ℓ : ℝ} (hℓ : ℓ < D.T)
    (hs : tsupport h ⊆ Icc α (α + ℓ)) :
    D.Eplus (WeilExplicit.autocorr fun u => deriv h u - h u / 2)
      = -2 * (D.eps1 0 : ℂ) * (∫ x, conj (h x) * h x)
        + ∫ x, ∫ y, conj (h x) * h y * (D.Qeps |y - x| : ℂ)
```
S2 proved that the pole-free g are exactly the g = h' − h/2 (`ArchS2.poleFree_iff_exists_lift`).
So `prop55_lift` is CC's "E∘Q(ξ∗ξ*) = ⟨ξ|N_I ξ⟩" composed with Prop 3.5, in the island's own `autocorr`.

## What S6 and S9 must supply

To instantiate `ProlateData` for c = 2π, even prolates:

1. **`lam n`** is the n-th eigenvalue of P₁F P₁ on even L² (CC (68)-(69)), with λ² < 1.
   S9 certifies λ_n for n ≤ 12.  S6 must give |λ_n| < 1 for all n.
2. **`phi n`** must be ξ_n^an.
   * It equals the normalised eigenfunction ξ_n on [0, 1], with ∫_0^1 ξ_n² = 1 in CC's normalisation (16).
   * On [1, ∞) it equals λ_n⁻¹ (F ξ_n)(x) = λ_n⁻¹ · 2∫_0^1 ξ_n(y) cos(2πxy) dy.
   * Recommended definition: `phi n x := λ_n⁻¹ · 2∫_0^1 ξ_n(y) cos(2πxy) dy` for all x.
     This is smooth on ℝ, which gives `phi_contDiff` by differentiation under the integral.
     It equals ξ_n on [0, 1] by the eigen-relation (69).
   * S8 never uses orthonormality or the eigen-relation itself.
     They matter only for S7's identification of `eps` with the ε of Thm 4.7.
3. **`T`.**  For CC's window |I| = log 2, any T > log 2 works.  T = log 3 is comfortable.
   * The numerical values of χ on [0, log 2] use ξ_n and ξ_n' only on [1/2, 2].
     That is exactly S9's range.
   * The range beyond 2 enters only through the structural bounds N_n.
4. **`N n`**, the outer bound on [1, e^T].  Take N_n = 4π/|λ_n| for λ_n ≠ 0.
   * |η_n| ≤ 2∫_0^1 |ξ_n| ≤ 2 and |η_n'| ≤ 4π∫_0^1 x|ξ_n| ≤ 4π hold for every x, so this bound is uniform in T.
   * When λ_n = 0 the weight w_n vanishes, and any finite N_n works.
5. **`M n`**, the inner bound on [e^{−T}, 1] for |ξ_n| and |ξ_n'|.  **This is the one substantive analytic obligation.**
   * With N_n = 4π/|λ_n|, `summable_wMN` reduces to Σ |λ_n| M_n / (1 − λ_n²) < ∞.
   * The eigen-relation alone gives only M_n ≤ 4π/|λ_n|, which is NOT enough: the sum becomes Σ 16π²/(1 − λ²).
   * So S6 must prove a sup bound on ξ_n and ξ_n' over [e^{−T}, 1], uniformly up to x = 1, that beats 1/|λ_n|.
   * Polynomial growth in n is plenty.  CC use |ξ_n(1)| ≤ √(2n + 1/2) (100) and Wang's bounds (166).
   * One route is the prolate ODE: ∫(1 − x²)ξ'² + 4π²∫x²ξ² = χ_n ≤ 2n(2n + 1) + 4π², plus a bound on ∫ξ''²(1 − x²)².
   * Another route is the Legendre expansion with coefficient decay.
6. **The tail of λ, the blueprint's bypass B3.**  Σ_{k≥n} σ_k² ≤ 4(2π)^{2n}/(n!)² gives σ_n ≤ 2(2π)^n/n!.
   * The n-th even eigenvalue is the (2n)-th singular value overall, so it is at most σ_n.
   * With polynomial M_n, this gives Σ |λ_n| M_n < ∞, hence `summable_wMN`.
   * So the concrete bound S6 must supply is: B3 for λ, plus a polynomial (or any o(1/|λ_n|)-compatible) bound M_n.

**S7 obligation.**
* S7 must show that CC's ε in Thm 4.7, Tr(ϑ(f)S) = W∞(f) + ∫ f(ρ⁻¹)ε(ρ)d*ρ, equals `D.epsMul` for the S6 data.
* By `cc84_term` and `epsMul_eq`, it suffices to prove (84) termwise with ζ_n = λ/√(1 − λ²)·ξ_n^an on [1, ∞).
  That is CC's remark after (98).
* Then E in Thm 4.7 is `Eplus` composed with x = log ρ.
* S12 then reads W∞(g∗g*) ≥ −E(g∗g*) = −⟨h | N_I h⟩ through `prop55_lift`.

## Open items

* **K_I as an operator is not built.**  CC Prop 5.5(i) says N_I is bounded and K_I is Hilbert-Schmidt on L²(I).
  * Here only the sesquilinear-form identity on continuous η and smooth ξ is proved.
  * The kernel χ(y − x) is continuous on I × I (see `continuous_Qeps_clamp`), so the HS property is immediate once S5's integral-operator API exists.
  * Extension of the form identity to all of L²(I) needs S5 (density plus boundedness).
* **Lemma 5.1 in CC's multiplicative pairing form is not stated.**  That form is ⟨η | ϑ(Qf)ξ⟩ = −⟨η | ϑ(f)Dξ⟩ for f ∈ C_c^∞(ℝ*₊).
  * Given instead: the pointwise core (`lemma51_scaling`) and the additive integrated form (`lemma51_corr`).
  * Also given: the boundary-term version Lemma 5.2, which is the one CC actually use.
  * CC themselves use (95) only "at the formal level".
* **Numerical values are not touched.**  ε'(1⁺) ≈ 22.9965, the range of χ, and Fig. 10 belong to S9 and S10.
  * Structurally, ε'(1⁺) ≥ 0 is proved, and ε'(1⁺) > 0 once one term is positive.
  * `prop55_KI` needs ε'(1⁺) ≠ 0, which follows from `eps1_zero_pos` with n = 0 once S9 certifies λ_0 and ξ_0(1) ≠ 0.
* **Real ξ_n, complex test functions.**  `phi` is real-valued, as CC's ξ_n are.
  The test functions η, ξ, h are complex, and the kernel is coerced.
* **The convergence of (98) itself is not stated.**  CC's Lemma F.1 is the remainder bound after N terms.
  * The Lean series converges uniformly with derivatives on (−T, T) under `summable_wMN`.
  * An explicit remainder Σ_{n>N} w_n·B_n with B_n = (2 + T)·2M_n·e^{T/2}(1 + e^T)N_n is available from `abs_kn_le`, but not packaged.
  * S10 will want that packaged.
* **Wiring was left to the coordinator.**  `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched.
  The four `[[lean_lib]]` stanzas (`ArchS8_Volterra`, `ArchS8_ProlateData`, `ArchS8_Kernel`, `ArchS8_Guard`) are at the end of `lakefile.toml`.

## Lean footguns met

* **Namespace of the parametric primitive.**  `continuous_parametric_primitive_of_continuous` is `intervalIntegral.continuous_parametric_primitive_of_continuous`.
* **The `Ι` notation.**  `Ι a b` (uIoc) needs `open scoped Interval`.
* **No parametric-primitive derivative lemma.**  There is none at this pin.
  The Volterra rule is proved by hand: a fixed-limit dominated derivative, plus FTC, plus an O(h²) cross term via `isLittleO_pow_sub_sub`.
* **`rw [← integral_add h₁.neg h₂]` with explicit integrability arguments fails.**  The argument fixes the function as `(-fun s => …)`, which does not match `fun s => -(…)`.
  Rewrite forward with no arguments, then close the side goals with `exact h₁.neg`.
* **Composition atoms before `ring`.**  `HasDerivAt.comp`, `.add` and `.mul` leave `(ξ ∘ g) x`, `Pi.add_apply` and `Pi.mul_apply` atoms.
  Run `simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]` before `ring` in `congr_deriv`.
* **`simpa using hf.scomp x (hasDerivAt_neg x)` fails on ℂ-valued f.**  Simp makes the function `f ∘ Neg.neg`, and the instance paths then differ (`addCommGroup` vs `instNormedAddCommGroup.toAddCommGroup`).
  Use `(hf (-x)).scomp x (hasDerivAt_neg x) |>.congr_deriv (by simp)` instead.
* **Beta-redexes after `integral_congr_ae`.**  `integral_congr_ae (Eventually.of_forall fun x => ?_)` leaves `(fun x => …) x` redexes.
  Use `try dsimp only`.  After `unfold Eplus`, `show` the beta-reduced integral before rewriting with a lemma whose function argument is given explicitly (`(g := …)`).
* **Hypothesis forms differ.**  `ContDiff.differentiable` takes `n ≠ 0` at this pin, while `ContDiff.continuous_deriv` takes `1 ≤ n`.
* **Smoothness of derivatives.**  For smooth test functions, `contDiff_infty_iff_deriv` iterated three times gives all the derivatives needed.
  `HasCompactSupport.deriv` and `tsupport_deriv_subset` give their supports.
* **`HasCompactSupport.intro` needs `[R1Space]`.**  It is the additive form of `HasCompactMulSupport.intro`, and ℝ × ℝ is an R1 space.
* **Replayed warnings.**  `lake build ArchS8_Kernel` replays upstream warnings: Zeta23 deprecations and a `ring` "Try this" from an E6Bridge module.
  None come from S8.  Grep the output for `ArchS8`.
