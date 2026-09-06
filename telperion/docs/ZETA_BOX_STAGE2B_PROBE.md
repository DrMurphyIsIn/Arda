# Stage 2B feasibility probe: local Blaschke split of Λ over a strip box

**Task 1 of the RH-in-a-box program (zeta box localization, Stage 2/3).**
**Verdict: GO.** `conjecture1_proved = False` (this probe is NOT a proof of RH).

Date: 2026-09-06. Worktree: `telperion-zeroloc`, branch `rh/zeta-box-localization`.
Lean/Mathlib: `leanprover/lean4:v4.32.0`, `mathlib` rev `v4.32.0`.

---

## 1. The question

Stage 2B needs the LOCAL Blaschke / principal-part split of `Λ = completedRiemannZeta`
over the capstone box `B = [2/5, 3/5] × [10, 35]`:

```
Λ'/Λ z  =  Σ_{ρ ∈ B} (divisor Λ ρ) / (z − ρ)  +  E z ,      E holomorphic on cl(B).
```

`B` has rational corners with `0 < 2/5 < 1/2 < 3/5 < 1` and `T0 = 10 > 0`. Because `T0 > 0`
and `σ1 = 3/5 < 1`, the box (and a small open neighborhood of `cl(B)`) EXCLUDES Λ's poles
`s = 0`, `s = 1` and all trivial zeros. Hence on that neighborhood Λ is holomorphic and its
only zeros are the nontrivial ones — so the split is a genuinely LOCAL statement: subtract the
finitely many simple-pole principal parts of `logDeriv Λ` at the zeros in `B`, and the remainder
`E` is holomorphic on `cl(B)`.

GO means: the E-holomorphicity path is concrete and bounded in Mathlib, with a named lemma chain.
NO-GO means: it needs unbuilt Mathlib machinery, and the fallback is to carry the split +
E-holomorphicity as documented non-kernel hypotheses (same trust boundary as the enclosures).

---

## 2. What I read

### 2.1 In-repo disk split (`telperion/examples/zero_free_bridge/lean/`)

- `DlvpBlaschkeSplitExpand.lean` — `logDeriv_eq_herglotz_add_entire`: for a `CanonicalDecomp f g R`
  with `f, g` analytic on `ball 0 R` and `g` zero-free, at `z ∈ ball 0 R` off the zeros,
  ```
  logDeriv f z = Σ_u (divisor f (ball 0 R) u)/(z−u)
                 + [ Σ_u (divisor f u)·conj u /(R² − conj u · z)  +  logDeriv g z ].
  ```
  This is the DISK version, center 0. Its "entire part" `E` carries TWO pieces: the bounded
  Blaschke correction `Σ conj-u/(R² − conj u · z)` (pole at `R²/conj u`, OUTSIDE the disk) and
  `logDeriv g`.
- `DlvpBlaschkeSplit.lean` — `logDeriv_split_off_zeros`: the underlying split
  `logDeriv f = Σ_u (−divisor u)·logDeriv (canonicalFactor R u) + logDeriv g`, proved by cutting to
  a small convex ball avoiding the zeros and using the function-agnostic transfer
  `DlvpTransfer.logDeriv_congr_of_codiscrete`, `logDeriv_mul`, and
  `DlvpBlaschkeHerglotz.logDeriv_finprod_canonicalFactor`.
- `DlvpCanonicalLogDeriv.lean` — `logDeriv_canonicalFactor`: the Blaschke factor
  `canonicalFactor R w z = (R² − conj w · z)/(R(z−w))` has
  `logDeriv (canonicalFactor R w) z = −conj w/(R² − conj w · z) − 1/(z−w)`.
- `CanonicalDecomp` / `canonicalFactor` come from Mathlib `Analysis/Complex/CanonicalDecomposition`.

Key observation: the in-repo path uses the BLASCHKE factor because it needs the `‖·‖ = 1`-on-sphere
/ Herglotz positivity structure for the dVP zero-free-region work. **The box localization does NOT
need positivity** — it only needs `E` holomorphic on `cl(B)`. So the plain factorization
`(z − u)^d` (no Blaschke correction term) is both sufficient and strictly simpler.

### 2.2 Mathlib divisor / factorization API (`.lake/.../Mathlib/Analysis/Meromorphic/`)

The decisive result is **`MeromorphicOn.extract_zeros_poles`** in
`Mathlib/Analysis/Meromorphic/FactorizedRational.lean`:

```lean
theorem MeromorphicOn.extract_zeros_poles {f : 𝕜 → E} (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) (h₃f : (divisor f U).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· − u) ^ divisor f U u) • g
```

This is EXACTLY the split, with the plain factorized-rational product `∏ᶠ u, (· − u)^(divisor f U u)`
and an analytic, zero-free remainder `g` on the OPEN set `U`. The in-repo `DlvpBlaschkeSplit` is
built on the Blaschke analogue of precisely this; here we use the raw Mathlib version directly.

Supporting Mathlib lemmas confirmed present in v4.32.0:

| Lemma | File | Gives |
|---|---|---|
| `MeromorphicOn.extract_zeros_poles` | `Meromorphic/FactorizedRational.lean:291` | the codiscrete factorization `f =ᶠ (∏ᶠ (·−u)^d) • g`, g analytic + zero-free |
| `Function.FactorizedRational.divisor` | `Meromorphic/FactorizedRational.lean:176` | `divisor (∏ᶠ (·−u)^D) U = D` (the exponents ARE the divisor) |
| `divisor_support_finite_of_subset` | `Meromorphic/Divisor.lean:91` | `MeromorphicOn f U`, `IsCompact U`, `V ⊆ U` ⇒ `(divisor f V).support.Finite` |
| `divisor_ball_support_finite` | `Meromorphic/Divisor.lean:106` | special case on a ball (template for the box) |
| `differentiableAt_completedZeta` | `NumberTheory/LSeries/RiemannZeta.lean:95` | Λ differentiable (hence analytic) away from `s = 0, 1` |
| `logDeriv_prod` | `Analysis/Calculus/LogDeriv.lean:73` | `logDeriv (∏ i∈s, f i ·) x = ∑ i∈s, logDeriv (f i) x` |
| `logDeriv_fun_zpow` | `Analysis/Calculus/LogDeriv.lean:87` | `logDeriv (h ·^n) x = n · logDeriv h x` |
| `deriv_sub_const` | `Analysis/Calculus/Deriv/Add.lean:414` | `deriv (·−u) z = deriv (·) z = 1` |
| `logDeriv_congr_of_codiscrete` (in-repo) | `DlvpTransfer.lean:58` | transfers `logDeriv` across a codiscrete equality on preconnected open `U` (function-agnostic) |
| `finprod_eq_prod_of_mulSupport_subset` | Mathlib `Algebra/BigOperators/Finprod` | collapses `∏ᶠ` to a `Finset` product under finite support |

No missing/unbuilt Mathlib machinery was found anywhere on the chain.

---

## 3. The toy reduction (machine-checked, no sorry)

`telperion/examples/zeta_zero_localization/lean/BlaschkeBoxProbe.lean` (THROWAWAY, NOT CI-wired —
not in `defaultTargets`, not a `lean_lib`, imported by nothing) proves, using ONLY the Mathlib
lemmas above:

```lean
theorem toy_blaschke_split {s : Finset ℂ} (d : ℂ → ℤ)
    (z : ℂ) (hz : ∀ u ∈ s, z − u ≠ 0) :
    logDeriv (fun w : ℂ => ∏ u ∈ s, (w − u) ^ (d u)) z
      = (∑ u ∈ s, (d u : ℂ) / (z − u)) + (0 : ℂ)
```

i.e. `logDeriv (factorized rational) z = Σ_ρ (d ρ)/(z − ρ) + logDeriv g z` with `g = 1`
(`logDeriv g = 0`), at any box point `z` avoiding the roots. Built via `logDeriv_prod` +
`logDeriv_fun_zpow` + `deriv_sub_const`. The `Finset` product here is precisely the form Mathlib's
`∏ᶠ u, (· − u)^(divisor Λ U u)` collapses to once the divisor support is finite
(`finprod_eq_prod_of_mulSupport_subset`).

**It compiles clean under `lake env lean BlaschkeBoxProbe.lean`: zero errors, zero warnings, zero
sorries.** (Cache warmed with `lake exe cache get` first; no cold Mathlib compile.) The genuine
mathematical content Task 7 needs — the principal-part sum and the identification of `E = logDeriv g`
as holomorphic — is therefore machine-verified in miniature, not merely sketched.

---

## 4. GO verdict and the exact Task-7 lemma chain

**GO.** The E-holomorphicity path is concrete and bounded; `E := logDeriv g` where `g` is the
analytic, zero-free remainder from `MeromorphicOn.extract_zeros_poles`, so `E = deriv g / g` is
holomorphic on the open `U ⊇ cl(B)` (`g` analytic, `g ≠ 0`). No unbuilt machinery.

Task-7 chain (each step has its named lemma above):

1. **Region.** Choose an OPEN neighborhood `U` of `cl(B)` avoiding `{0, 1}` (possible since
   `T0 = 10 > 0`, `σ1 = 3/5 < 1`; e.g. an open rectangle slightly larger than `B`, or an open ball
   containing `cl(B)` but not `0, 1`). On `U`, `differentiableAt_completedZeta` ⇒
   `AnalyticOnNhd ℂ Λ U` ⇒ `MeromorphicOn Λ U`. Preconnected + open `U` (take a rectangle/ball —
   convex ⇒ preconnected) for the transfer step.
2. **Finite divisor support.** `divisor_support_finite_of_subset` with `U₀ := cl(B)` (or a closed
   ball ⊇ `cl(B)` still avoiding `0,1`), `IsCompact U₀`, `U ⊆ U₀`: `(divisor Λ U).support.Finite`.
   (Λ is not locally-constant zero, so `meromorphicOrderAt Λ u ≠ ⊤`.)
3. **Split.** `MeromorphicOn.extract_zeros_poles` ⇒
   `∃ g, AnalyticOnNhd ℂ g U ∧ (∀ u:U, g u ≠ 0) ∧ Λ =ᶠ[codiscreteWithin U] (∏ᶠ u,(·−u)^(divisor Λ U u)) • g`.
4. **Finprod → Finset.** `finprod_eq_prod_of_mulSupport_subset` (finite support from step 2) turns
   `∏ᶠ` into `∏ u ∈ (support).toFinset` — the exact hypothesis shape of `toy_blaschke_split`.
5. **Log-derivative transfer.** `logDeriv_congr_of_codiscrete` (in-repo `DlvpTransfer`,
   function-agnostic) moves `logDeriv Λ` to `logDeriv ((∏ …) • g)` across the codiscrete equality on
   preconnected open `U`.
6. **Split the log-derivative.** `logDeriv_mul` + the `logDeriv_prod`/`logDeriv_fun_zpow` expansion
   of the finite product (Step-3 pattern, i.e. `toy_blaschke_split`) ⇒
   ```
   logDeriv Λ z = Σ_{ρ ∈ B} (divisor Λ U ρ)/(z − ρ) + logDeriv g z .
   ```
7. **E holomorphic on cl(B).** `E := logDeriv g`; `g` is `AnalyticOnNhd ℂ g U` and zero-free on `U`,
   so `logDeriv g = deriv g / g` is analytic on `U ⊇ cl(B)` (quotient of analytic by non-vanishing
   analytic; `AnalyticAt.logDeriv`-style, or directly `(hg z).div` with `g z ≠ 0`).

### Recentering note (`logDeriv_shift_center` gap named at Stage 1)

The Stage-1 probe worried the in-repo split is anchored at `ball 0 R`, center 0, and would need a
`logDeriv_shift_center` to move to a region containing `B`. **That gap is dissolved, not bridged:**
we do NOT recenter the disk split. We go straight to Mathlib's `MeromorphicOn.extract_zeros_poles`,
which is stated for an ARBITRARY set `U` — pick `U` to be a box/ball neighborhood of `cl(B)` from
the start. No center-0 assumption, no shift lemma needed. (If a future step wants the Blaschke/
Herglotz positivity of the in-repo path over the box, THEN a recentering would be required; the box
localization does not.)

### Effort estimate

Small-to-moderate, ~1–2 focused sessions. The load-bearing Mathlib lemma
(`extract_zeros_poles`) already returns the full factorization; the remaining work is bookkeeping:
picking `U`, discharging the three hypotheses (`MeromorphicOn`, `order ≠ ⊤`, finite support),
`finprod_eq_prod`, wiring the in-repo `logDeriv_congr_of_codiscrete`, and the
`logDeriv_prod`/`logDeriv_fun_zpow` expansion already proved in `toy_blaschke_split`. No new theory.
Main friction points are the usual Mathlib coercion/`∏ᶠ` plumbing (already exercised in the toy
file) and confirming `meromorphicOrderAt Λ u ≠ ⊤` on `U` (Λ is analytic and not identically zero
on `U`, so orders are finite non-negative).

---

## 5. NO-GO fallback (not needed, recorded for completeness)

Were the chain to hit an unbuilt-Mathlib wall, the fallback is to carry the two facts as documented
NON-KERNEL hypotheses at the same trust boundary as the numeric enclosures:

- `hSplit : ∀ z ∈ U \ zeros, logDeriv Λ z = Σ_{ρ ∈ B} (divisor Λ U ρ)/(z − ρ) + E z`
- `hE_holo : AnalyticOnNhd ℂ E U` (E holomorphic on `U ⊇ cl(B)`)

fed into the argument-principle total-count certificate as assumptions. This probe finds the
fallback unnecessary: the derivation is available in-kernel via the chain in §4.

---

## 6. Bottom line

**GO.** Stage 2B is buildable in Lean/Mathlib v4.32.0 with no unbuilt machinery. Anchor result:
`MeromorphicOn.extract_zeros_poles`. The E-holomorphicity is `logDeriv` of the analytic zero-free
remainder, strictly simpler than the in-repo disk Blaschke split (which additionally carries a
bounded correction term needed only for disk Herglotz positivity, which the box localization does
not require). The core log-derivative expansion is machine-checked sorry-free in the throwaway
`BlaschkeBoxProbe.lean`. `conjecture1_proved = False`.
