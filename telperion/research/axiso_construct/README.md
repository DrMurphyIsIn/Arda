# Class P, constructor seat: the buildable core

`conjecture1_proved = False`. Nothing in this directory, or in the Lean file it accompanies,
says anything about where the zeros of the Riemann zeta function lie.

## What this is, in one paragraph

The constructor seat set out to build a member of "class P" with a zero off the critical line.
Class P asks for three things. (P1) is a zeta-shaped functional equation with an `s(s-1)` pole
normalization. (P2) says the von Mangoldt function `Λ_F` of the Dirichlet series is
nonnegative. The third is the usual analytic hygiene. The seat found that every route to a
counterexample is blocked. It also found two sharp near-misses, and each one shows which
hypothesis is doing the blocking:

- `F0 = ζ(s)(1+2^{-s})(1+2^{1-s})` breaks only P2.
- `F1 = ζ(s/2+3/4)ζ(s/2-1/4)` breaks only the pole normalization in P1.

This build takes the parts of that report that can be settled exactly, today, and settles
them in the Lean kernel. The heavier theorems (Theorem A, Theorem B, general Lemma C, Prop D)
still rest on paper. They are listed below with their status unchanged.

## Where things live

| File | What it is |
|---|---|
| `telperion/examples/rvm_bridge/lean/Crux/Crux_axiso_construct.lean` | The Lean file: 1776 lines and 73 headline theorems. `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for every one. It has no `sorry`, no `admit`, no `native_decide`, no `opaque`, and no new `axiom`. |
| `telperion/research/axiso_construct/axiso_construct_numerics.py` | The numerical companion. It runs 26 checks, each marked PASS or FAIL, and exits nonzero if any fails. |
| `telperion/research/axiso_construct/outputs/numerics.json` | Machine-readable results. |
| `telperion/research/axiso_construct/outputs/numerics_summary.txt` | The same results as text. |
| `telperion/research/axiso_construct/outputs/lean_print_axioms.txt` | The transcript of the kernel check: 73 `#print axioms` lines, exit 0. |

**Why the rvm_bridge island.** That island pins Anthropic's Zeta23 formalization (Lean
v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb). Zeta23 proves the Riemann–von Mangoldt formula
with no hypotheses. From it, `exists_nontrivial_zero_above` derives, in about 20 lines, that ζ
has nontrivial zeros of arbitrarily large height. That single input is what makes
"`F1` has infinitely many zeros off the line" an unconditional kernel theorem rather than a
floating-point observation. Zeta23 is used nowhere else in the file. The lemmas consumed are
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts`, `Zeta23.Assembly.eventually_N_ge`, and
`Zeta23.Assembly.tendsto_Tl_atTop`.

## How to check it yourself

```sh
cd telperion/examples/rvm_bridge/lean
lake env lean Crux/Crux_axiso_construct.lean        # ~50 s once the island's .lake is built
# (on the shared build machine, wrap it in the lean-slot lock: leanlock.sh lake env lean ...)

cd ../../../research/axiso_construct
/usr/bin/python3 axiso_construct_numerics.py         # ~4 s; needs mpmath, sympy, python-flint
```

The Lean check prints 73 lines of the form `'CruxAxisoConstruct.X' depends on axioms: [propext,
Classical.choice, Quot.sound]` and nothing else: no errors and no warnings.

## Status ledger: what moved and what did not

The tags follow the program's convention: THEOREM-kernel-checked, THEOREM-paper-proof,
CONJECTURE-with-evidence, HEURISTIC.

| Claim in the constructor report | Tag in the report | Tag after this build | Lean name(s) |
|---|---|---|---|
| Positivity lemma: P2 forces `a_n ≥ 0` | paper | **kernel-checked** | `positivity_lemma`, `coeff_nonneg_of_logDeriv_nonneg` |
| Positivity lemma: the Landau half (a pole at 1, no zeros for `σ > 1`, `F` not entire) | paper | paper (unchanged) | none |
| Theorem A, Step 3: Cohn–Elkies support forcing, and exclusion of `ε = -1` | paper | **kernel-checked, conditional on the Step-2 pairing identity** | `ce_support_forcing`, `thmA_step3_plus`, `thmA_step3_minus` |
| Theorem A: pointwise facts about `f` and `f̂` | paper | **kernel-checked** | `ceF_nonpos`, `ceF_eq_zero_iff`, `ceFhat_nonneg`, `ceFhat_eq_zero_of_one_le`, `ceF_zero`, `ceFhat_zero` |
| Theorem A: the Fourier identity `𝓕 f = f̂` | paper (sympy) | computed (sympy symbolic + 50-digit quadrature, check N6); not in Lean | none |
| Theorem A: Step 2 (FE ⟹ distributional Poisson identity) and Step 4 (Hamburger) | paper | paper (unchanged) | none |
| Conductor bound `q ≥ 1` | paper | paper (unchanged; it rests on Theorem A) | none |
| Theorem B | paper (cites Kaczorowski–Perelli, Saias–Weingartner) | paper (unchanged) | none |
| Lemma C at prime conductor `q = p` | paper | **kernel-checked** | `Pc_selfRecip_sq`, `Pc_sqrt_selfRecip`, `lemmaC_prime`, `Fc_logDeriv_exists` |
| Lemma C at conductor `q = p²`, every prime `p` | paper | **kernel-checked** | `Pq_selfRecip_cases`, `sq_family_core`, `Fq_plus_values`, `lemmaC_prime_sq` |
| Lemma C in general | paper | paper, plus new evidence for `q = 6, 10, 14, 15` (check N7) | none |
| Prop D | paper | paper (unchanged) | none |
| Near-miss 1 (`F0`) | paper, float-certified | **kernel-checked** (except "order 1"; see caveats) | Section B of the Lean file |
| Near-miss 2 (`F1`) | paper, float-certified | **kernel-checked**, including unconditional existence of infinitely many off-line zeros | Section D |
| E8-normalized twin | paper, float-certified | **kernel-checked** for the zeta-product form; the E8 identification is not formalized | Section E |
| Rescaling a degree-`d` object puts the pole at `(d+1)/2` | paper | **kernel-checked** (the algebra) | `rescale_pole`, `rescale_reflect` |
| Moving zeros, signed Beurling measures, DMV systems | paper | paper (unchanged; they rest on Theorem A) | none |
| Twisted Beurling conjecture | CONJECTURE-with-evidence | unchanged | none |

## A tour of the Lean file

### A. What "P2" means in the kernel

The first design decision was how to state P2 so that a hostile referee cannot wriggle out of
it. The definition is

```lean
def IsLogDerivCoeff (F : ℂ → ℂ) (g : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv g < ⊤ ∧ ∀ᶠ x : ℝ in atTop, -deriv F x / F x = LSeries g x
```

P2 for `F` is then `∃ g, IsLogDerivCoeff F g ∧ ∀ n, 0 ≤ g n`, where `0 ≤ z` on `ℂ` means "real
and nonnegative" (Mathlib's `ComplexOrder`). The hypothesis only asks for agreement along a real
ray, so the uniqueness theorems below are as strong as possible: any Dirichlet series that matches
`-F'/F` far out on the real axis has the forced coefficients.

The workhorse is `logMul_eq_convolution`. If `F = L a` with `a 1 = 1`, then
`log n · a(n) = Σ_{d | n} g(d) a(n/d)` for every `n ≥ 1`. The proof takes the derivative
of the L-series, applies the L-series convolution theorem, and then uses Mathlib's L-series
injectivity. This makes `g` unique, and small divisor sums pin its values:

- `logDerivCoeff_prime`: `Λ_F(p) = a(p) log p`.
- `logDerivCoeff_prime_sq`: `Λ_F(p²) = log p · (2a(p²) − a(p)²)`.
- `P2_forces_sq_ineq`: P2 implies `a(p)² ≤ 2a(p²)` at every prime. This is a clean necessary
  condition that anyone can check against a candidate in one line.
- `positivity_lemma`: P2 implies every `a(n) ≥ 0`, by strong induction on `n` through the same
  recursion. This is the arithmetic half of the report's positivity lemma.
- `zeta_P2`: the positive control. `ζ` itself satisfies the definition, with `g = Λ ≥ 0`, so the
  predicate is not vacuous.

### B. Near-miss 1: `F0 = ζ(s)(1+2^{-s})(1+2^{1-s})`

Everything the report says about `F0` is now a kernel theorem, with the exceptions listed under
the caveats:

- **Functional equation.** `P0(s) = 1 + 3·2^{-s} + 2·4^{-s}` is self-reciprocal with conductor 4:
  `P0(s) = 4^{1/2-s} P0(1-s)` (`P0_reciprocal_four`). The completion
  `Xi0(s) = 2^s P0(s) · xiC(s)` is **entire** (`Xi0_entire`) and **symmetric**,
  `Xi0(1-s) = Xi0(s)` (`Xi0_one_sub`). Here `xiC(u) = u(u-1)Λ₀(u) + 1` is the entire completion
  of zeta built from Mathlib's `completedRiemannZeta₀`. Away from `0`, `1`, and the poles of
  `Γ(s/2)`, `Xi0(s) = s(s-1) 2^s Γ_ℝ(s) F0(s)` (`Xi0_eq`), which is the twisted P1 shape
  `s(s-1)(2/√π)^s Γ(s/2) F0(s)`.
- **Coefficients.** `F0 = L a0` on `Re s > 1` (`F0_eq_LSeries`), with `a0(n) = 1 + 3[2|n] + 2[4|n]`
  taking only the values 1, 4, 6 (`a0_cases`). The coefficients are multiplicative
  (`a0_mul_coprime`), so `F0` has an Euler product.
- **Zeros.** The zero set of `P0` is exactly `{i t_k} ∪ {1 + i t_k}` with `t_k = (2k+1)π/log 2`,
  `k ∈ ℤ` (`P0_eq_zero_iff`). So the entire, FE-symmetric `Xi0` vanishes at points with real
  part exactly 1 (`Xi0_zero_offline`). These are zeros off the critical line of an object with
  the exact functional equation.
- **P2 fails, and exactly where the report says.** The von Mangoldt series exists
  (`F0_logDeriv_exists`, with explicit witness `Λ + geomCoeff 2 1 + geomCoeff 2 2`). It has the
  closed form `Λ_{F0}(2^m) = log 2 · (1 − (−1)^m − (−2)^m)` (`F0_vonMangoldt_two_pow`), and every
  representation has `Λ_{F0}(4) = −4 log 2` (`F0_logDerivCoeff_four`). Hence `F0_not_P2`. Check N1
  confirms in exact rational arithmetic that `n = 4, 16, 64, 256, 1024, 4096` are the only
  `n ≤ 4096` with `Λ_{F0}(n) < 0`.

### C. Lemma C at prime conductor

Take `P(s) = 1 + c p^{-s}` with `c` real and `p` prime (P2 forces real coefficients anyway,
through `positivity_lemma`), and suppose `P(s) = E · p^{1/2-s} P(1-s)` for some constant `E`.
Then `c² = p` (`Pc_selfRecip_sq`). The proof uses the identity only at `s = 0` and `s = 2`;
eliminating `E` leaves `(p² − 1)(p − c²) = 0`. The family is nonempty: `c = √p`, `E = 1` works
(`Pc_sqrt_selfRecip`). Its von Mangoldt series exists (`Fc_logDeriv_exists`), and
`Λ_F(p²) = (1 − p) log p < 0`. So P2 fails for every member (`lemmaC_prime`). Check N2 re-derives
this in Arb ball arithmetic for every prime below 100 and both signs, by two independent routes.

The same holds at conductor `p²`, for every prime at once. A real self-reciprocal
`1 + x p^{-s} + y p^{-2s}` of conductor `p²` has exactly two branches (`Pq_selfRecip_cases`,
using the identity at `s = 0, 1, 2` and a Vandermonde elimination):

- **`y = p`, any `x`.** Here the prime-power recursion gives `Λ_F(p^k) = log p · (1 − s_k)` for
  `k ≤ 5` (`Fq_plus_values`), where the `s_k` are the Newton power sums of the inverse roots.
  `sq_family_core` is a real-polynomial fact, proved by case analysis and `nlinarith`: for every
  real `x` and every `p ≥ 2`, some `1 − s_k` with `k ≤ 5` is negative. Five is sharp at `p = 2`,
  where `x = −1` survives `k ≤ 4`.
- **`x = 0`, `y = −p`.** Here `a(p)² = 1 > 2a(p²) = 2(1 − p)`, so `P2_forces_sq_ineq` is
  violated.

Both branches are genuinely self-reciprocal (`Pq_plus_selfRecip`, `Pq_minus_selfRecip`), and
`lemmaC_prime_sq` packages the result. Check N2b cross-checks the recursion against Newton's
identities up to `k = 8` in exact arithmetic, and evaluates `sq_family_core` on 21,015 exact grid
points; the largest value of `min_k (1 − s_k)` there is `−3/5`. Unlike Section C, existence of
`Λ_F` for this family is not re-proved in Lean. The P2 statement is `¬ ∃ g ≥ 0`, which does not
need it.

### D and E. Near-miss 2 and its E8 twin

Both are cases of one family, `XiPair a s = xiC(s/2 + a) · xiC(s/2 + 1/2 − a)`. Every member is
entire (`XiPair_entire`) and symmetric under `s ↦ 1 − s` (`XiPair_one_sub`). The zeros of
`xiC` lie in the open strip `0 < Re u < 1` (`xiC_zero_strip`, from Mathlib's nonvanishing on
`Re u ≥ 1` and the reflection). So for `a ≥ 3/4` there is **no zero at all on `Re s = 1/2`**
(`XiPair_no_zero_on_line`). And, unconditionally via Zeta23, there are zeros of arbitrarily
large height with `2a − 1 < Re s < 2a + 1` (`XiPair_offline_zeros`).

- `F1` is the case `a = 3/4`. The completion `Xi1` equals `F1` times one gamma factor
  `Γ_ℂ(s/2 − 1/4) = 2(2π)^{1/4 − s/2} Γ(s/2 − 1/4)` times the polynomial
  `(s/2+3/4)(s/2−1/4)²(s/2−5/4)`, in place of class P's `s(s−1)` (`Xi1_eq`). Every zero has real
  part in `(−3/2, 1/2) ∪ (1/2, 5/2)` (`Xi1_zero_re`), and there are infinitely many with
  `1/2 < Re s < 5/2` (`Xi1_offline_zeros`).
- **P2 holds for `F1` in Beurling form.** For `Re s > 5/2`,
  `−F1'/F1 = Σ_n b1(n) (√n)^{−s}` with `b1(n) = (Λ(n)/2)(n^{−3/4} + n^{1/4}) ≥ 0`
  (`F1_logDeriv_hasSum`, `b1_nonneg`). The frequencies are `log √n`, so this is a generalized
  Dirichlet series over the Beurling integers `√n`.
- **The pole normalization is what breaks.** `(s − 1/2) F1(s) → −1` as `s → 1/2`
  (`F1_pole_half`), so `F1` has a genuine pole at `1/2 ∉ {0, 1}`. Check N5 also shows the second
  residue, `(s − 5/2)F1(s) → π²/3`.
- **The E8 twin** is the case `a = 7/4`, the product `ζ(s/2+7/4)ζ(s/2−5/4)`. No zero has real part
  in `[−3/2, 5/2]` (`XiE8_zero_re`), and there are unconditional zeros with `5/2 < Re s < 9/2`
  (`XiE8_offline_zeros`). Check N4 exhibits one rigorously at `7/2 + 2iγ₁`.

### F. Theorem A, Step 3

The Cohn–Elkies function is written `ceF x = sinc(πx)² / (1 − x²)`. Lean's junk value at
`x = ±1` (division by zero) happens to coincide with the true limit 0, and `sinc 0 = 1`
supplies `f(0) = 1`. So `ceF` agrees at every point with the continuous extension of
`sin²(πx)/(π²x²(1−x²))`. (Continuity itself is not stated in Lean, and nothing below needs it.)
Its partner is
`ceFhat t = (1 − |t| + sin(2π|t|)/(2π))₊`.

Proved outright:

- `f ≤ 0` on `|x| ≥ 1`, vanishing there exactly on ℤ.
- `f̂ ≥ 0`. The key step is `sin(2πv) ≤ 2πv` after the substitution `v = 1 − |t|`.
- `f̂ = 0` on `|t| ≥ 1`.
- **Support forcing** (`ce_support_forcing`): a positive measure living on `|x| ≥ 1` with
  `∫ f dN = 0` is concentrated on the integers.

`thmA_step3_plus` and `thmA_step3_minus` then run the two cases of the report's Step 3. They take
the pairing identity `⟨ν, f⟩ = ⟨ν, f̂⟩` (respectively its `ε = −1` form, together with the
Gaussian pairing) as a **hypothesis**. So they are exactly as strong as Step 2, which is not
formalized.

### G. Rescaling

`s/d + 1/2 − 1/(2d) = 1 ⟺ s = (d+1)/2` (`rescale_pole`), and the substitution commutes with
`s ↦ 1 − s` (`rescale_reflect`). This is the whole algebraic content of "rescaling a degree-`d`
object to one gamma factor centered at 1/2 moves its pole to `(d+1)/2`". The identifications with
Dedekind and Epstein zetas are not formalized.

## The numerical companion (26 checks, all PASS)

| Check | What it does | Rigor |
|---|---|---|
| N1 (7 checks) | Computes `a0` and `Λ_{F0}` by exact rational recursion over the log-primes for `n ≤ 4096`. Confirms the Lean closed form at every `n`, `Λ_{F0}(4) = −4 log 2`, the negative set `{4, 16, …, 4096}`, the report's log-coefficients `4, −2, 10/3, −4, 34/5, −32/3`, and multiplicativity. | exact |
| N2 | Lemma C at prime conductor: self-reciprocity and `Λ_F(p²) = (1−p) log p < 0` for every prime `p < 100` and `ε = ±1`, by two independent derivations. | Arb balls |
| N2b (3 checks) | Lemma C at conductor `p²`: the recursion matches Newton power sums for `k ≤ 8`; `min_{k≤5}(1 − s_k) < 0` on 21,015 exact grid points; the minus branch violates `a(p)² ≤ 2a(p²)`. | exact rational |
| N3 (3 checks) | `Xi0`, `Xi1`, `XiE8` satisfy `X(1−s) = X(s)` at 5 generic points; `0 ∈` every difference ball; relative radius about `1e−73`. | Arb balls |
| N4 (6 checks) | `P0` vanishes at `1 + iπ/log 2` and `iπ/log 2`. The first zeta zero comes from Arb's rigorous `zeta_zero(1)` and is confirmed by an independent Hardy-Z sign change on `(14.134, 14.135)`. `F1(2ρ₁ + 1/2) = 0` at real part 3/2, and the E8 twin vanishes at `2ρ₁ + 5/2`, real part 7/2. A smoke test on the critical line: `min |F1(1/2+it)| = 0.159` for `t ≤ 80`. | Arb balls (the smoke test is a float grid) |
| N5 (2 checks) | The Beurling sum for `−F1'/F1` at `s = 8+3i` agrees with a 20000-term partial sum to `2.4e−13`, within the tail bound. The residues at `1/2` and `5/2` are `−1` and `π²/3`. | mpmath 50 digits (not interval) |
| N6 (3 checks) | sympy: the generic branch of `2∫₀¹ f̂(t)cos(2πxt)dt − f(x)` simplifies to `0`. The special points `x = 0, 1` and a 59-point grid are checked by 50-digit quadrature. Sign smoke tests. Poisson sanity for ζ. | symbolic + mpmath |
| N7 | Evidence for general Lemma C: for `q = 6, 10, 14, 15`, over the one-parameter self-reciprocal family and both signs, the best achievable `min_n Λ_F(n)/log n` over `q`-smooth `n ≤ 3000` is still negative (`−2.19, −2.23, −3.33, −1.61`). | float64, grid over the parameter (evidence, not proof) |

## What remains, stated plainly

1. **Theorem A, Steps 2 and 4.** Step 2 derives, from the functional equation and `N ≥ 0`, the
   distributional identity `ν̂ = εν + β(δ₀ − ελ)`: Mellin inversion, then density of Gaussians
   times `x^{2k}`. Step 4 is Hamburger's theorem. Neither is in Mathlib or here. Until they are,
   Theorem A and everything downstream of it (the conductor bound, the moving-zeros and DMV
   remarks, the twisted Beurling conjecture's `q = 1` base case) stay THEOREM-paper-proof.
2. **The Fourier identity `𝓕 ceF = ceFhat` in Lean.** This is doable: an elementary integral
   `2∫₀¹ f̂(t)cos(2πxt)dt`, then Mathlib's Fourier inversion. It would leave Steps 2 and 4 as
   Theorem A's only non-kernel inputs. It is not done here.
3. **Theorem B.** It needs the Kaczorowski–Perelli structure theorem for `S#_1` and
   Saias–Weingartner. Neither is formalized anywhere we know of.
4. **Lemma C beyond the single-prime conductors `p` and `p²`.** The paper proof uses
   simultaneous Dirichlet approximation on the axis polynomials (needed once an axis polynomial
   has degree ≥ 3, where several inverse roots with unrelated angles can share the maximal
   modulus), Landau's theorem for the mixed part, and Hadamard's factorization. The kernel has `q = p` and `q = p²` for every prime. Check N7 is
   numerical evidence for squarefree two-prime conductors.
5. **Prop D and the Landau half of the positivity lemma.** Landau's theorem (a Dirichlet series
   with nonnegative coefficients is singular at its real abscissa) is not in Mathlib.
6. **The E8 identification** `Σ_{v ∈ E8∖0} |v|^{−2u} = 240 ζ(u) ζ(u−3)`. It is classical but not
   formalized. The Lean "E8 twin" is the zeta product by definition.
7. **The twisted Beurling conjecture** (`q > 1`, non-integer frequencies) and the `μ ≠ 0` corner
   (poles at both 0 and 1, outside `S#`) remain open, exactly as the report says.

## Caveats a referee should hear from us first

- **There is no formal "class P" predicate.** The file checks each class-P condition separately
  on each near-miss: the functional equation, entire completion, coefficient sign,
  multiplicativity, P2, and the pole structure. A one-line `ClassP F` definition would force
  choices that the report leaves informal, such as how `Q`, `μ`, and `ε` enter. We did not make
  them.
- **"Entire of order 1" is not checked.** For `Xi0` and `Xi1` we prove entire and symmetric, not
  finite order. The order statement follows from the classical order of `ξ`, which Mathlib does
  not state.
- **The report states `F1`'s gamma factor as `Γ(s/2+3/4)` with `ε = −1`. Lean states it as
  `Γ_ℂ(s/2 − 1/4)` with `ε = +1`.** The two agree because
  `Γ(s/2 + 3/4) = (s/2 − 1/4) Γ(s/2 − 1/4)` and `(s/2 − 1/4)` is odd under `s ↦ 1 − s`. That
  conversion is algebra we did not re-state in Lean.
- **"About `T log T` zeros" is not checked.** Lean gives infinitely many off-line zeros of
  arbitrarily large height, not the counting asymptotic. The asymptotic would follow from the
  same Zeta23 counting theorem with more bookkeeping.
- **The Euler product over the Beurling primes `√p` is not checked for `F1`.** It is inherited
  from ζ's Euler product, but not stated in the file.
- **The Theorem A Step-3 theorems are conditional.** Their pairing hypotheses are exactly what
  Step 2 would produce. They check that the conclusion follows. They do not check that the
  hypothesis holds.
- **Relation to sibling work.** A class-P barrier file on another branch
  (`telperion/examples/class_p_barrier`, if present) covers the one-prime family
  `ζ(s)(1 + c p^{-s} + p·p^{-2s})`, of which `F0` is the case `(p, c) = (2, 3)`. It includes an
  explicit zero with real part in `(1/2, 1)` at `(29, 11)` and a finite conductor-4
  real-coefficient core. That file works at the level of local power sums. This one adds the
  analytic layer: `Λ_F` exists, is unique, and its values are forced.
