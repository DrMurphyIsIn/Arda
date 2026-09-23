# Class P = {zeta}: the buildable core, kernel-checked

conjecture1_proved = False. Nothing here proves, or claims to prove, anything about the Riemann
Hypothesis. The class-P question ("every F in P satisfies RH") turns out to be a relabeling of RH for
zeta itself (claim C4), and that stays open.

This directory holds the computational half of the build for the write-up *"Class P is the
one-element set {zeta}: the FE plus log-positivity forces F = zeta, with or without
multiplicativity"*. The Lean half is a single file:

    telperion/examples/li_positivity/lean/Crux/Crux_axiso_theorem.lean   (2079 lines, 98 theorems)

It is checked with

    cd telperion/examples/li_positivity/lean
    <scratchpad>/leanlock.sh lake env lean Crux/Crux_axiso_theorem.lean

The check exits 0 and prints 98 `#print axioms` lines. 97 of them are
`[propext, Classical.choice, Quot.sound]`. The remaining one, `IsQSmooth.dvd`, uses only
`[propext]`. The file contains no `sorry`, no `admit`, no `native_decide`, and no `axiom` or
`opaque` declarations. The toolchain is v4.34.0-rc1 with Mathlib `de5ce8a9`.

## The short version

The write-up's main theorem is C3. It says that if F satisfies the degree-1 functional equation
(P1) and log-positivity (P2), then F = zeta. No Euler product is needed. The published input is the
Kaczorowski-Perelli structure theorem for S#_1 (KP99). It says the Dirichlet coefficients of such
an F are periodic modulo the conductor q. After that, the write-up runs four steps. Each step uses
a piece of complex analysis: Pringsheim's theorem twice, Hadamard factorization and independence
of exponentials, Bohr means, and Landau's theorem.

We formalized the whole chain at the level of Dirichlet coefficients. Every analytic step was
replaced by something elementary enough for the kernel to check. The end product is
`classP_eq_zeta`:

> If `a = exp⋆(b)` (that is, F = exp G as formal Dirichlet series), `b ≥ 0` (P2), `a` is periodic
> mod `q` (the KP99 input), and the top coefficient of `P = F/ζ` satisfies `|P(q)| = √q` (the
> coefficient form of the FE), then `q = 1` and `a ≡ 1`. That is, F = ζ.

Two inputs remain outside the kernel, and both are hypotheses of that theorem:

1. **KP99 periodicity** (Acta Math. 182, 1999), together with the write-up's small argument that
   the twist `θ` is 0. This is a published theorem, used as a black box.
2. **FE ⟹ `|P(q)| = √q`.** Dividing F's functional equation by ζ's gives
   `q^{s/2} P(s) = ε q^{(1-s)/2} P(1-s)`. Comparing Dirichlet-polynomial coefficients then gives
   `P(q) = ε√q`. This is a routine paper step, but it is not in the kernel.

The claim "with or without multiplicativity" is honored: the Lean statement never assumes
multiplicativity.

## How the four steps became elementary

**Step 1: the unit part is zeta's.** Take k distinct primes, all congruent to one unit g mod q.
Mathlib supplies Dirichlet's theorem. On square-free products of these primes, the coefficients
of F and of log F form a moment-cumulant pair: `a` is the moment sequence `m_j = A(g^j)` and `b`
is the cumulant sequence (`IsDirExp.sqfree_cumulant`). The write-up then argues with Pringsheim,
Hadamard and exponential independence. The kernel instead checks a two-line inequality: if every
cumulant is nonnegative, then `m_{kt} ≥ t!·κ_k^t`. A periodic moment sequence is bounded, so every
cumulant of order two or more vanishes. This is `cumulant_rigidity`.

**Step 2: the q-smooth part is unit-invariant.** The write-up expands in Dirichlet characters and
uses Pringsheim on a rational function. The kernel proof uses the prime derivation `D_ℓ` (the
identity `v_ℓ(n) a(n) = Σ v_ℓ(d) b(d) a(n/d)`, which follows from `F = exp G` by a
derivation-commutation argument). At `m·ℓ·∏S` it gives `u_{k+1} = u_k + Σ(nonnegative b's)`, where
`u_j = A(m g^j)`. So `u` is monotone. It is also periodic, hence constant. The write-up's lemma
about forward differences is proved too (`finite_difference_rigidity`), and it is equally short:
Newton's forward formula makes `u` monotone.

**Step 3: `P = F/ζ` is a Dirichlet polynomial on the divisors of q.** The write-up uses Bohr means
and a contour shift. With periodicity in hand, this step is pure arithmetic (`step3`). The only
trick is that `p + q/p^e` is a unit mod q.

**Step 4: `|P(q)| ≤ 1`.** This is the step we are proudest of, and it may be new; we did not check
novelty. The write-up uses Landau's theorem on `-P'/P`, then Hadamard factorization of a zero-free
entire function of order 1. The kernel proof instead specializes every `p^{-s}` (for `p | q`) to one
variable t:

* The q-smooth part of F becomes `f(t)/V(t)`, where `f(t) = Σ_{d|q} P(d) t^{Ω(d)}` and V is a
  polynomial satisfying `V·Σ N_k t^k = 1`.
* The Ω-derivation gives nonnegative coefficients `B_k` of `t·(log)'`, and `B_k ≤ k·A_k`, which grows
  only polynomially. So `Σ B_k t^k` converges on the open unit disk.
* In the formal power-series ring, `V f B = X (V f' - V' f)`. At a root `z₀` of f inside the disk,
  cancel `(X - z₀)^{μ-1}` in the integral domain `ℂ⟦X⟧` and evaluate at the single point `z₀`.
  This gives `0 = z₀ μ V(z₀) g(z₀) ≠ 0`, a contradiction.
* So f has no root in the open disk. Then `|leading coefficient| ≤ |f(0)| = 1`, and the leading
  coefficient is `P(q)`.

Note that `step4_top_coeff` does not use the functional equation at all. **Log-positivity plus
periodicity alone force `|P(q)| ≤ 1`.** The FE demands `|P(q)| = √q`, so `q = 1`. The bound is
sharp: `P = (1 ± 2^{-s})(1 ± 3^{-s})` is log-positive with `|P(6)| = 1`, and the random search
below hits `|P(q)| = 1` for q = 2, 3, 6, 10.

## Claim-by-claim verdict

| claim | what the write-up says | status after this build |
|---|---|---|
| C1(i) | P2 gives `a_n ≥ 0` | **THEOREM-kernel-checked** (`IsDirExp.nonneg`) |
| C1(ii)-(iv) | `σ_a = σ_c = 1`, pole at 1, `μ = 0`, `ε = ±1`, `F ≠ 0` on `σ ≥ 1` | THEOREM-paper-proof (Landau, Gamma-pole bookkeeping). Referee note 1 below. The 3-4-1 trigonometric input is kernel-checked (`trig_341`). |
| C2 | Hamburger case: `Q = π^{-1/2}` forces F = ζ | THEOREM-paper-proof (Hamburger 1921; Titchmarsh 2.13). Not formalized. |
| C3 | every F with P1+P2 is ζ | **THEOREM-kernel-checked at the coefficient level** (`classP_eq_zeta`), modulo the two inputs above: KP99 (published) and FE ⟹ `|P(q)| = √q` (paper-level) |
| C3 Step 1 | unit part is zeta's | **THEOREM-kernel-checked** (`step1_units`, `cumulant_rigidity`) |
| C3 Step 2 | q-smooth part is unit-invariant | **THEOREM-kernel-checked** (`step2`, `finite_difference_rigidity`) |
| C3 Step 3 | P is a Dirichlet polynomial | **THEOREM-kernel-checked** (`step3`) |
| C3 Step 4 | P = 1 | **THEOREM-kernel-checked** as `|P(q)| ≤ 1` (`step4_top_coeff`, no FE needed), plus `classP_eq_zeta` |
| C4 | class-P RH ⟺ RH for zeta | THEOREM-paper-proof (immediate from C3). The exclusions of `L(s,χ)` and `ζ(s+iθ)` are one-liners. |
| C5 | Beurling: `q ≥ 1` (ε = +1, equality iff ζ), `q ≥ 2π/3` (ε = -1) | THEOREM-paper-proof. The numerics agree (Hermite eigenfunction to 3e-11, threshold 0.690988, Fejér identity). Not formalized. |
| C6 | zero-free region `σ > 1 - (7-4√3)/L(t)` | Final algebra **kernel-checked** (`dlvp_step`, `dlvp_opt`, `dlvp_opt_attained`, `dlvp_region`). The analytic inputs are THEOREM-paper-proof. The constant 2.430257 < 2.44 and the digamma bound are checked numerically. |
| C7 | P1 improves the rate only via rigidity | (a) identity, checked numerically. (b) THEOREM via C3 + Ford 2002. (c) literature. The meta-claim is HEURISTIC, as the write-up says. |
| C8 | RvM: `N_F(T) = (T/2π) log(qT/2πe) + 7/8 + S_F(T) + O(1/T)` | THEOREM-paper-proof (Davenport ch. 15 adaptation). The `log q` term was checked on `ζ(s)(1+5^{1/2-s})` at T = 50, 100, 200. The `2/5` bound was checked. |
| C9(i) | `ζ(s)(1+4·2^{-s}+2·4^{-s})` vanishes at `Re s₀ = 1.7716` | **THEOREM-kernel-checked**: exact FE, the zero, `b(4) = -11/2` (`nc_F_vanishes`, `ncLambda_one_sub`, `ncLambda_eq`, `a9_logcoeff_four`) |
| C9(ii) | KP conductor-5 element fails P2, `b = -2 = κ₄(log cosh)` | **THEOREM-kernel-checked** for the coefficient value (`a5_logcoeff`). Its S#_1 FE is checked numerically (residual 2e-31). |
| C9(iii) | E8-renormalized G has zeros off the line | THEOREM (exact algebra). Checked numerically (FE residual 2e-32, `|G| = 6e-31` at `3.5 + 28.2695i`). |
| C10 | Beurling class P has nothing with q > 1 | CONJECTURE-with-evidence. Not touched here. |

We also added two controls that the write-up does not have:

* **Non-vacuity** (`classP_hypotheses_satisfiable`): ζ satisfies every hypothesis of
  `classP_eq_zeta` with q = 1. So the theorem is not vacuous.
* **Sharpness** (`a2_topcoeff`, `a2_logcoeff_four`): `ζ(s)(1 + 2^{1/2-s})` is periodic mod 2,
  satisfies `|P(2)| = √2`, and has an exact FE. Only P2 fails: `b(4) = -1/2`. So P2 cannot be
  dropped.

## Referee notes on the write-up

These are the places a hostile referee will poke. None of them breaks a claim.

1. **C1(iii) needs a simple pole.** The 3-4-1 exclusion of `F(1+it) = 0` needs the pole at 1 to
   be simple, but simplicity is only derived in C1(iv): `Γ(s/2)` has a simple pole at 0, and the FE
   reflects the pole. With a pole of order m, 3-4-1 only excludes zeros of order above 3m/4. The
   logic is fine; the order of presentation should be swapped.
2. **C3 Step 4 skips a step.** The text goes from "P has no real zeros in (0, ∞)" straight to
   "P has no zeros on σ > 0". That needs a second application of Landau: with no real zeros,
   `σ_c(S) ≤ 0`, so S is analytic on σ > 0. The formal proof takes a different route and does not
   need this.
3. **C3 Step 3 (Bohr means) is unnecessary once periodicity is available.** Unit invariance plus
   periodicity make P a Dirichlet polynomial by pure arithmetic.
4. **The Pringsheim arguments in Steps 1-2 and the Landau/Hadamard argument in Step 4 are
   replaceable.** The replacements are above. They shrink the analytic surface of the proof to the
   KP99 black box and the FE bookkeeping.
5. **"Novelty vs literature not checked"** applies to our `|P(q)| ≤ 1` inequality and to the
   elementary proofs as well. We did no literature search.

## The numerical evidence

`verify_axiso_theorem.py` runs in about 30 seconds under `/usr/bin/python3` (numpy 1.23.5,
mpmath 1.3.0, 30 digits). It writes `verify_axiso_theorem_output.txt` and
`verify_axiso_theorem.json`. It uses exact rational arithmetic wherever the claim is
combinatorial. The log-coefficients come from the same Ω-derivation recursion the Lean file uses
(`IsDirExp.pmul_additive` with `w = Ω`), so no floating logarithms are needed. Highlights:

* **K1.** The Newton identity holds exactly. None of 3000 random nonconstant periodic sequences
  has all forward differences ≥ 0.
* **K2.** None of 2000 nonconstant periodic nonnegative moment sequences has all cumulants ≥ 0.
  The cumulants of (1,0,1,0,…) are `0, 1, 0, -2, 0, 16, 0, -272`, which are those of log cosh.
* **Steps 2 and 4 on random periodic data.** Every log-positive periodic example found (63 of them)
  is unit-invariant with `|P(q)| ≤ 1`, so there are 0 violations. Among random `P` on the divisors
  of q, the log-positive ones have max `|P(q)|` equal to 1 (q = 2, 3, 6, 10), 3/4, 5/8, or 1/2.
  All are far below `√q`.
* **Diagonal identity (R).** `k A_k = Σ B_j A_{k-j}` holds exactly on a q = 12 example.
* **C9.** `|F(s₀)| = 3e-31`, the FE residual is 4e-32, and `b(4) = -11/2` exactly. For the KP
  element, `b(36) = -1/2` and `b(8806) = -2` exactly, and the FE residual is 2e-31. For the E8
  control, `|G(3.5 + 28.2695i)| = 6e-31`.
* **C5.** Hermite `ψ̂ = ψ` to 3e-11, and `t_δ → √(3/2π) = 0.690988`. The Fejér identity gives
  0.7071068 vs 0.7071061 with 4e5 terms; the exact value is `√2/2`.
* **C6.** The constant is 2.430257, `c* = 7 - 4√3 = 0.0717968`, and the asymptotic constant is
  34.82. `Re ψ(z) - log|z| ≤ -1.85e-8` on the grid.
* **Self-dual periodic nonnegative data** (the FE-compatible case) at q = 2..12: every sample
  fails log-positivity. This is consistent with C3, which is now kernel-checked anyway.

## What remains open or unformalized

* KP99 is a black box, and so is `θ = 0` (the latter is short and could be formalized).
* FE ⟹ `|P(q)| = √q` needs the analytic FE of ζ in Mathlib (`completedRiemannZeta_one_sub`
  exists) plus uniqueness of generalized Dirichlet-polynomial coefficients. This is the most
  tractable next brick.
* C1(ii)-(iv): Landau's theorem for nonnegative Dirichlet series is not in Mathlib as far as we
  know.
* C2, C5, C7, C8 are not formalized. C10 is a conjecture.
* RH, of course. `conjecture1_proved = False`.

## Files

* `verify_axiso_theorem.py`: all numerical and exact checks, with the output files next to it.
* `verify_axiso_theorem_output.txt`: human-readable log of the last run.
* `verify_axiso_theorem.json`: every number from the last run.
* `lean_axiom_audit.txt`: the complete output of the prescribed `lake env lean` check, with 98
  `#print axioms` lines and nothing else (no errors or warnings).
* Lean: `telperion/examples/li_positivity/lean/Crux/Crux_axiso_theorem.lean`.
