# crux_fq_kernel: Theorem A in the kernel up to one classical step, and why it cannot see zeros

`conjecture1_proved = False`. Nothing in this directory, or in the Lean file it documents, proves RH,
reduces RH, or moves a clause of the wall. Every claim below is tagged THEOREM-kernel-checked,
THEOREM-paper-proof, CONJECTURE-with-evidence, HEURISTIC, or COMPUTED/Arb.

## The short version

Round 1's Theorem A is a rigidity statement. A positive "Beurling" measure `N` on `[1, ∞)` whose Dirichlet
transform `∫ x^{-s} dN` has zeta's exact functional equation (conductor 1, the pole normalization, finite
order) must be the integers: `N = Σ_{n≥1} δ_n`. The Fourier-quasicrystal (FQ) literature was the stronger
lead against it, and the round-2 kernel seat recast it in that language. The symmetric measure
`ν = δ₀ + N + N(-·)` is then a positive self-dual crystalline measure with a gap, and Theorem A says the
gap forces it to be the integer comb.

The seat got Steps 3 and 4 of that argument into the kernel. It left Step 2, "the FE implies the Poisson
identity on compactly supported tests". The seat judged that the obstacle was substrate: nobody had a
kernel route from the Gaussian or Schwartz tests that the FE naturally produces to the `C_c` tests that
Steps 3 and 4 consume.

This build supplies that route, so the harmonic-analysis half of Step 2 is now in the kernel. What is left
is a single classical piece of complex analysis, Hamburger's converse ("FE implies the modular relation"),
now stated in Lean as the `Prop` `HamburgerConverse`. A kernel theorem shows that round 1's registry
milestone `classP_collapse_beurling_q1` follows from it.

Along the way the build found and closed a gap in round 1's registry statement. Its `ZetaShapeFE`
quantifies the root number `ε` existentially. For `ε = -1` the converse gives an ANTI-modular relation,
and Theorem A's Fejér mechanism does not apply to that relation at all. A three-Gaussian LP certificate
now excludes that branch in the kernel (`no_antiTheta`).

Every theorem that the rigidity can see is about the prime side. The same file re-proves, in the new
modular-relation language, that the fooling family `ν_{p,c}` meets every hypothesis except the gap and has
zeros off the critical line. So the rigidity is still blind to zeros, exactly as the seat found.

## What Theorem A looked like before this build

- **Round 1.** Theorem A was a paper proof. Its Step 3 was kernel-checked, conditional on an unproved
  Cohn-Elkies pairing identity.
- **Round 2 kernel seat** (`examples/li_positivity/lean/Crux/CruxFQ_PoissonRigidity.lean`).
  - The Fejér pair `𝓕(max 0 (1-|x|)) = sinc²(π·)` is proved in the kernel.
  - Steps 3 and 4 are kernel theorems for any measure satisfying `IsPoissonPair ν β`. That predicate is
    `ν̂ = ν + β(δ₀ - Leb)`, tested on continuous compactly supported `f` with `ν`-integrable transform.
  - The file's header carried a CAVEAT: the `C_c` form was assumed directly, not derived from anything the
    FE gives you.
- **Open after round 2.** Step 2 in full. The route ran through Mellin inversion, a contour shift, and a
  Gaussian-to-`C_c` approximation. The approximation step was the missing substrate.

## What this build adds

All items are THEOREM-kernel-checked in `examples/li_positivity/lean/Crux/CruxFQ_kernel.lean`.

- **Size:** 2958 lines, 205 declarations.
- **Toolchain:** Lean v4.34.0-rc1, Mathlib de5ce8a9.
- **Imports:** Mathlib only.
- **Axioms:** all 37 audited declarations report exactly `[propext, Classical.choice, Quot.sound]`.
- **Clean:** no `sorry`, `admit`, `native_decide`, `axiom` or `opaque`.
- **Part 0:** re-states the seat's Theorem-A core verbatim under the namespace `CruxFQK`. The island builds
  Crux files one at a time, so the seat file cannot be imported.

### 1. Even-test reduction (`isPoissonPair_of_even`)

This is the cheap item on the seat's list. For a negation-invariant `ν`, the Poisson identity on even
`C_c` tests implies it on all `C_c` tests. The proof applies the even-test identity to
`(f + f(-·))/2` and shows that each of the four terms matches the corresponding term for `f`.

### 2. Gaussian determination (`isPoissonPair_of_theta`): the missing substrate

Let `ν` be a positive, locally finite, even measure with every Gaussian integrable. Suppose it satisfies
the modular relation

    θ_ν(1/t) = √t · θ_ν(t) + β(√t - 1)   for all t > 0,   where θ_ν(t) = ∫ e^{-π t x²} dν(x).

Then `IsPoissonPair ν β` holds on every continuous compactly supported test. The theorem needs only real
Gaussians, and it assumes no Schwartz-class or `C_c` identity. The proof has four steps, and each one is a
named kernel lemma.

1. **Regularize.** Define `T_s(h) = T(h * G_s)`, the Poisson defect of the test after Gaussian smoothing.
   It is written out so that no convolution theorem is needed (`Tdef`).
2. **Vanish on Gaussians** (`Tdef_gauss`). `T_s(G_t) = 0` for all `s, t > 0`. This is the modular
   relation evaluated at `u = st/(s+t)`, together with the identity `G_t * G_s = (s+t)^{-1/2} G_u`.
3. **Bound, then approximate.** `T_s` is linear, and on tests dominated by `C e^{-πx²}` it is bounded by
   `C·K_s` (`norm_Tdef_le`).
   - An even `C_c` test is a function of `z = e^{-πx²} ∈ (0,1]`.
   - The Weierstrass theorem in `z` approximates it within `ε e^{-πx²}` by a finite combination of the
     Gaussians `e^{-π(i+1)x²}` (`exists_gauss_poly_approx`).
   - Together these give `T_s(f) = 0` for every even `C_c` test (`Tdef_even_eq_zero`).
4. **Remove the regularization** (`tendsto_sqrt_mul_Tdef`). `√s · T_s(f) → T(f)` as `s → ∞`. This is an
   approximate-identity argument with dominated convergence on both sides.

**Novelty.** The mathematical content is classical: a tempered even distribution that kills every centred
Gaussian kills every even test (Hermite completeness, Bochner's modular relations). What is new is only
that it is now a kernel theorem in the exact form Theorem A consumes.

### 3. Theorem A from the modular relation alone (`thmA_theta`, `thmA_theta_selfDual`)

Hypotheses:
- `ν` is positive, locally finite, even and Gaussian-integrable;
- `ν` has no mass in `(-1,1) \ {0}`;
- `ν` satisfies the modular relation.

Conclusions:
- `ν` lives on `ℤ`;
- `ν{m} = ν{0} + β` for every `m ≠ 0`;
- `ν` is the sum of its atoms;
- if `β = 0`, then `ν = ν{0} · Σ_{n∈ℤ} δ_n`.

The seat needed `sinc²`-integrability as a hypothesis. Here it is derived (`integrable_fej_of_theta`). The
modular relation gives `θ_ν(4^{-i}) ≤ 2^i(θ_ν(1) + 2‖β‖)`, which is linear growth, and a dyadic Gaussian
majorant of the Fejér kernel does the rest. Two further corollaries also hold in theta form:
- a wider gap forces `ν = 0` (`theta_gap_gt_one_forces_zero`, LP sharpness);
- every unit window has bounded mass (`translation_bounded_of_theta`).

The last is the kernel shadow of the statement that zeta's zero measure, whose windows grow like
`(1/2π) log T`, can satisfy no relation of this shape.

### 4. Controls in theta form

- **Positive control.** The integer comb satisfies every hypothesis, via Jacobi's identity from Mathlib's
  Gaussian Poisson summation (`intComb_theta_admissible`). Item 2 then re-derives its `C_c` Poisson
  identity from Jacobi alone.
- **Fooling family, round 2.** `ν_{p,c} = p^{-1/2} comb(1/p) + c comb(1) + p^{1/2} comb(p)` satisfies
  Jacobi's relation exactly (`nup_theta`). It is even, positive, locally finite and Gaussian-integrable.
  Item 2 re-derives its `C_c` self-duality (`nup_isPoissonPair_via_theta`), which independently checks
  the seat's `nup_isPoissonPair`.
  - Its completed Mellin transform `Λ_ζ · Q_{p,c}` has zeta's exact FE.
  - For `2 < c < √p + 1/√p` it has a zero with `1/2 < Re s < 1`.
  - The only hypothesis it violates is the gap (`theta_rigidity_is_rh_blind`).
- **Onset.** Below the threshold, for `c ≤ 2`, the theta data are the same and every zero of `Q_{p,c}` is on
  the line. The onset `c = 2` is exactly local Ramanujan (`theta_fooling_onset`).
- **Round 1's controls.** W1(29,11) and the golden fake both satisfy Jacobi's relation exactly
  (`controls_in_theta_form`).

### 5. Round 1's milestone NT4, reduced to one step

The registry definitions `BeurlingNormalized` and `ZetaShapeFE` are copied verbatim from
`docs/RH_AXIOM_ISOLATION_2026-09-22.md` §5.2.

- **`classP_collapse_beurling_q1_of_theta`.** Let `N` be a normalized Beurling measure whose even
  extension `δ₀ + N + N(-·)` satisfies the modular relation, for any `β`. Then
  `N = Σ_{n≥1} δ_n`. Gaussian integrability is derived from the polynomial growth by a dyadic ratio-test
  argument (`integrable_gauss_of_beurling`). The atom `N{1} = 1` forces `β = 0`.
- **`classP_collapse_beurling_q1_of_hamburgerConverse`.** `HamburgerConverse` implies the registry
  statement `classP_collapse_beurling_q1`.

### 6. The root number is forced (`no_antiTheta`, `step2_of_hamburgerConverse`)

The registry's `ZetaShapeFE` allows either root number. For a real measure `ε = ±1`. When `ε = -1`, the
classical converse gives the anti-modular relation

    θ_ν(t) + t^{-1/2} θ_ν(1/t) = c (1 + t^{-1/2}),   i.e.  ν̂ = -ν + c(δ₀ + Leb) on Gaussians.

Theorem A's support-forcing argument is useless here. The Fejér test gives `∫ sinc² dν = 2c > 0`, which
forces nothing. The Cohn-Elkies-style LP does the job instead.
- **The test.** `K = 2G_1 - G_4 - G_{1/4}/2` is self-dual: `K = f + 𝓕 f` with `f = G_1 - G_4`. It
  satisfies `K(0) = 1/2` and `K ≤ -G_4 < 0` on `|x| ≥ 1`. The margin is `e^{3π/4} ≥ 4`.
- **The contradiction.** Two instances of the relation, at `t = 1` and `t = 4`, give
  `∫ K dν = θ_ν(1)/2`. Positivity and the gap give `∫ K dν ≤ ν{0}/2 + K(1) ν{1}`, while
  `θ_ν(1) ≥ ν{0} + e^{-π} ν{1}`. These are incompatible once `ν{1} > 0`.

So the only branch the converse can produce is the one Theorem A handles. This resolves an issue in the
registry statement that neither round noted, and it does so in the kernel.

## What is still open: exactly one classical step

`HamburgerConverse` is stated as a `Prop` in the Lean file and is NOT proved:

> for every normalized Beurling `N` with `ZetaShapeFE 1 N`, the even extension `δ₀ + N + N(-·)`
> satisfies the modular relation (some `β`) or the anti-modular relation (some `c`).

This is Hamburger's converse, in Bochner's modular-relation form, with the root-number bookkeeping made
explicit. It is THEOREM-paper-proof, classical and not re-derived here. It uses no positivity: all the
positivity content of Theorem A is now in the kernel.

There is a kernel route that avoids residues.
- **Remove the poles.** Apply `L = (t d/dt)(4 t d/dt + 2)` to `θ_N`. Its Mellin transform becomes
  `ξ(2s)`, which is entire.
- **Invert and shift.** Invert on a line where the Gamma decay is explicit. Shift to `Re s = 1/2 - c`;
  the rectangle Cauchy theorem (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) applies
  with no residues. The horizontal decay comes from finite order and
  `PhragmenLindelof.vertical_strip`.
- **Transfer.** The FE then gives `Lθ_N(t) = ε t^{-1/2} (Lθ_N)(1/t)`. `L` commutes with
  `h ↦ t^{-1/2} h(1/t)`, and its kernel is `{A + B t^{-1/2}}`, so the modular relation (sign `ε`)
  follows from an ODE uniqueness argument.

Two pieces are missing from Mathlib: vertical decay of `Γ` off the special lines, and the PL bookkeeping.
The reverse implication (modular relation implies FE) is Mathlib's `WeakFEPair` machinery. It is not
wired here, and nothing here depends on it.

Also not formalized: the converse of item 2 (`IsPoissonPair` implies the modular relation). It is
classical and not needed for Theorem A.

## Why none of this touches RH (negative-control ledger)

- **What Theorem A constrains.** In any form it constrains the prime side (the Dirichlet data). It makes
  no claim about zeros, so no zero-side control can refute it. Its hypotheses exclude each control:
  - Davenport-Heilbronn: signed coefficients, conductor 5, so not a positive weight-1/2 theta relation;
  - Epstein zeta: its theta relation has weight 1 on a 2-D lattice, not weight 1/2;
  - W1 and the golden fake: they satisfy the relation but violate the gap (kernel).
- **The fooling family is the surgered-zeta control in crystalline form.** It passes every linear-scale FQ
  test, including now the modular relation itself, and it has off-line zeros exactly when local Ramanujan
  fails at `p`. Any argument from "theta relation + positivity" to zero location is refuted by it
  (THEOREM-kernel-checked).
- **Circularity (test a):** nothing here is RH-equivalent; the statements concern the prime side.
- **Euler-blind (test b):** not applicable, since no zero claim is made. The family shows that the
  separating property (local Ramanujan) is invisible to the theta data.
- **Tests c and d:** not applicable.

## The d = 2 Epstein rung, now Arb-certified

In `d = 2` the Theorem-A package is not rigid. The class-number-2 form `Q2 = 3m² + mn + 3n²` (disc
`-35`), rescaled to covolume 1, satisfies it and has off-line zeros. The seat had these as COMPUTED
(mpmath). `epstein_d2_arb.py` certifies them with Arb, using the whole-segment-enclosure argument principle
from `research/axiso_literature/arb_winding.py`. The function is
`Z(s) = ζ(s)L(s,χ_{-35}) - L(s,χ_{-7})L(s,χ_5)`.

| box (Re × Im) | certified winding | off-line |
|---|---|---|
| [0.76, 0.80] × [19.30, 19.35] | 1 | yes |
| [0.20, 0.24] × [19.30, 19.35] (FE partner) | 1 | yes |
| [0.63, 0.67] × [55.87, 55.92] | 1 | yes |
| [0.61, 0.645] × [78.63, 78.67] | 1 | yes |
| [0.81, 0.845] × [92.40, 92.45] | 1 | yes |
| [0.56, 0.59] × [101.11, 101.16] | 1 | yes |

Each winding is read from an Arb interval `[1 ± 5e-31]` or tighter, at 128-bit precision; the whole run
takes 42 s in a single process. The script also runs three sanity checks before certifying:
- the Conrey characters `(7,6)`, `(5,4)`, `(35,34)` equal the Kronecker symbols for `n < 2000`;
- the decomposition matches the direct lattice sum at `s = 3` to 5.3e-12, which is the truncation tail
  at `R = 300`;
- the completed FE holds to `[± 9e-40]`.

Trust class: Arb ball arithmetic, not Lean kernel. Output: `epstein_d2_arb.json`, `epstein_d2_arb.log`.

## Numerical cross-checks

`theta_checks.py` runs at 40 digits in a single process and writes `theta_checks.json`. It checks:
- Jacobi for the comb (defect 2e-41);
- the modular relation for `ν_{29,11/√29}`, `ν_{5,√5}` and `ν_{2,2.1}` (defects of 1e-38 or less);
- the pole footprint `β = c - r` for `rδ₀ + cΣ_{n≠0}δ_n`;
- the growth bound `θ(4^{-i}) ≤ 2^i θ(1)`.

It also runs a negative control: `comb + δ_{±1/2}` satisfies no modular relation, because
`(θ(1/t) - √tθ(t))/(√t - 1)` is not constant.

## Draft registry nodes (statement-only; grant only after commit, CI and AxiomGuard wiring)

| node | kind | artifact | status now |
|---|---|---|---|
| `RH_gaussian_determination` | lemma | `CruxFQ_kernel.lean` `isPoissonPair_of_theta` | kernel, untracked |
| `RH_thmA_theta` | theorem | `thmA_theta`, `thmA_theta_selfDual`, `integrable_fej_of_theta` | kernel, untracked |
| `RH_thmA_crystalline` | theorem | seat file `poisson_rigidity` (also restated here) | kernel, untracked |
| `RH_NT4_reduced_to_hamburger_converse` | lemma | `classP_collapse_beurling_q1_of_hamburgerConverse` | kernel, untracked |
| `RH_beurling_root_number_forced` | lemma | `no_antiTheta`, `step2_of_hamburgerConverse` | kernel, untracked |
| `RH_classP_collapse_beurling_q1` | milestone | unchanged; open exactly at `HamburgerConverse` | STATED ONLY |
| `MM_fooling_family_theta_offline` | lemma | `theta_rigidity_is_rh_blind` part 3 | kernel, untracked |
| `MM_onset_is_local_ramanujan` | lemma | `theta_fooling_onset` / `satake_ramanujan_iff` | kernel, untracked |
| `MM_zero_side_fejer_archimedean` | lemma | seat file `rvm_bridge/.../CruxFQ_ZeroSideFejer.lean` | kernel, untracked |
| `RH_negctl_epstein_d2_offline` | data | `epstein_d2_arb.json` | Arb, not kernel |

## Literature pointers

None of these was re-read in this build.

- **Hamburger's theorem.** H. Hamburger, *Math. Z.* 10 (1921), with sequels in vols. 11 and 13; Titchmarsh,
  *The Theory of the Riemann Zeta-Function*, §2.13.
- **The modular relation and its equivalence with the FE.** S. Bochner, "Some properties of modular
  relations", *Ann. of Math.* 53 (1951); K. Chandrasekharan and R. Narasimhan, "Hecke's functional equation
  and arithmetical identities", *Ann. of Math.* 74 (1961).
- **The distributional Poisson form.** J.-P. Kahane and S. Mandelbrojt, *Ann. Sci. ÉNS* 75 (1958). The
  rigidity seat located it; its growth hypotheses were never checked against "finite order", as
  RH_AXIOM_ISOLATION §6 notes.
- **FQ neighbourhood.** Cohn-Elkies 2003 (1-D LP); Lev-Olevskii 2015 and 2017; Kurasov-Sarnak 2020. Novelty
  of Theorem A in theta form is CONJECTURE-with-evidence (not found by the literature seats); an expert
  check is recommended.
- **The `d = 2` control.** Davenport-Heilbronn 1936 (Epstein zeta functions with class number > 1).

## How to check

```
cd telperion/examples/li_positivity/lean && leanlock.sh lake env lean Crux/CruxFQ_kernel.lean
cd telperion/research/crux_fq_kernel && python3 epstein_d2_arb.py && python3 theta_checks.py
```

`lean_axioms_transcript.txt` in this directory is the full `#print axioms` output: 37 lines, all standard,
exit 0.

## Files

- `epstein_d2_arb.py`, `.json`, `.log`: the Arb certification.
- `theta_checks.py`, `.json`: the numerical cross-checks.
- `lean_axioms_transcript.txt`: the Lean axiom audit.
- `../../examples/li_positivity/lean/Crux/CruxFQ_kernel.lean`: the kernel file. It is untracked, like
  every Crux file; sha256 `03a8e42b40a4d60ff31826e9e1d082b00c42bce0668c20e829cfc10d41685630`.

`conjecture1_proved = False`.
