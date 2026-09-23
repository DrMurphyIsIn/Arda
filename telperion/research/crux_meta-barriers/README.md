# The golden-fake barrier: the buildable core, built, corrected, and bounded

`conjecture1_proved = False`. Nothing in this directory, or in either Lean file that goes with it,
says anything about where the zeros of the Riemann zeta function lie. This is a meta-result. It
bounds what one class of arguments can do. It does not advance any argument.

## The story in four paragraphs

The proposal (lens: META-MATHEMATICS / BARRIERS) was a relativization barrier with a twist. Its
counterexample model keeps the Euler product, so the Davenport–Heilbronn negative control cannot
dismiss it. The model is the "golden fake". Take the genus-one zeta function of a formal curve over
F_5 with trace m = ±5:

    Z(T) = (1 - mT + 5T²)/((1 - T)(1 - 5T)).

It has every formal property of an elliptic-curve zeta function except the Hasse bound m² ≤ 20, so
its Riemann hypothesis fails. Glue it onto ζ at the prime 5 to get the "hybrid"
`ζ(s)·Z(5^{-s})`. The hybrid is an ordinary Dirichlet series. Its Euler product has nonnegative
von Mangoldt weights, and its completion is entire, symmetric and of order one. The proposal
claimed that the hybrid also satisfies every hypothesis-free conclusion the corpus has proved about
ζ, while having zeros off the line. If so, no argument built only from those conclusions can prove
RH.

We built the parts of that claim that can be settled today, in the kernel where possible. What
survives is real and fairly sharp. The hybrid's completion `XiH = ξ·XiA` provably satisfies the
corpus's pointwise zero-location layer: Box 1, Box 2, the effective de la Vallée Poussin region, no
real zeros, and the Li disk condition. Its Li rungs 0..4 are nonnegative. On the rvm_bridge island,
the multiplicity-weighted zero side of the entire function `ξ·XiA` satisfies both flagship Gaussian
instruments of the Wall: E6Bridge30 (every centre, widths ≤ 3/2000) and the E6Bridge16 envelope
(widths ≤ 1/40). All of that holds exactly as it does for ζ, and yet `XiH` has a zero at
`0.799 + 1.952i`.

Two things did not survive, and both are theorems here too. First, a **correction**: the literal
hybrid `ζ(s)Z_{5,-5}(5^{-s})` has a **double pole** at s = 1, so it is not in the proposal's class.
A repaired model, `H4 = ζ(s)(1 + 5·5^{-s} + 5·5^{-2s})/(1 - 4·5^{-s})`, fixes the pole at 1 but pays
with a pole at the real point `log 4/log 5 = 0.861`, inside the strip. Second, the **limits**: that
trade is forced (the "pole shadow" theorem). Moreover every such lattice fake has an off-line zero
below height π/log 2 < 4.54, which the corpus's finite certificates exclude. So the barrier does NOT
support the dossier heuristic "every finite certificate is compatible with an off-line zero". For
lattice models the opposite is a theorem.

## Where things live

| File | What it is |
|---|---|
| `telperion/examples/li_positivity/lean/Crux/Crux_meta_barriers.lean` | Lean (v4.34.0-rc1, Mathlib de5ce8a9), 2034 lines, namespace `CruxMetaBarriers`. It holds the genus-one theory, the fake's zero set, the hybrid and the pointwise layer, the Li rungs, the Euler side (the double-pole correction and the repaired model), and the limits (pole shadow, lattice). Its 161 `#print axioms` lines all report a subset of `[propext, Classical.choice, Quot.sound]`. |
| `telperion/examples/rvm_bridge/lean/Crux/Crux_meta_barriers.lean` | Lean (v4.33.0-rc2, Mathlib 51e6992e, Zeta23), 1477 lines, namespace `CruxMetaBarriersRvM`. It holds the Gaussian layer: the fake Gaussian sum is ≥ 0 for every centre and every width ≤ 1/40, the hybrid (`ξ·XiA`, the corpus's own ξ) satisfies E6Bridge30 and E6Bridge16, and at width 1/2 the Wall detects the fake. Its 88 `#print axioms` lines all report a subset of the standard three. |
| `golden_fake_numerics.py` | The numerical companion: 14 checks N1–N12, each marked PASS or FAIL, exit code nonzero on any failure. Runs in about 45 s with `mpmath`, `numpy`, `json`. |
| `outputs/numerics.json`, `outputs/numerics_summary.txt` | The numerics results. |
| `outputs/lean_print_axioms_li_positivity.txt`, `outputs/lean_print_axioms_rvm_bridge.txt` | Transcripts of both kernel checks. Each exited 0 with no errors and no warnings. |

Neither file contains `sorry`, `admit`, `native_decide`, a new `axiom` declaration, or `opaque`.

## How to check it yourself

```sh
cd telperion/examples/li_positivity/lean
<scratchpad>/leanlock.sh lake env lean Crux/Crux_meta_barriers.lean     # ~45 s, exit 0, 161 axiom lines

cd ../../rvm_bridge/lean
<scratchpad>/leanlock.sh lake env lean Crux/Crux_meta_barriers.lean     # ~40 s, exit 0, 88 axiom lines

cd ../../../research/crux_meta-barriers
/usr/bin/python3 golden_fake_numerics.py                                # ~45 s, 14 PASS
```

The Lean files are checked by single-file elaboration against each island's prebuilt `.lake`. They
are not wired into any `lakefile` or CI guard; see "What remains".

## The mathematics that was built, with honest tags

The status tags are THEOREM-kernel-checked, THEOREM-paper-proof, CONJECTURE-with-evidence, and
HEURISTIC.

### 1. Genus one: the formal Euler axioms give exactly the trivial bound (kernel)

For a formal datum `(q, m)` the Lefschetz numbers `N_n = q^n + 1 - t_n` are the von Mangoldt
weights at `q^n` in units of `log q`. The build proves:

* `admissible_iff` (q ≥ 2): the positive residue, a nonnegative degree-two place count, and
  `N_n ≥ 0` for all n hold **iff |m| ≤ q**. The positivity half is new relative to the proposal,
  which had it only at q = 5. It is `N_pos_of_abs_le`, proved for every q. The complex-root case
  uses the Lucas identity `t_n² - (m² - 4q)U_n² = 4q^n`. In the real-root case both roots have
  modulus > 1.
* `rh_int_iff_zeros`, `rh_iff`: RH for the datum, meaning every zero of
  `Xi = 2cosh((s-1/2)log q) - m/√q` lies on the line, holds iff `m² ≤ 4q`.
* `exists_admissible_not_rh_iff`: an admissible RH-violating datum exists **iff q ≥ 5**.
* `hasse_iff`: Hasse/Rosati positivity of `r² - mrs + qs²` is equivalent to RH. At this abstract
  level that is a relabeling, as the proposal said. `N_eq_det`: `N_n = det(A^n - 1)` for the
  companion matrix (the toral-dynamics model).
* The golden data `(5, ±5)` have `N_n ≥ 1` for every n. Their place counts `a_1..a_10` are the
  listed nonnegative integers (checked by `decide` and by numerics N2). Over F_5 every trace in
  `[-4, 4]` belongs to a real elliptic curve (N2b).

A subtlety the proposal missed (numerics N1, q = 2..40). With only `Λ ≥ 0` and a positive residue,
the admissible range is `[-(q+1), q]`, not `[-q, q]`. The extra point `m = -(q+1)` has zeros exactly
on `Re s = 1`. Either the place-count axiom or "F ≠ 0 on Re s ≥ 1" removes it.

### 2. The anti-golden fake's zero set (kernel)

`XiA s = 2cosh((s-1/2)log 5) + √5` vanishes **exactly** at `1/2 ± x0 + i(2k+1)π/log 5`, with
`x0 = log φ/log 5 = 0.29899…` (`XiA_eq_zero_iff`). Every one of these zeros is simple
(`XiA_zero_simple`, `deriv_XiA_ne_zero`), inside the strip, off the line, and at height
`≥ π/log 5 = 1.95198…`. The zero set is periodic under `s ↦ s + 2πi/log 5` (`XiA_periodic`).

### 3. The hybrid satisfies the corpus's pointwise layer (kernel)

`XiH = riemannXi·XiA` (upstream `LiCriterion.riemannXi`) is entire (`XiH_entire`), symmetric
(`XiH_one_sub`), and real on ℝ (`XiH_conj`). Its zero set is `{nontrivial ζ-zeros} ∪ {fake zeros}`
(`XiH_eq_zero_iff`). The structure `PointwiseLayer Z` collects the following clauses:

* strip, reflection and conjugation symmetry;
* Box 1, `√3/2 ≤ |Im ρ|`, and Box 2, `(Re ρ - 1/2)² ≤ (Im ρ)²/3 - 1/4` (`LowHeightBox`);
* no real zeros;
* the effective dVP region `Re ρ ≤ 1 - dlvpRateC/log|Im ρ|` for `|Im ρ| ≥ 55/16`
  (`ZeroFreeBridge.riemannZeta_ne_zero_region`);
* the Li disk condition `Re(ρ(1-ρ)) ≥ 1`, from which `LiBoxRungs` derives the Li rungs 0..4.

`zeta_pointwiseLayer` (non-vacuity) and `hybrid_pointwiseLayer` both hold. Hence
`pointwise_layer_does_not_imply_rh`.

`hybrid_li_rungs` gives `0 ≤ Re(hybridLi n)` for n < 5, where `hybridLi n` is ζ's upstream
`taylorCoeff riemannXi n` plus the fake paired zero sum. The fake sums are proved summable
(`summable_fake_pairTerm`) and termwise nonnegative (`pairTerm_re_nonneg`, which uses LiBoxRungs's
disk polynomials Q1..Q5). **Paper-level:** the identification of `hybridLi n` with the Li
coefficient of `XiH`, which rests on additivity of log-derivatives and the fake's symmetric
Hadamard product. Numerics N5 confirm it: the Taylor coefficients of `log XiA(1/(1-z))` match the
paired zero sums, and `λ_1 = XiA'(1)/XiA(1) = 0.58525…`.

### 4. The Gaussian layer, on the rvm_bridge island (kernel)

* `fake_gaussian_nonneg`: for every centre c and every `0 < λ ≤ 1/40`, the corpus's
  `gaussTest c λ`, summed over all fake zeros, has nonnegative real part. The proof is an explicit
  lattice argument: the nearest pair of fake ordinates contributes at least `1 - 0.16e`, and the
  far tail is majorized by `e^{-|u|/2}/100` and summed by a two-sided geometric series.
  Numerically the fake sum stays positive for all c up to `λ* = 0.182711…` (N4b), which confirms
  the proposal's "0.18".
* `analyticOrderNatAt_XiHR`: `XiHR = RvMBridge18.xi·XiA` (the corpus's own ξ) has analytic order
  `zeroMult ρ + [XiA ρ = 0]` at every ρ. `XiHRZeroSide_eq` shows that its multiplicity-weighted zero
  side is ζ's `zeroSide` plus the fake side.
* `XiHR_gaussian_positivity_small`: the zero side of `ξ·XiA` satisfies **E6Bridge30** (every c,
  every `λ ≤ 3/2000`). `XiHR_gaussian_envelope`: it satisfies the **E6Bridge16 sharp envelope** at
  every `λ ≤ 1/40`.
* `fake_gaussian_negative`: at `λ = 1/2` and `c = π/log 5` the fake sum is **negative**. The Wall,
  which asks for every width, is therefore not blind to the fake. Only the proved widths are. N10
  shows the same numerically for the hybrid: for `λ ≥ 0.19` the hybrid sum is negative near the
  fake heights.

This is the core of the barrier. Each of the corpus's two proved Gaussian instruments certifies ζ
and certifies an explicit entire function with an off-line zero, by the same statement.

### 5. The Euler side: correction and repair (kernel)

The functions `Hlit`, `H4`, `gammaLit` and `gammaH4` are defined in the li_positivity file.

* **Correction.** `Hlit_double_pole`: `(s-1)²·Hlit(s) → 11/(4 log 5)`. `Hlit_not_simple_pole`: no
  limit of `(s-1)·Hlit(s)` exists. The proposal's Theorem B ("H is a P-datum") therefore fails
  clause P3 (a simple pole).
* **Repair.** `H4` has the following properties:
  * `XiH_eq_completion_H4`: its completion is the same `XiH`, with the explicit factor
    `gammaH4 = ½s(s-1)Γ_ℝ(s)·5^{s-½}(1 - 4·5^{-s})`.
  * `w4_pos`: its von Mangoldt weights at 5 are `1 + 4^n - t_n(5,-5) ≥ 1` for every n.
  * `H4_simple_pole`: `(s-1)H4(s) → 11`.
  * `H4_pole_in_strip`: it pays with a simple pole at `s4 = log 4/log 5 ∈ (1/2, 1)`, with residue
    `ζ(s4)·(41/16)/log 5 ≠ 0`. `gammaH4_zero_in_strip` shows that the completion factor vanishes
    there to absorb it.
  * `w4_even_ge`: Ramanujan fails at 5, since `Λ(5^{2j+2}) ≥ (1 + 4^{2j}) log 5`.

### 6. Limits: what separates ζ from every lattice fake (kernel)

* `pole_shadow`: take a genus-one local factor `P_{q,m}(T)/∏_j(1 - δ_j T)` with an off-line zero
  (`m² > 4q`), and suppose every inverse pole satisfies `|δ_j| ≤ R < bigRoot`, i.e. every pole
  lies strictly left of the zero. Then for every constant C some weight
  `C + Re Σ_j δ_j^n - t_n` (n ≥ 1) is **negative**. Positivity therefore forces a local pole at
  least as far right as the zero. N8 gives the sharp modulus for the golden hybrid: `√14 = 3.7417`,
  binding at n = 2, which sits at `Re s = 0.8199 > 0.7990`.
* `local_rh_of_positivity`: positivity plus "no pole of the local factor in Re s > ½" forces
  `m² ≤ 4q`. The sibling near-miss `F0 = ζ(s)(1+2^{-s})(1+2^{1-s})` of Crux_axiso_construct is the
  q = 2 instance of the contrapositive: it has no local pole, `m = -3`, and `Λ(4) = -4 log 2`.
* `local_factor_periodic`, `local_zero_low_copy`: every zero of a polynomial local factor at
  `p ≥ 2` has a copy with the same real part at height `≤ π/log 2 < 4.54`.
* `genus_one_low_offline_zero`: every RH-violating admissible genus-one datum has an off-line zero
  in the open strip at height `≤ π/log q`. N9 checks all 545,924 such data over prime powers
  q ≤ 2000. Half of them have a real off-line zero, and the highest "lowest zero" is at height
  1.952.
* `hybrid_zero_in_certified_box`: the golden hybrid has an off-line zero inside
  `[0.001, 0.999] × [0, 55/16]`. That is exactly the box the corpus certifies zero-free for ζ, in
  `NoZerosInBox_1d1000_999d1000_0_55d16`, which is conditional on Arb inputs.

The single statements `golden_fake_barrier` (li_positivity) and `gaussian_layer_barrier`
(rvm_bridge) package all of this.

## Claim-by-claim ledger against the proposal

| Proposal's claim | Proposal's tag | Verdict after this build | Where |
|---|---|---|---|
| Trivial bound: pole + a₂ ≥ 0 ⟹ \|m\| ≤ q | kernel | **kernel** (reproved) | `trivial_bound` |
| RH for genus one ⟺ Hasse bound, with an explicit off-line zero | kernel | **kernel** | `rh_iff`, `offline_zero_explicit`, `rh_int_iff_zeros` |
| Golden fakes: N_n ≥ 1, place counts, N_n = det(A^n - 1) | kernel | **kernel** | `N_golden_pos`, `N_anti_pos`, `euler_*`, `N_eq_det` |
| Missing axiom = Hasse/Rosati (a relabeling) | kernel | **kernel** (relabeling, as stated) | `hasse_iff`, `golden_negative_degree` |
| Exact square-root gap: admissible ⟺ \|m\| ≤ q | 'only if' kernel, 'if' paper | **kernel** at the Λ-level for every q ≥ 2; integrality of a_d for all d remains paper (toral dynamics) plus numerics (N1, d ≤ 60) | `admissible_iff`, `N_pos_of_abs_le` |
| H = ζ·Z_{5,-5}(5^{-s}) is a P-datum | paper | **FALSE as stated**: double pole at s = 1 (kernel). The repair H4 is a P-datum literally, with a pole in the strip (kernel) | `Hlit_double_pole`, `H4_*` |
| H satisfies every hypothesis-free corpus conclusion | paper | **FALSE as stated**: it violates the finite certificates (kernel: its zero lies in the certified box). **TRUE** for the listed layer: pointwise (kernel), Li rungs 0..4 (kernel modulo identification), Gaussian small width (kernel), Gaussian envelope (kernel for λ ≤ 1/40, paper beyond) | sections 3-6 |
| Gaussian F_fake > 0 ∀c when λ ≤ 0.18 | paper + numerics | computed: exact threshold λ* = 0.182711 (N4b); **kernel** for λ ≤ 1/40 | `fake_gaussian_nonneg` |
| Weil form = 2 log 5·‖g‖² on supp g ⊂ [-a,a], 2a < log 5 (passes Zhu's 0.8) | paper | paper (Poisson), plus numerics N7 (exact 2 log 5 inside the window, negative once the support passes log 5) | none |
| Li λ₁..λ₆₁ > 0, first negative at 62 | numerics | computed: correct in 0-based corpus indexing (rungs 0..61 ≥ 0, rung 62 < 0); in 1-based Li indexing λ₁..λ₆₂ > 0 and λ₆₃ < 0. The hybrid fails at the same index (N5, N6) | none |
| Box, no real zeros, dVP for the fake zeros | paper (exact checks) | **kernel** | `fake_box2`, `fake_dvp`, `hybrid_pointwiseLayer` |
| Envelope: F_ζ grows like log\|c\|, F_fake bounded | paper | paper; kernel only where F_fake ≥ 0 (λ ≤ 1/40); numerics N10 show the crossover centre grows fast (72 at λ = 0.3, 334 at 0.5, > 1387 at 1) | `XiHR_gaussian_envelope` |
| H₁₃,₋₈: Gaussian 0.47, window 1.28 | numerics | computed: λ* = 0.4711, window log(13)/2 = 1.2825, first height 1.2248 (N12). "Theta 1.77" was not checked (quantity unclear) | none |
| Barrier: P does not entail RH | paper | **kernel** for the pointwise and Gaussian layers (as relativizations); the Li-coefficient identification is paper | `pointwise_layer_does_not_imply_rh`, `gaussian_layer_barrier` |
| "Finite certification is finite, so the infinite-height wall must be crossed with R1/R2/R3" | barrier reading | **Non sequitur.** Finite certification (height ≥ 4.54) excludes every lattice fake (kernel). The barrier gives no information about positivity plus finite certificates | `local_zero_low_copy`, `hybrid_zero_in_certified_box` |
| "Turns 'every finite certificate is compatible with an off-line zero' into a theorem" | claim | **Refuted for lattice models**: the golden hybrid is incompatible with the corpus's certificates, and so is every local fake | same |
| DH negative control: DH is not a P-datum | paper | computed (N11: b(6) = 1 ≠ b(2)b(3) = -κ², Λ_DH(3) < 0) | none |

## What the barrier does and does not show

**What it shows.** Two kinds of corpus conclusions are satisfied by an explicit entire function
with an off-line zero, exactly as they are by ξ. The first is the pointwise zero-location layer
(boxes, dVP, no real zeros, the Li disk). The second is the proved positivity instruments: Li rungs
0..4, the Gaussian small-width theorem, and the Gaussian envelope at λ ≤ 1/40. The function's
Dirichlet series (H4) has a genuine Euler product, positive von Mangoldt weights and a simple pole
at 1, so the Davenport–Heilbronn control does not apply. It follows that no argument using only
those conclusions, as properties of a zero set, can prove RH. This answers the `enriched_bundle_flips`
objection from `wall_adversary/BarrierScopeXR.lean`: the enriched class, now with an Euler product,
positivity and a simple pole, still contains an off-line witness.

**What it does not show.**

1. **Anything about ζ.** Like the retracted FE-uniformity barrier, this is a relativization: it
   refutes a universal statement, and such a refutation is silent about each single member
   (`BarrierScopeXR.barrier_silent`). Its positive content is the list of separating properties
   below, each separation proved.
2. **That the corpus as a whole cannot prove RH.** The corpus contains three things that exclude
   the hybrid. (i) Finite certificates: its zero lies in the certified box. (ii) ζ's holomorphy in
   `Re s > ½` except at s = 1: by the pole shadow, every positive local fake needs a pole there.
   (iii) The exact Γ_ℝ completion. The sibling `Crux_axiso_theorem.lean` shows that the exact
   FE plus log-positivity collapses the class to {ζ}, modulo KP99. On top of that, the hybrid fails
   Ramanujan at 5 (`w4_even_ge`).
3. **A barrier against arguments that use finite certificates or the pole axiom.** Such a barrier
   would need a non-lattice, "global" Euler product, because no function of `p^{-s}` can avoid low
   zeros (`local_factor_periodic`). None is known. This is the sharpened form of the proposal's
   load-bearing "Beurling–FE problem":

   > **OPEN.** Is there an Euler product F with `Λ_F ≥ 0`, holomorphic in `Re s > ½` except for a
   > simple pole at 1, with an entire symmetric order-one completion whose factor has no zeros or
   > poles in the strip, all of whose zeros up to height 4.54 (or 4000) lie on the line, but which
   > has an off-line zero? Every local modification is excluded (kernel, genus one; the general
   > case follows from the same Pringsheim–Landau argument, paper). A YES would be a genuine
   > barrier. A NO for all such F would contain RH.

So the precise lesson is narrower than the proposal's. **The positivity instruments the corpus has
actually proved do not see the difference between ζ and a lattice fake.** Positivity still helps,
though: combined with ζ's analytic structure (the pole axiom) or with finite certification,
positivity is enough to exclude every lattice fake. A proof of RH must use more than positivity,
and it must use it at infinite height, where no lattice model lives.

## Relation to the sibling builds in this worktree

* `wall_barrier` / `wall_adversary/BarrierScopeXR.lean` retracted the FE-only barrier as "sound
  but empty", because `s(s-1)` already refutes that bundle. This build keeps the Euler product and
  every proved positivity instrument inside the class, and it maps exactly which extra inputs
  separate ζ.
* `research/axiso_theorem` (Class P = {ζ}) works with the EXACT degree-one FE plus log-positivity
  and gets rigidity: F = ζ, modulo KP99. The golden fake needs the arbitrary completion factor,
  which vanishes inside the strip for H4. Together the two results bracket the role of the FE.
  Their `step4_top_coeff` (log-positivity forbids zeros inside the disk of convergence) is the
  periodic-coefficient cousin of `pole_shadow` here.
* `research/axiso_construct`: its near-miss `F0 = ζ·P_{2,-3}` is an instance of
  `local_rh_of_positivity`.

## What remains

These are formalization tasks, not new mathematics:

1. Kernel-check the identification `hybridLi n = taylorCoeff XiH n`. The additivity of
   `taylorCoeff` over the product is routine. The fake's paired-sum formula would use the
   Euler sine product.
2. Push `fake_gaussian_nonneg` from λ ≤ 1/40 toward λ* = 0.1827. The same lattice argument works
   with sharper constants. Beyond λ*, the fake sum does go negative.
3. Kernel-check the hybrid envelope for λ > 1/40. That needs a quantitative log-growth lower bound
   on ζ's Gaussian sum, not just the corpus's `≥ 0`.
4. Kernel-check the Weil-window identity (Poisson summation for compactly supported tests at a
   complex shift).
5. Kernel-check the general pole shadow (any degree, via Pringsheim), and integrality of the place
   counts a_d for all d (toral dynamics).
6. Wire both files into their islands' `lakefile`s and axiom guards if the program wants them
   under CI. They are currently checked by single-file elaboration only.

The one genuinely mathematical open item is the boxed question in the section above.
