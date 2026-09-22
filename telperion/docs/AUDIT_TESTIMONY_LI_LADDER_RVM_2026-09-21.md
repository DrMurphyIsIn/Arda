The artifact is the Li ladder in the rvm island vocabulary (zeros on the line up to T buy 0 <= Re liLimit N for N <= 3 pi T / 2), the sharp low-height box by integration by parts, and rungs N = 1..5 with no hypothesis, carried to the closed forms archSide N + finiteSide N; finite inequalities and conditional implications; NOT a proof of anything about RH.

# Audit testimony: E6Bridge28 (rvm_bridge island)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-21.
Island: telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned fbdc36bb.
File: E6Bridge28.lean (978 lines, namespace RvMBridge28, 84 declarations, imports E6Bridge27).
Probes (mine): Probes/Audit28_Auditor_Axioms.lean, Probes/Audit28_Probes.lean. The author's
Probes/Audit28_Axioms.lean (86 lines) was read but not relied on. conjecture1_proved = False.

## 1. Verdict

PASS. One sentence: the regrouping of E6Bridge15's real-part sum over the involution
rho -> 1 - conj rho is done correctly without splitting on fixed points, Lemmas A and B and
Theorems C and D transfer verbatim from the li island with the factor-3 split honest, the sharp
sawtooth bound by integration by parts and Zeta0EqZeta at N = 1 give Boxes 1 and 2, and the
unpaired termwise certificates for N = 2..5 (rung 5 through the Box-2 parametrisation) are
correct polynomial identities, so the registry node RH_li_ladder_liLimit is proved with a
byte-identical statement and the five closed-form corollaries are unconditional.

Two docstring notes (section 8), not defects.

## 2. Kernel evidence (my runs)

Probes/Audit28_Auditor_Axioms.lean: 92/92 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(84 RvMBridge28 declarations, mechanically extracted, plus RvMBridge6.zeroMult_reflect,
Zeta23.zeta_reflect_zero, RvMBridge6.reflectEquiv, RvMBridge15.summable_liPaired,
RvMBridge15.liPaired_re, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial, RvMBridge27.liValue,
Zeta0EqZeta). Verbatim from Probes/Audit28_Probes.lean:

    'RvMBridge28.liLimit_re_nonneg_of_line_below' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RvMBridge28.archSide_add_finiteSide_five_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option):
only line 9, the docstring phrase "no `sorry`". Built .olean exists; E6Bridge28 is in the
lakefile defaultTargets and imported by AxiomGuardRvMBridge.lean:171. Only my probes were built.

## 3. Registry byte comparison

missions/rh/lean/Statements/RH_li_ladder_liLimit.lean (under `open Zeta23 RvMBridge15
RvMBridge15.BombieriLagarias`):

    theorem liLimit_re_nonneg_of_line_below (T : ℝ) (hT : 1 ≤ T)
        (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ)
        (hN : (N : ℝ) ≤ 3 * Real.pi * T / 2) : 0 ≤ (liLimit N).re := by sorry

E6Bridge28 line 481: byte-IDENTICAL (python comparison). Node toml: status draft,
closure_clean false, depends_on RH_li_zero_sums_converge, artifact E6Bridge28.lean.

## 4. Inputs re-read

- `Zeta23.reflect ρ = 1 - conj ρ` definitionally (my probe: `rfl` accepted);
  `zeta_reflect_zero : IsNontrivialZero ρ → IsNontrivialZero (reflect ρ)` (ZetaReflect.lean:278);
  `RvMBridge6.zeroMult_reflect`, `RvMBridge6.reflectEquiv : ℂ ≃ ℂ` with reflect both ways.
- E6Bridge15: `liKernel n ρ = 1 - (1 - 1/ρ)^n`, `liPaired n ρ = zeroMult ρ * Re(liKernel n ρ)`,
  `liLimit n = ∑' ρ : ℂ, liPaired n ρ`, `summable_liPaired`, `liPaired_re`,
  `norm_one_sub_inv_of_on_line (ρ.re = 1/2) (ρ ≠ 0) : ‖1 - 1/ρ‖ = 1`.
- `RvMBridge4.zeroMult_eq_zero_of_not_nontrivial`; `RvMBridge27.liValue N (0 < N) : liLimit N =
  archSide N + finiteSide N` (hypothesis-free, audited earlier today).
- `Zeta0EqZeta {N} (0 < N) (0 < Re s) (s ≠ 1) : riemannZeta0 N s = riemannZeta s` with
  `riemannZeta0 N s = Σ_{range(N+1)} 1/n^s + (-N^{1-s})/(1-s) + (-N^{-s})/2 + s ∫_{Ioi N} (⌊x⌋ + 1/2 - x)/x^{s+1}`.

## 5. Mathematics re-derived

(a) Pair identity (section B). 1 - 1/ρ = (ρ-1)/ρ = (wOf ρ)⁻¹ and 1 - 1/(1 - conj ρ) = conj(ρ/(ρ-1))
= conj(wOf ρ). So Re K_N(ρ) = 1 - Re(w^{-N}) = 1 - r^{-N} cos(Nθ) and Re K_N(1 - conj ρ) =
1 - Re(conj(w^N)) = 1 - r^N cos(Nθ); sum 2 - (r^N + r^{-N}) cos(Nθ) = 2 - 2cosh(N log r) cos(Nθ).
Checked; numerically 1.2e-38 relative on 2000 random (ρ, N).
(b) Lemma A (section C): g = sinh cos - cosh sin, g' = -2 sinh sin ≤ 0 on [0, π], g(0) = 0;
f = cosh cos, f' = g, f(0) = 1, so f ≤ 1 on [0, π/2]; then cos|b| ≤ cos|a| for |a| ≤ |b| ≤ π/2.
Same proof as the li island's. Checked.
(c) Lemma B (section D), for |Im ρ| ≥ 1: Re w = (β(β-1) + γ²)/|ρ-1|² > 0 since γ² ≥ 1 > β(1-β);
tan(arg w) = Im w/Re w = -γ/(β(β-1)+γ²); |arg w| = arctan(β/|γ|) + arctan((1-β)/|γ|) by the
addition formula (product < 1). Upper bound via arctan u ≤ u; lower bound via arctan u ≥ u/2 on
[0,1] (h(x) = arctan x - x/2 has h' = 1/(1+x²) - 1/2 ≥ 0 there; needs β/|γ| ≤ 1 and
(1-β)/|γ| ≤ 1, true for |γ| ≥ 1). |log r| ≤ 1/(2γ²) via log(P/Q) ≤ P/Q - 1 both ways with
|P - Q| = |2β - 1| < 1 and P, Q ≥ γ². So |log r| ≤ 1/(2γ²) ≤ 1/(2|γ|) ≤ |θ|. Checked. This is
the arctan route the li-island skeptic warned about, but here it is correctly restricted to
|γ| ≥ 1, where u ≤ 1 holds; the lower bound 1/(2|γ|) ≤ |θ| is what Theorem C uses.
(d) Theorem C (section E): N ≤ 3π|γ|/2 gives |Nθ| ≤ N/|γ| ≤ 3π/2 and |N log r| ≤ |Nθ|. Case
|Nθ| ≤ π/2: Lemma A. Case π/2 < |Nθ| ≤ 3π/2: cos ≤ 0 (`Real.cos_nonpos_of_pi_div_two_le_of_le`),
cosh > 0, product ≤ 0, term ≥ 2. Exhaustive. On-line: r = 1 (‖1 - 1/ρ‖ = 1 gives ‖w‖ = 1),
term 2(1 - cos) ≥ 0. Theorem D termwise: |Im ρ| ≤ T on line; else |Im ρ| > T ≥ 1 and
N ≤ 3πT/2 ≤ 3π|Im ρ|/2 (probe 4). Checked.
(e) The regrouping (section F). liRe N ρ = Re(liPaired N ρ) = m(ρ) Re K_N(ρ). HasSum (liRe N)
(Re liLimit N) from `Complex.hasSum_re` of the summable liPaired. Reindex by reflectEquiv
(`Equiv.hasSum_iff`), add: HasSum (liRe N ρ + liRe N (1 - conj ρ)) (2 Re liLimit N). Each
summand is m(ρ)(Re K_N(ρ) + Re K_N(1 - conj ρ)) using m(1 - conj ρ) = m(ρ); nonnegative for
nontrivial zeros by the pair lemma and zero otherwise (zeroMult = 0). So 2 Re liLimit N ≥ 0.
The involution's fixed points (on-line zeros, 1 - conj ρ = ρ; probe 2) are NOT split off: each
is counted twice in the doubled sum, which is exactly what the factor 2 absorbs. Correct; the
abstract pattern is re-proved in my probe 3. Checked.
(f) Rung 1 (section G): K_1(ρ) = 1/ρ, Re = β/|ρ|² ≥ 0 on the strip, unpaired; tsum of
nonnegatives. Checked.
(g) Sharp sawtooth bound (section H). On [m, m+1] with c = m + 1/2 and G(x) = (x-c)²/2 - 1/8
(G(m) = G(m+1) = 0, G ≤ 0 on the interval), integration by parts:
∫ (x - c) x^{-σ-1} = [G x^{-σ-1}] - ∫ G · (-σ-1) x^{-σ-2} = -∫ G (-σ-1) x^{-σ-2}, and the
integrand G·(-σ-1)x^{-σ-2} is (≤0)·(≤0) ≥ 0, so the integral is ≤ 0. {x} - 1/2 = x - c on
(m, m+1). Sum over m = 1..n by `sum_integral_adjacent_intervals`, pass to the limit by
`intervalIntegral_tendsto_integral_Ioi` (integrable since |{x} - 1/2| ≤ 1/2 and x^{-σ-1}
integrable). Then ∫ {x} x^{-σ-1} = ∫ ({x} - 1/2) x^{-σ-1} + (1/2)/σ ≤ 1/(2σ). Complex bound
by norm of integrand = {x} x^{-Re s - 1}. Checked. Same bound as the li island's midpoint
reflection, different proof; numerically I(σ) ≤ 1/(2σ) at σ = 0.1, 0.5, 0.9, 2 (earlier run).
(h) Zero constraint (section I). Zeta0EqZeta at N = 1: 0 = 1 + (-1)/(1-s) + (-1)/2 + s ∫ (⌊x⌋ + 1/2 - x)/x^{s+1},
and ⌊x⌋ + 1/2 - x = 1/2 - {x}, so the integral is (1/2)(1/s) - J' with J' = ∫ {x} x^{-(s+1)}.
Hence 0 = 1 + 1/(s-1) - 1/2 + 1/2 - s J', i.e. s J' = 1 + 1/(s-1) = s/(s-1), J' = 1/(s-1).
With |J'| ≤ 1/(2σ): 2σ ≤ |s - 1|, 4σ² ≤ (σ-1)² + t². Reflection through 1 - conj s (a
nontrivial zero by zeta_reflect_zero): 4(1-σ)² ≤ σ² + t². Adding: Box 2 and Box 1 (probe 5).
Checked. Same boxes as the li island, from a different representation.
(i) Unpaired rungs 2..5 (section J). 1 - 1/ρ = (A + iγ)/P with A = β² - β + γ², P = |ρ|².
Re K_N = 1 - Re(A + iγ)^N / P^N, so need Re(A + iγ)^N ≤ P^N.
- N = 2: A² - γ² ≤ P². With A ≥ 0 (from γ² ≥ 3/4 > β(1-β)) and P - A = β > 0:
  P² - A² + γ² = β(P + A) + γ² ≥ 0 (probe 7). Checked.
- N = 3: A³ - 3Aγ² ≤ P³: P³ - A³ = β(P² + PA + A²) ≥ 0 and 3Aγ² ≥ 0. Checked.
- N = 4: A⁴ - 6A²γ² + γ⁴ ≤ P⁴: P⁴ - A⁴ = β(P+A)(P²+A²) ≥ 0 and 6A²γ² - γ⁴ = γ²(6A² - γ²) ≥ 0
  using A ≥ γ² - 1/4 and γ² ≤ 6(γ² - 1/4)² for γ² ≥ 3/4 (roots of 6(x-1/4)² - x are 0.113 and
  0.554, so it holds for x ≥ 0.554; probe 6). Checked.
- N = 5: the file's identity P⁵ - Re(A+iγ)⁵ = Σ_{k=0}^{4} c_k(u) e^k with u = β - 1/2,
  e = γ² - 3u² - 3/4 ≥ 0 (Box 2). I re-expanded the left side in (u, e) by sympy: degree 4 in e
  and all five coefficient polynomials match the file's li5c0..li5c4 exactly. Minima on
  |u| ≤ 1/2: c0 = 0.2726 at u = -0.094, c1 = 4.39, c2 = 16.8, c3 = 24.5, c4 = 10. The
  nlinarith certificates were accepted by the kernel. Checked.
- Numerics (grid over the Box-2 region, γ up to 4.9): min of Re K_N is 0.043, 0.127, 0.253,
  0.368 for N = 2, 3, 4, 5 and -1.43 (N = 6, at β = 0.29, γ = 0.939), -3.72 (N = 7). Rungs 2, 3
  with only A ≥ 0: min 0.335 and 1.000. So N ≤ 5 is the honest reach, as the file says.
(j) Closed forms: archSide N + finiteSide N = liLimit N by RvMBridge27.liValue (N ≥ 1). I
recomputed archSide N + finiteSide N from the E6Bridge15 definitions and, independently, Li's
λ_N by a Cauchy integral of s^{N-1} log ξ(s) about s = 1:

    N=1: 0.02309570897   N=2: 0.09234573523   N=3: 0.2076389206   N=4: 0.3687904795   N=5: 0.5755427145

both routes agree to all printed digits and all five are positive.

## 6. Probes (Probes/Audit28_Probes.lean)

Expected successes, all elaborated: closed-form rung 5 re-composed (1); reflect = 1 - conj by
rfl and on-line fixed points (2); the regrouping pattern abstractly (3); Theorem D threshold
arithmetic (4); box algebra (5); the rung-4 auxiliary inequality (6); rung 2 unpaired (7);
consumption of the ladder node at N = 3, T = 1 (8). Expected failures:

    Probes/Audit28_Probes.lean:51:43: error: unsolved goals      -- Theorem D at T = 1/2
    Probes/Audit28_Probes.lean:56:68: error: unsolved goals      -- closed form at N = 0 (0 < N)
    Probes/Audit28_Probes.lean:60:46: error: (deterministic) timeout at `whnf`  -- rung-5 termwise lemma offered for rung 6

The third fails by a defeq timeout (Lean tries to unfold liKernel 6 against liKernel 5) rather
than a clean type mismatch; it fails either way and rung 6 is not obtainable this way.

## 7. Overclaim grep

E6Bridge28.lean: lines 42-44 "NOTHING here proves anything about RH: Theorem D consumes zero
localisation (a hypothesis, or the finite box) and produces sign information about finitely many
Li coefficients. conjecture1_proved = False." No other RH language. No memo under docs references
E6Bridge28 yet.

## 8. Notes (not defects)

- Header line 34 cites the rung-6 failure point "(0.24, 0.95)" (β, γ²): that point is inside
  Box 1 but marginally outside Box 2 ((0.24 - 1/2)² = 0.0676 > 0.95/3 - 1/4 = 0.0667). Rung 6
  does fail inside Box 2 (e.g. β = 0.29, γ = 0.939, Re K_6 = -1.43), so the claim stands; only
  the cited point is slightly off.
- The rungs here are UNPAIRED termwise (Re K_N(ρ) ≥ 0 for every zero), stronger than the li
  island's paired route and giving N = 1..5 versus rungs 0..4 there (same five coefficients).

## 9. What this does and does not establish

Established: (i) unconditionally, 0 ≤ Re(liLimit N) = Re(archSide N + finiteSide N) for
N = 1..5, and the two boxes; (ii) conditionally, 0 ≤ Re(liLimit N) for N ≤ 3πT/2 from zeros on
the line up to T ≥ 1. Nothing here evaluates the sign for all N, and that uniform statement is
RH. NOT a proof of anything about RH. conjecture1_proved = False.
