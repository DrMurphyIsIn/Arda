# REFLECTION TRACK DESIGN — kernel-checked numeric enclosures for T5 bands

(Authored by the reflection-architect agent, PROGRAM ANDÚRIL Wave 0, 2026-09-12.
Operator-approved as part of PROGRAM_ANDURIL_2026-09-12.md. conjecture1_proved = False.)

## 0. Verified repo context the design rests on

- T5 trust surface (TuringBand.lean:49-66): a reflected band must discharge four
  hypothesis groups: (H1) hLine — chain of n exact on-line zeros of
  completedRiemannZeta; (H2) three edge non-vanishings of riemannZeta; (H3) hins
  zero confinement; (H4) five Set.Icc enclosures of argChangeVert/Horiz for
  riemannZeta and Gammaℝ. Everything downstream is already kernel.
- XiLineZeros.lean is the H1 template: rational gLine bounds → exact zeros via
  intermediate_value_Icc + gLine_continuous. Reflection's H1 job: produce those
  gLine bounds as kernel facts instead of hypotheses.
- argChangeVert f σ T0 T1 = (∫ logDeriv).re (DiffractionCore:949) IS the
  continuous argument change; for f with a holomorphic logarithm L on a
  neighborhood of the segment, argChangeVert = Im L(end) − Im L(start) by FTC.
  This ONE bridging lemma converts FOUR of the five edge quantities into point
  evaluations — no rigorous quadrature. Only the two horizontal ζ-edges need
  Backlund cell subdivision.
- riemannSiegelTheta is integral-defined (DlvpTheta:82) and
  theta_eq_argChangeVert_gammaR (DiffractionCore:1066) welds it to argChange. A
  Stirling/Binet evaluation of Im log Γℝ serves BOTH the Γ edges (H4) and θ for
  the A3 Riemann–Siegel era. One formalization, two consumers.
- Pinned Mathlib: bernoulli : ℕ → ℚ and Polynomial.bernoulli exist; NO
  Euler–Maclaurin theorem anywhere (ours to prove; upstreamable). AbelSummation
  exists (Re s > 1 base case). riemannZeta_ne_zero_of_one_le_re exists.
- The Re=2 ζ vertical edge has a convergent-series closed form
  (log ζ(2+it) = Σ_{p,k} p^{−k(2+it)}/k, geometric tail) — kernel-cheap; corpus
  has logDeriv_zeta_eq_neg_LSeries_vonMangoldt.

## 1. Foundation: in-house dyadic core (DIntv), NOT a girving/interval port

Rationale: (1) Lean 4 kernel special-cases GMP Nat/Int — dyadic
(mantissa : Int, exp : Int) makes every op a few big-int ops, while Rat pays a
GCD per op and girving/interval's Floating is UInt64 bit-twiddling engineered
for compiled speed, not kernel whnf; (2) v4.26→v4.32 port cost with no
owned-proof benefit for the kernel-decide era; (3) the evaluators need a tiny
op set (division-free, certificate-heavy design).

Core: `structure DIntv where lo hi : Int; e : Int` with mem
`(lo:ℝ)*2^e ≤ x ∧ x ≤ (hi:ℝ)*2^e`. Ops: add, sub, neg, abs, mul (4 corner
products, min/max), roundTo p (directed truncation — the width-control
primitive), scale2, ofInt, sign/containment predicates. No division, no GCD.

Transcendentals via VERIFY-NOT-COMPUTE (untrusted Arb pipeline supplies dyadic
candidates; the kernel checks algebraic certificates):
- 1/√n: check l ≥ 0 ∧ l²·n ≤ 2^{2p} ≤ h²·n — two Int muls.
- 1/n and reciprocals: l·n ≤ 2^p ≤ h·n.
- ln n: verify expLo(l) ≤ n ≤ expHi(h), expLo/expHi once-proven truncated
  Taylor with Lagrange remainder (vs Mathlib Real.exp bounds), argument
  reduction by halving-and-squaring (≤60 doublings).
- cos/sin: in-kernel Taylor after argument reduction mod 2π using a
  high-precision π enclosure (once-proven; Machin lemma if Mathlib's bits are
  insufficient). At height t the reduction of t·ln n costs ~log₂ t extra
  mantissa bits — linear, not a blocker.
- Bernoulli/factorial constants: rational literals with a once-proven finite
  lemma list (j ≤ ~12, norm_num/decide from Mathlib.NumberTheory.Bernoulli).

FALLBACK TRIGGER: A0 throughput < ~3·10⁴ interval-ops/s, OR A1 correctness
> 2× estimate at week 3 ⇒ timebox 1 agent-day to lake-build girving/interval
on v4.32; adopt ONLY for the flagged native island; DIntv stays for the kernel
island.

## 2. Stage A2 scope: what gets evaluated + theorem list

Targets: gLine sign boxes (ζ(1/2+it) by EM × Γℝ(1/2+it) by Stirling/Binet →
H1 via IVT); ζ(σ+iT) boxes for σ∈[−1,2] (interval-σ EM, K≥2, valid
Re s > 1−2K → H2, H4 horizontals via Backlund cells, H3 slivers);
argChangeVert ζ 2: closed form Im L differences (prime-power series → H4 edge
1); argChangeVert Γℝ (σ=−1,2): Im log Γℝ points via Stirling+Binet (shift
z←z+m) → H4 edges 4,5; argChangeHoriz ζ: ~20–40 Backlund cells over [−1,2].

Do NOT take Hardy-Z-via-θ in A2 (needs the same Stirling work plus an extra
bridge; Z/θ is the A3 representation).

Theorem list (H=hard, M=solid engineering, E=easy):
1. [H, 4–6 aw] em_zeta_enclosure: EM identity (base Re s>1 by Abel summation +
   induction on integration-by-parts with periodized Polynomial.bernoulli;
   extension to Re s>1−2K by the identity theorem / AnalyticOnNhd.eqOn) +
   explicit remainder bound. Absent from Mathlib — upstreamable.
2. [H, 3–4 aw] stirling_binet_gammaR: computable enclosure of log Γℝ(z)
   (continuous-branch Im) for Re z ≥ 1/4 via Stirling series + Binet remainder
   |μ_K(z)| ≤ |B_{2K}|/((2K−1)(2K)|z|^{2K−1} cos^{2K}(arg z/2)) + shift trick.
   Only K=4 instance needed first.
3. [M, 1–2 aw] argChangeVert_eq_im_log_sub: the FTC/branch bridge (+ both
   instantiations: Γℝ Stirling branch; ζ-at-2 Dirichlet branch).
4. [M, 1 aw] logZeta_series_re2: L(s) = Σ Λ(n)/log n · n^{−s}, L' = logDeriv ζ,
   geometric tail, Re s ≥ 3/2.
5. [M, 1–2 aw] backlund_cell: nonvanishing path in a closed 0-free region B
   with arg-spread < π ⇒ argument change within B's arg-spread interval.
6. [E–M, 1 aw] hins discharge: ZetaZeroConfinement +
   riemannZeta_ne_zero_of_one_le_re + FE reflection; slivers via the same cells.
7. [E, 0.5 aw] alternating_signs_chain: n+1 kernel-checked alternating gLine
   sign boxes ⇒ hLine verbatim (generalizes XiLineZeros' pattern).

EM AFFORDABILITY: M ~ t terms/eval, ~200–300 Int ops/term; a 40-height band at
height t needs ~110–160 evals ⇒ t=10³: ~4·10⁷ ops/band (~1 min at 10⁶ ops/s);
t=10⁴: ~7 min/band; t=10⁵: ~1 h/band. Kernel-decide EM era ends ≈ t=1–3·10⁴.
⇒ **CHARTER CAVEAT: A3 (RS) is on the critical path for the 10⁹ kernel-only
milestone** (RS main sum is √(t/2π) terms: a 10⁹-height band ≈ 10 kernel-min).

## 3. Stage A4: checkBand design

Reflected bands prove the CONCLUSION outright (no numeric hypotheses):
```
def ReflectedBand.Statement (d : BandData) : Prop :=
  ∀ ρ : ℂ, (q d.s0 ≤ ρ.re ∧ ρ.re ≤ q d.s1) → (dy d.T0 ≤ ρ.im ∧ ρ.im ≤ dy d.T1) →
    riemannZeta ρ = 0 → ρ.re = 1/2
def checkBand (d : BandData) : Bool := ...          -- pure, structural, Int-only
theorem checkBand_correct : checkBand d = true → Statement d
```
Per-band file: `def d := <Int literals>`; `theorem ok : checkBand d = true :=
rfl`; `theorem band := checkBand_correct d ok`; `theorem band_t5shape : <the
exact T5 conclusion Π-type> := by norm_num [Statement, q, dy] at band ⊢ ...` —
so the height chain consumes reflected and T5 bands interchangeably.

checkBand phases: (1) table validation (ln n, 1/√n, reciprocals, π) against
algebraic certificates; (2) sign-chain via EM×Stirling at n+1 points →
alternating_signs_chain → hLine; (3) edges: Im L differences + Backlund cell
loops (also yield hnzb/hnzt/hnzl and feed hins); (4) hpin as Int inequalities;
(5) apply turing_band_on_line with every hypothesis discharged.

Encoding rules: Int mantissas at fixed per-band exponents; NO Rat in checker
code; List folds + structural recursion ONLY (kernel unfolds WF-recursion
abysmally); no ByteArray in the kernel island; big-literal elaboration is a
first-class measured cost.

## 4. Stage A0: benchmark spike (build first)

Spike/DIntvMini.lean + Spike/Toy.lean: checkAlt (sign alternation of x²−2 at
1000 dyadic points, 128-bit mantissas), `theorem toy_ok : checkAlt pts = true
:= rfl`. Variants: rfl vs decide; identical checker over Rat; 100k-literal
trivial checker (elaboration cost). Measure with -Dprofiler=true; metric =
kernel interval-ops/s; #print axioms toy_ok. Thresholds: ≥3·10⁵ green;
3·10⁴–3·10⁵ proceed with fatter certificates + EM cap at t~3·10³; <3·10⁴
native-first re-plan. 0.5–1 aw.

## 5. Staging ladder (effort, kill criteria)

A0 0.5–1 aw (kill: <3·10⁴ ops/s ⇒ native-first re-plan).
A1 DIntv + correctness + Taylor kernels + certificate verifiers, 3–4 aw
   (kill: >2× at wk 3 ⇒ girving port assessment for native island only).
A2 theorems 1–7; end-state = fully reflected bands at t≈100 and 10³ consumed
   by the chain. 10–15 aw (kill-to-descope: EM base case stalls ⇒ on-line-only
   reflection — still a genuine trust shrink).
A3 RS era: θ via Stirling branch + theta_eq_argChangeVert_gammaR; RS main sum;
   MINIMAL-FIRST Gabcke C0-only |R| ≤ 0.053·t^{−3/4} (t ≥ 200). 12–20 aw; no
   prior art in any assistant (kill/pivot: 2 monthly reviews without the
   saddle/contour layer ⇒ explicit-constant AFE; then terminal EM-era-only).
A4 productionize: BandData emitter (Arb pipeline as untrusted candidate
   producer), sharded lake targets, Statement gate, per-shard guards,
   native_decide flagged sibling island. 2–3 aw.

Totals: reflected EM-era chain ~17–24 aw; through RS ~30–45 aw.

FILE LAYOUT: telperion/examples/zeta_reflection/lean/ requiring
zeta_zero_localization (zero_free_bridge require pattern): DIntvDef,
DIntvCorrect, TaylorKernels, CertVerify, StirlingBinet, EulerMaclaurinZeta,
LogBranches, BacklundCell, SignChain, CheckBand, CheckBandCorrect, Spike/,
per-band RBand_*.lean; native variant = sibling island sharing all above
CheckBand.

FIRST WEEK: (1) A0 spike + measurements + axiom check; (2) DIntvDef + add/mul
mem-soundness only; (3) argChangeVert_eq_im_log_sub STATEMENT elaboration
check against DiffractionCore; (4) decision memo re-basing the height caps.
