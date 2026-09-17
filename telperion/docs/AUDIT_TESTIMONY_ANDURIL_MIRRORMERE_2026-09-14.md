# Blind Read-Back Audit Testimony — 2026-09-14

Auditor: blind read-back of formal Lean text only. Source of vocabulary: `ANDDefs.lean`, `MMDefs.lean`. Provenance comment headers were read for context but their mathematical claims are NOT trusted; they are what is being checked.

---

## Vocabulary (authored definitions, unfolded)

**ANDDefs.lean**
- `DIntvProd.DIntv` — a dyadic interval record `{lo, hi, e : Int}`; `memR x I` means `lo·2^e ≤ x ≤ hi·2^e`. `isPos I := 0 < lo`, `isNeg I := hi < 0`, `sign? I` returns `some true` if strictly positive, `some false` if strictly negative, else `none`.
- `XiLineZeros.gLine (t : ℝ) : ℝ := (completedRiemannZeta (1/2 + t·I)).re` — the real part of the completed zeta on the critical line, as a function of height `t`.
- `ZetaReflection.sawBernoulli`, `emTailCoeff3`, `binetRem` — analytic helper functions (periodized Bernoulli, a cubic coefficient, digamma−log). Not referenced by the audited statements.
- `ZetaReflection.checkLine` — a Bool recursion over a list of dyadic intervals asserting consecutive sign alternation (each interval has a definite sign and adjacent signs differ). `BandData` wraps a `boxes` list; `BandData.check := checkLine boxes`. Not referenced by the audited statements.

**MMDefs.lean**
- `Quasicrystal.twoFreq c₁ c₂ lam₁ lam₂ x := c₁·exp(lam₁·x·I) + c₂·exp(lam₂·x·I)` — a two-term complex exponential sum.
- `Quasicrystal.hardyZ` — a polynomial-driven Hardy-type function; not referenced by the audited statements.
- `Quasicrystal.IsUniformlyDiscrete (S : Set ℝ) := ∃ δ > 0, ∀ x,y ∈ S, x≠y → δ ≤ |x−y|` — a uniform minimum gap between distinct points of `S`.
- `Quasicrystal.RvMUnboundedMeanDensity (S : Set ℝ) := ∀ r>0, ∃ finite F ⊆ S and reals a, L≥0 with F ⊆ [a, a+L] and r·L + 1 < |F|` — for every density rate `r` there is a bounded window containing more than `r·L+1` points of `S`.
- **`Quasicrystal.zetaOrdinates := {t : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = t}`** — AUTHORED. The set of imaginary parts of zeros of `riemannZeta` whose real part lies strictly in the open critical strip `(0,1)`.
- `Quasicrystal.torusOrbit N lam x := (j ↦ exp(lam j · x · I))`; `linearTorusForm N c z := ∑ⱼ c j · z j`; `expSum N c lam x := ∑ⱼ c j · exp(lam j · x · I)` — AUTHORED cut-and-project vocabulary.
- `RHLinalg.hermForm A x := Re(star x ⬝ (A ·ᵥ x))`; `PosDefOn A W := ∀ x∈W, x≠0 → 0 < hermForm A x`; `posIndex hA := #{i | 0 < eigenvalue i}` (count of positive eigenvalues of a Hermitian `A`).
- `DefectDictionary.defect hA := posIndex hA.neg` — the count of positive eigenvalues of `−A`, i.e. the number of NEGATIVE eigenvalues of `A`. `NegativeWitness hA p` bundles a subspace `W` with `PosDefOn (−A) W` and `finrank W = p`.
- `BraggDefect.Aon := 2`; `Aoff := exp(1/10)+exp(−1/10)`; `excess := Aoff − Aon`; `defectFunctional d := −(d²)`; `expLo`, `expHi` are explicit rational bounds bracketing `exp(1/10)`.

---

## AND_ladder_h280000.lean
TESTIMONY: For every complex `ρ`, if `riemannZeta ρ = 0` and `0 < ρ.im ≤ 280000`, then `ρ.re = 1/2`. This is exactly the Riemann Hypothesis restricted to zeros with imaginary part in `(0, 280000]`. The theorem body is `sorry` (unproven). Note the hypotheses do NOT restrict `ρ` to the critical strip — `ρ.re` is unconstrained on entry — so trivial zeros are excluded only via the height window and the `re = 1/2` conclusion; any real zero in that height band would be a counterexample, but zeta has none there, so the statement is (believed) mathematically true and just unproven.
FLAGS: none (statement is a genuine finite-height RH restriction; it is stated correctly, only unproven via `sorry`).

## AND_ladder_1e6.lean
TESTIMONY: Identical shape to the h280000 node with the height bound at `10^6`: for all `ρ`, `riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000 → ρ.re = 1/2`. RH restricted to `0 < Im ρ ≤ 10^6`. Body is `sorry`.
FLAGS: none.

## AND_ladder_1e9.lean
TESTIMONY: Same shape, height bound `10^9`: RH restricted to `0 < Im ρ ≤ 1000000000`. Body is `sorry`.
FLAGS: none.

## AND_ladder_1e13.lean
TESTIMONY: Same shape, height bound `10^13`: RH restricted to `0 < Im ρ ≤ 10000000000000`. Body is `sorry`.
FLAGS: none.

## MM_zeta_comb_membership.lean
TESTIMONY: The theorem is literally `zeta_comb_membership : RiemannHypothesis`, i.e. it asserts Mathlib's full Riemann Hypothesis with no hypotheses. Body is `sorry`. The comment concedes this is a placeholder standing in for the intended (abstract) Fourier-quasicrystal membership statement, and that per the program dictionary it is RH-equivalent.
FLAGS: none on well-formedness. Worth noting for the referee: the *file name and node title* ("zeta comb membership") do not match the *stated content* (bare `RiemannHypothesis`) — the statement is honest and RH-hard, but it is a stand-in, not the titled quasicrystal-membership property. Not a soundness flag; a naming/scope mismatch the header itself discloses.

## MM_rvm_unbounded_mean_density.lean
TESTIMONY: Asserts `RvMUnboundedMeanDensity zetaOrdinates`: for every `r > 0` there exist a finite set `F` of imaginary parts of critical-strip zeta zeros, reals `a` and `L ≥ 0`, with `F ⊆ [a, a+L]` and `r·L + 1 < |F|`. Informally: the ordinates of the nontrivial zeros do not have bounded mean density — arbitrarily many of them can be packed into a window relative to its length. Body is `sorry`. `zetaOrdinates` correctly captures ordinates of zeros with `0 < Re ρ < 1` (the open strip), so it includes ALL nontrivial zeros regardless of whether RH holds — this is the right unconditional set for this claim. The statement is (by known zero-counting `N(T) ~ (T/2π)log T`) mathematically true.
FLAGS: none. (The `zetaOrdinates` set matches its name: nontrivial-zero ordinates. It is not empty — Mathlib knows nontrivial zeros exist — so no vacuity.)

## MM_zeta_ordinates_not_uniformly_discrete.lean
TESTIMONY: Asserts `¬ IsUniformlyDiscrete zetaOrdinates`, i.e. there is NO `δ > 0` that lower-bounds the gap between all distinct nontrivial-zero ordinates. Equivalently, the ordinates have arbitrarily close distinct pairs (no uniform separation). Body is `sorry`. Again `zetaOrdinates` is the open-strip ordinate set, unconditionally containing all nontrivial zeros.
FLAGS: none on structure. CAUTION for the referee (not a defect in the statement): whether this is actually TRUE depends on the true distribution of zero gaps — known results have `N(T)~(T/2π)log T` giving average gap `→ 0`, which forces non-uniform-discreteness, so the statement is believed true. But note it is a *stronger-sounding negative* than the RvM node and follows from it; the two are consistent. No soundness flag.

## MM_bragg_defect_witness.lean
TESTIMONY: Under the hypothesis `hexp : expLo ≤ exp(1/10) ≤ expHi` (an Arb-style rational enclosure of `exp(1/10)`), the theorem asserts a conjunction: (1) `defectFunctional 0 = 0`, which unfolds to `−(0²) = 0` — trivially true by computation; and (2) two rational bounds sandwiching `defectFunctional excess = −(excess²)` where `excess = exp(1/10)+exp(−1/10) − 2`, i.e. an explicit lower and upper rational bound on `−(Aoff−2)²`. Body is `sorry`. I cannot verify the ~150-digit rational literals in the two-sided bound by hand and explicitly do not certify them; structurally the second conjunct is a numeric enclosure of `−(excess)²` that would be true iff those literals correctly bracket the value, which is plausible given `excess ≈ 0.01·(1 + …) ` is tiny and `−(excess²)` is a very small negative number (both literals are negative, consistent with `−(excess²) < 0`).
FLAGS: none on structure. NOTE: the 150-digit literals are unverifiable by inspection; correctness of conjunct (2) rests entirely on those constants, which I do not certify. Conjunct (1) is TRIVIAL (`rfl`-level). The hypothesis `hexp` is satisfiable (a true enclosure of `exp(1/10)` exists), so no vacuity.

## MM_offline_pairs_le_defect.lean
TESTIMONY: For any `RCLike` field `𝕜`, finite index type `n`, Hermitian matrix `A : Matrix n n 𝕜`, and natural `p`, if there is a `NegativeWitness hA p` — a subspace `W` of dimension exactly `p` on which `−A` is positive definite (i.e. `A` is negative definite on `W`) — then `p ≤ defect hA`, where `defect hA` is the number of negative eigenvalues of `A` (count of positive eigenvalues of `−A`). This is the standard fact that the dimension of any negative-definite subspace is at most the negative index of inertia. Body is `sorry`. Mathematically true (min–max / inertia).
FLAGS: none.

## MM_torus_section_dictionary.lean
TESTIMONY: For all `N`, coefficient vector `c : Fin N → ℂ`, frequency vector `lam : Fin N → ℝ`, and `x : ℂ`, the identity `expSum N c lam x = linearTorusForm N c (torusOrbit N lam x)`. Unfolding both sides: LHS `= ∑ⱼ c j · exp(lam j · x · I)`; RHS `= ∑ⱼ c j · (torusOrbit N lam x) j = ∑ⱼ c j · exp(lam j · x · I)`. The two sides are definitionally the SAME expression. Body is `sorry`.
FLAGS: **TRIVIAL** — this is definitionally an identity (`linearTorusForm N c (torusOrbit N lam x)` beta/delta-reduces to exactly `expSum N c lam x`); provable by `rfl`. Not false, but it carries no mathematical content — it is the definition of `expSum` re-expressed through `linearTorusForm ∘ torusOrbit`.

## MM_torus_section_n2_rigidity.lean
TESTIMONY: For nonzero complex `c₁, c₂` and distinct reals `lam₁ ≠ lam₂`, the biconditional: "for all `x : ℂ`, if `linearTorusForm 2 ![c₁,c₂] (torusOrbit 2 ![lam₁,lam₂] x) = 0` then `x.im = 0`" ⟺ `‖c₁‖ = ‖c₂‖`. The left side (via the dictionary identity) is the real-rootedness of the two-frequency section `c₁·exp(lam₁ x I) + c₂·exp(lam₂ x I)`: all its zeros are real. The claim: this two-term exponential sum has only real zeros iff the two coefficient magnitudes are equal. Body is `sorry`. The `![c₁,c₂]` / `![lam₁,lam₂]` are `Matrix.of ![…]` finite-vector literals; `linearTorusForm`/`torusOrbit` are the authored defs. Mathematically this is the standard two-frequency rigidity fact and is plausibly true.
FLAGS: none. (`![...]` notation requires `Matrix` scope, available via `import Mathlib`; elaboration expected fine.)

## MM_euler_factor_section_offline.lean
TESTIMONY: Asserts `¬ (∀ x : ℂ, twoFreq 1 (−(1/√2)) 0 (−log 2) x = 0 → x.im = 0)`. The function is `f(x) = 1·exp(0·x·I) + (−(1/√2))·exp((−log 2)·x·I) = 1 − (1/√2)·exp(−(log 2)·x·I)`. Solving `f(x)=0`: `exp(−(log 2)·x·I) = √2`. Writing `x = a + bi`, `−(log 2)·x·I = (log 2)b − (log 2)a·I`, so magnitude `exp((log 2)b) = √2 ⟹ b = 1/2`, and phase `−(log 2)a ∈ 2πℤ ⟹ a = −2πk/log 2`. Hence EVERY zero has `Im x = 1/2 ≠ 0` (e.g. `x = i/2` is a zero). Therefore the universal statement "all zeros are real" is FALSE, so its negation (what the theorem asserts) is TRUE. I verified numerically that `f(i/2) = 0` and `f(−2π/log2 + i/2) = 0`. Body is `sorry`.
FLAGS: none — the negated-universal is TRUE as written (I computed the zeros: all lie on `Im x = 1/2`, so real-rootedness genuinely fails). The header's algebra claim checks out.

---

## Summary

The four AND ladder nodes are all honest finite-height restrictions of RH (`0 < Im ρ ≤ H` for `H ∈ {280000, 10^6, 10^9, 10^13}`), correctly stated and left as `sorry` — none claims RH itself. `MM_zeta_comb_membership` is a bare `RiemannHypothesis` placeholder whose file/node name ("zeta comb membership") does not match its stated content, though the header discloses this and the statement is honestly RH-hard. The two `zetaOrdinates`-based nodes (RvM unbounded mean density, not-uniformly-discrete) use the authored set correctly — it is exactly the ordinates of open-strip zeta zeros, non-empty and RH-independent — and both are believed true unconditionally. `MM_bragg_defect_witness` is a conjunction of a trivial first conjunct and a 150-digit rational enclosure I cannot and do not certify. `MM_offline_pairs_le_defect` is a correctly-stated inertia inequality. For the two flagged authored torus nodes: `MM_torus_section_dictionary` is definitionally TRIVIAL (`rfl`), and `MM_euler_factor_section_offline`'s negated-universal is TRUE (I computed the zeros — all sit on `Im x = 1/2`). `MM_torus_section_n2_rigidity` is a well-stated rigidity biconditional.

### FLAGS raised
- `MM_torus_section_dictionary.lean` → **TRIVIAL** → `expSum` and `linearTorusForm ∘ torusOrbit` are the same expression by definition; provable by `rfl`, zero mathematical content.
- `MM_zeta_comb_membership.lean` → **naming/scope mismatch (not a soundness flag)** → node titled "zeta comb membership" but the stated theorem is bare `RiemannHypothesis`; disclosed in header, honestly RH-hard.
- `MM_bragg_defect_witness.lean` → **UNVERIFIABLE LITERALS (partial)** → first conjunct `defectFunctional 0 = 0` is TRIVIAL; second conjunct's correctness rests entirely on ~150-digit rational bounds I did not certify.

No `VACUOUS`, `SUSPICIOUS-SET`, `TYPE-ODDITY`, `LIKELY-FALSE`, or `ELABORATION-RISK` flags: `zetaOrdinates` matches its name and is non-empty; the `euler_factor` negated-universal is genuinely true; identifiers (`riemannZeta`, `completedRiemannZeta`, `RiemannHypothesis`, `![…]`, `RCLike`, `Matrix.IsHermitian`) are all Mathlib-standard under `import Mathlib`.
