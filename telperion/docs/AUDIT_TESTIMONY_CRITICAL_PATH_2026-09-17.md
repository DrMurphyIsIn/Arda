# Blind read-back audit: RH critical-path draft nodes (2026-09-17)

Auditor: independent blind session (no author context). Sources read from `origin/main`:
`telperion/missions/rh/lean/Statements/{RH_corridor_bound,RH_rvm_unconditional,RHDefs}.lean`,
`telperion/missions/rh/nodes/{RH_corridor_bound,RH_rvm_unconditional}.toml`,
`telperion/docs/RH_ROUTES_ROADMAP_2026-09-16.md` (sections 2, 6; rows A3/A4/B5/D5/D6),
and, only after the verdicts below were formed, `telperion/docs/RH_CRITICAL_PATH_NODES_2026-09-17.md`.
No registry file was modified. Nothing was proved. `conjecture1_proved = False` is unaffected.

Elaboration evidence (not in the registry; done in the scratchpad against the built Mathlib
`de5ce8a9` at `leanprover/lean4:v4.34.0-rc1` from the `rh` mission's pinned manifest):

| file | result |
|---|---|
| `RHDefs.lean` (origin/main, with the new `RvMCount` block) | compiles, no errors |
| `RH_corridor_bound.lean` | elaborates; only `declaration uses sorry` |
| `RH_rvm_unconditional.lean` | elaborates; only `declaration uses sorry` |
| trivial-close probes (`simp`, `aesop`, hand-picked witness `T' = T`, `simp [zetaZeroCount]`) | none closes either statement; `zetaZeroCount T = 0` is NOT simp-reducible |

---

## Node 1: `RH_corridor_bound` -- verdict: CLEAN

### Statement as registered

```lean
theorem corridor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1),
      (∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) ∧
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        ‖logDeriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2
```

### Classical statement compared against

Davenport, *Multiplicative Number Theory* (3rd ed.), ch. 17, in the proof of the truncated
explicit formula for ψ(x): since the number of zeros with T ≤ γ ≤ T+1 is O(log T) (ch. 15),
one may choose T (in any unit interval) so that |T − γ| ≫ (log T)⁻¹ for every ordinate γ,
and then, for −1 ≤ σ ≤ 2,

    ζ'/ζ(σ + iT) ≪ log² T.

The input is ch. 15 eq. (for −1 ≤ σ ≤ 2, t not an ordinate):
ζ'/ζ(s) = Σ_{|t−γ|<1} 1/(s−ρ) + O(log t) (Titchmarsh Theorem 9.6(A) in the same range).
With O(log T) terms each of size ≤ (log T)/c, the sum is O(log² T). Same lemma in
Montgomery–Vaughan ch. 12 (Lemma 12.2 plus the good-ordinate choice in the proof of the
explicit formula) and Ingham ch. IV.

### Checks

1. **Exponent 2 is correct.** O(log T) zeros in the window, each contributing at most
   1/|s−ρ| ≤ 1/|T'−γ| ≪ log T. Not log T (that is the bound away from the strip), not
   log³ T (an over-loose variant).
2. **σ-range [−1, 2] is the classical one** (Davenport and Titchmarsh both use −1 ≤ σ ≤ 2;
   σ ≤ −1 is handled separately via the functional equation and is not part of this lemma).
   Re s = 1 is in the range; the pole is at s = 1 with Im = 0, and T' ≥ T ≥ 2, so the
   segment never meets the pole. Trivial zeros are real (Im = 0) and are likewise off the
   segment.
3. **Zero-free conjunct and Lean's junk values.** `logDeriv f = deriv f / f` (Mathlib
   `Mathlib/Analysis/Calculus/LogDeriv.lean:34`, `rfl`-unfolding to `deriv f x / f x`), so at a
   zero of ζ the value is 0 and the norm bound holds vacuously *at that point*. The explicit
   conjunct `riemannZeta (σ + iT') ≠ 0` on the whole segment removes this. Two remarks:
   - The conjunct is classically *redundant*: if ζ(β + iT') = 0 with β ∈ [−1,2], then for
     σ → β, σ ≠ β on the segment, ‖ζ'/ζ(σ+iT')‖ ~ m/|σ−β| → ∞, so the uniform bound already
     rules out zeros on the segment. Redundant is fine here: it makes the non-vacuity legible
     to a reader and hands consumers the nonvanishing directly. No edit.
   - `deriv riemannZeta` is the true derivative on the segment because ζ is differentiable
     at every s ≠ 1 (`differentiableAt_riemannZeta`), so `logDeriv` is not junk for the
     differentiability reason either.
4. **Trivial satisfiability.** Ruled out: (i) no T' with a pole on the segment (item 2);
   (ii) no T' with the zero-free conjunct AND ‖logDeriv‖ ≡ 0 on the segment, since that would
   force ζ' ≡ 0 on a segment, hence ζ constant; (iii) `T' = T` witness with `simp` fails
   (probe). The `0 < C` conjunct is harmless (any valid C may be enlarged).
5. **`Real.log T` vs `Real.log T'`.** Harmless: T ≤ T' ≤ T+1 and T ≥ 2 give
   log T ≤ log T' ≤ log T + log(3/2), absorbed by C. Using log T matches Davenport.
6. **Threshold T ≥ 2 is load-bearing.** At T = 1, `Real.log 1 = 0` and the bound would force
   `logDeriv = 0` on a whole segment, making the statement false. T ≥ 2 keeps
   `C * (log T)^2 > 0`. Any threshold T₀ > 1 works classically; 2 is fine.
7. **Well-formedness.** `open Complex` supplies `I`; `Set.Icc` binders elaborate to
   `T ≤ T' ∧ T' ≤ T+1` and `-1 ≤ σ → σ ≤ 2 → …` (seen in the probe goal state). Imports only
   `Mathlib`; consistent with the vocabulary file (uses none of it, correctly).
8. **Registry consistency.** TOML `kind = milestone`, `depends_on = [RH_rvm_unconditional]`.
   The lemma consumes only the window count N(T+1) − N(T) = O(log T), which is a corollary of
   the full RvM node, so the dependency is sound though stronger than necessary. Not a flag.

### TRIVIAL-flag risk: none identified.

### Recommended edits: none.

---

## Node 2: `RH_rvm_unconditional` -- verdict: CLEAN

### Statement as registered

```lean
theorem rvm_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |((RvMCount.zetaZeroCount T : ℕ) : ℝ)
          - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)|
        ≤ C * Real.log T
```

with, in `RHDefs.lean`,

```lean
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
    ((MeromorphicOn.divisor riemannZeta {s : ℂ | 0 < s.re ∧ s.re < 1} : ℂ → ℤ) ρ).toNat
```

### Classical statement compared against

Titchmarsh, *The Theory of the Riemann Zeta-Function*, Theorem 9.3:
N(T) = (T/2π) log(T/2π) − T/2π + O(log T); and Theorem 9.4 (Backlund's refinement):
N(T) = (T/2π) log(T/2π) − T/2π + 7/8 + S(T) + O(1/T) with S(T) = O(log T), where N(T) is the
number of zeros ρ = β + iγ of ζ with 0 < β < 1, 0 < γ ≤ T, counted with multiplicity.
Davenport ch. 15 gives the O(log T) form. The 7/8 comes from
N(T) = θ(T)/π + 1 + S(T) with θ(T) = (T/2) log(T/2π) − T/2 − π/8 + O(1/T):
(−π/8)/π + 1 = 7/8. Von Mangoldt 1905; Backlund 1918 (effective constants).

The registered O-form (|N(T) − main| ≤ C log T) is exactly Theorem 9.3 with the 7/8
carried explicitly. Carrying 7/8 in an O(log T) statement is mathematically inert (any
constant is absorbed), but it is the correct constant and is the shape consumers of the
effective follow-up will want, so no objection.

### Checks

1. **Right count: multiplicity, upper half, rectangle.**
   - `MeromorphicOn.divisor f U` (Mathlib `Mathlib/Analysis/Meromorphic/Divisor.lean:39`) is
     total: value `(meromorphicOrderAt f z).untop₀` if `MeromorphicOn f U ∧ z ∈ U`, else 0
     (`MeromorphicOn.divisor_apply` confirmed by `#check`). ζ is analytic on the open strip
     (1 ∉ U; `differentiableAt_riemannZeta`), so on U the divisor is the zero-order function:
     m ≥ 1 at a zero of multiplicity m, 0 elsewhere, never negative (no poles in U), never ⊤
     (ζ ≢ 0). `.toNat` is therefore the identity on the support. Multiplicity-weighted: yes.
   - Index set `0 < Re < 1, 0 < Im ≤ T`: the upper-half open-strip rectangle. Conjugate zeros
     (Im < 0) are excluded, so there is no factor-of-2 or ball-versus-rectangle miscount.
     Open strip versus closed strip is immaterial only because ζ ≠ 0 on Re = 1 (Mathlib
     `riemannZeta_ne_zero_of_one_le_re`) and hence on Re = 0; the statement does not rely on
     this, it simply uses the open strip like Titchmarsh.
   - `Im ≤ T` (closed) versus `Im < T`: differs by the multiplicity at height T, which is
     O(log T) and absorbed. Either convention is classical.
2. **`finsum` on possibly infinite support.** `∑ᶠ` returns 0 when the support is infinite.
   The support here is {zeros of ζ in the closed rectangle [0,1] × (0,T]}, which is finite
   (zeros of a non-identically-zero analytic function are isolated, hence finite in a compact
   set). That finiteness is a theorem, not an assumption, and it is *implicitly asserted by the
   statement*: if the count were junk 0 for some T ≥ 15, the statement would read
   |0 − main(T)| ≤ C log T with main(T) ~ (T/2π) log T, which is FALSE for large T. So the
   junk value makes the statement harder, not vacuous. Direction of risk is correct.
   Numeric confirmation (main(T)/log T): 6.3 at T = 100, 93.9 at T = 1000. Also, at
   T = 2π the main term is −1/8 (its minimum), harmless.
3. **Coercions.** `((zetaZeroCount T : ℕ) : ℝ)` is an explicit `Nat.cast` to ℝ; the
   subtraction and `|·|` are in ℝ. `π` is `Real.pi` via `open Real`. Confirmed by the
   elaborated goal state (probe output shows `↑(∑ᶠ …)`).
4. **7/8 constant.** Correct (derivation above).
5. **Threshold T ≥ 2.** Load-bearing: at T = 1, log T = 0 and the bound would force
   N(1) = main(1) = 0.4233 ≠ 0, so the statement is false at T = 1. For T ∈ [2, 14.13),
   N(T) = 0 and |main(T)| ≤ 0.2 ≤ C log 2 for C ≥ 0.3, so the small-T range is consistent.
   T ≥ 2 is the right threshold for an O(log T) remainder.
6. **Wrong-but-provable readings.** (i) "count = 0 satisfies the absolute value": no, see
   item 2. (ii) "divisor is 0 because `MeromorphicOn` fails": would make the count 0, hence
   the statement false, not provable. (iii) `simp [zetaZeroCount]` does not reduce the count
   to 0 (probe). (iv) No degenerate real-arithmetic identity: `Real.log (T/(2π))` is at a
   positive argument for T ≥ 2.
7. **Well-formedness.** Elaborates against the pinned Mathlib. The `(… : ℂ → ℤ)` ascription
   coerces `Function.locallyFinsuppWithin U ℤ` through its `FunLike` instance. Namespace
   `RvMCount` is new and does not collide with the island namespaces in `RHDefs`
   (`LiCriterion`, `ZeroFreeBridge`, `DiffractionCore`, `Backlund`). The RHDefs header says
   "every definition below is a VERBATIM copy" of island code; the `RvMCount` block is marked
   AUTHORED in its own comment, which is adequate, but see the note below.
8. **Registry consistency.** TOML `kind = milestone`, `depends_on = [RH_backlund_s_log]`
   (status `proved`; that node gives |S(T)| explicitly for T ≥ 4 under a zero-free-segment
   hypothesis). Discharging that hypothesis for every T and covering T ∈ [2, 4) and ordinate
   heights is the content of this node; the dependency is the right one. The "implies
   `MM_rvm_unbounded_mean_density`" claim in the header comment is plausible (superlinear
   count follows from N(T) ~ (T/2π) log T) but is a claim about a future proof, not about
   this statement; it does not affect the verdict.

### TRIVIAL-flag risk: none identified.

### Recommended edits: none required.

Optional, non-blocking: the `RHDefs.lean` module docstring (lines 4-5) still says every
definition is a verbatim island copy; the `RvMCount` block contradicts that one line. A
one-word amendment to the docstring ("every definition below except the AUTHORED
`RvMCount` block ...") would keep `build_rhdefs.py --verify-upstream` readers from
being surprised. This is documentation hygiene, not a statement defect.

---

## Cross-node remarks

- **Both nodes are the correct classical statements**, in O-form, at the standard thresholds,
  with the right count and the right exponents. Neither is provable by `rfl`, `simp`, `decide`,
  a degenerate witness, or a Lean junk-value quirk; in both cases the junk-value direction
  (logDeriv = 0 at zeros; finsum = 0 on infinite support) is either excluded by an explicit
  conjunct or makes the statement strictly harder.
- **Dependency chain** `corridor_bound → rvm_unconditional → backlund_s_log` is
  mathematically sound. The corridor node only needs the unit-window count, so a future
  refactor could insert a weaker `RH_window_count` node between them; not needed now.
- **Not registered, correctly:** the limit explicit formula (E8). Its statement depends on
  an unchosen test-function class; registering it now would be authoring a statement whose
  content is the choice itself.

## After reading the authoring note (`RH_CRITICAL_PATH_NODES_2026-09-17.md`)

Read after the verdicts above were fixed. It changes nothing. Its four design decisions
(rectangle not ball; multiplicity not distinct; explicit zero-free conjunct; no edge/winding
hypotheses) are exactly the properties I verified independently. One refinement of its
rationale: the note says the bare norm bound "would be vacuous on ordinates". Strictly, the
bare bound would still be non-vacuous, because uniformity in σ over [−1, 2] already excludes
zeros on the segment (item 3 of node 1). The explicit conjunct is nonetheless the right
authoring choice: it makes the non-vacuity visible without a side argument. Verdicts stand.

| node | verdict |
|---|---|
| `RH_corridor_bound` | CLEAN |
| `RH_rvm_unconditional` | CLEAN (optional docstring hygiene in RHDefs, non-blocking) |
