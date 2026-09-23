# Audit testimony: RH_dbn_H0_zero_strip (rh campaign), blind auditor A2, 2026-09-22

```
node                     = RH_dbn_H0_zero_strip   (name RH.dbn_H0_zero_strip, kind lemma, status draft)
artifact                 = telperion/examples/dbn/lean/DBNStrip.lean :: dbn_H0_zero_strip
pass                     = true
axioms_clean             = true
statement_byte_identical = true
conjecture1_proved = False
```

I worked blind: no author notes, no author testimony, and no other auditor's testimony were read
before the verdict was fixed. I wrote nothing outside this file and my own probe file (which I
deleted at the end). I ran no git operations, made no registry edits, and did not run `lake build`.

## 1. My read-back of the registry statement (written before I opened the artifact)

The statement file `missions/rh/lean/Statements/RH_dbn_H0_zero_strip.lean` reads

    theorem dbn_H0_zero_strip :
        ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1

against the vocabulary in `Statements/RHDefs.lean` (DBN block):

- Φ(u) = Σ_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) · exp(−πn²e^{4u}), with n ranging over ℕ+ and u real.
- HIntegrand t z u = e^{tu²} · Φ(u) · cos(zu), taking complex values.
- H t z = ∫ over u in (0, ∞) of HIntegrand t z u. This is a Bochner integral, so it would be 0 by
  convention if the integrand were not integrable.

In words: **every complex zero z of the de Bruijn–Newman function H_0 satisfies (Im z)² ≤ 1, so
it lies in the closed horizontal strip |Im z| ≤ 1.** Classically H_0(z) = ξ(1/2 + iz/2)/8, and
Re s = 1/2 − Im z / 2, so the statement is the familiar fact that the zeros of ξ lie in the closed
critical strip 0 ≤ Re s ≤ 1. It is weaker than the strict open-strip fact. It says nothing about
where zeros lie inside the strip, so it is nowhere near RH. The Bochner convention is not a
problem here: DBNDefs proves `integrableOn_HIntegrand` for every t and z, so H 0 z really is the
integral and not a junk value.

## 2. Statement comparison and the hardened gate

- The theorem block in the artifact, with whitespace collapsed, is
  `theorem dbn_H0_zero_strip : ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1`. That string is equal to
  `V._normalized_statement(node, root)`. **Byte-identical modulo whitespace: yes.** The proof
  body is `:= DBN.H0_zero_strip`.
- `V.statement_matches(artifact_text, V._normalized_statement(node, root))` gives **True**.
- `V.artifact_incompleteness_markers` gives `[]` for DBNStrip.lean and `[]` for DBNDefs.lean.
  Those two files are the entire island part of the import closure: DBNStrip imports only DBNDefs,
  and DBNDefs imports only Mathlib and `Lc.LiCriterion.Basic`. I also scanned the pinned upstream
  `Lc/LiCriterion/Basic.lean` and got `[]`.
- Negative controls on the gate itself:
  - weakening the conclusion to `≤ 2` makes `statement_matches` return False;
  - appending a `:= by sorry` theorem makes the markers return `['sorry']`.
- Mirror check: the DBN definitions in RHDefs (thetaMoment, Φ, HIntegrand, H) are textually
  identical to DBNDefs lines 40-41, 211-214, 408-409 and 413 (diff is empty).
- `lake build --no-build` (through leanlock) reported "All targets up-to-date (8747 jobs)".
- `telperion.cli mission verify rh` reported `verify [rh]: OK`.
- `mission status` shows this node as `(lemma, draft)`, with `RH_dbn_debruijn_real_zeros`
  depending on it.

## 3. Axiom probe (my own)

`Probes/AuditProbe_RH_dbn_H0_zero_strip_A2.lean` imports DBNStrip and contains:

- `#print axioms dbn_H0_zero_strip`, which printed **[propext, Classical.choice, Quot.sound]**
  (exactly the required set);
- `theorem probe_type_eq : (type_of% dbn_H0_zero_strip) = (∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1) := rfl`,
  which elaborated;
- a transitive walk over every constant the proof uses, covering both types and values:
  - 55,354 constants in total;
  - modules outside core and Mathlib that contribute constants: **only [DBNStrip, DBNDefs]**;
  - no constant whose name contains `H0_eq_xi`, `H0EqXi`, `riemannXi`, `LiCriterion`,
    `RiemannHypothesis` or `sorryAx`;
  - the only names my filter caught were Mathlib's own `completedRiemannZeta` and
    `completedRiemannZeta.eq_1`, which come from Mathlib's definition of `riemannZeta` and its
    lemma `zeta_eq_tsum_one_div_nat_add_one_cpow`. Neither is an RH-strength input.
- `#print axioms` for `DBN.H_zero_eq_of_im_lt` and for `DBN.Φ_neg` also printed the clean
  triple.

## 4. Re-deriving the mathematics by hand

Throughout, s = 1/2 + iz/2, so Re s = 1/2 − Im z / 2, and Im z < −1 exactly when Re s > 1.

- **L1a (fold).** First, cos w = (e^{iw} + e^{−iw})/2; this is Mathlib's definition, and the
  proof uses it by `rfl`. Substituting u ↦ −u and using the evenness Φ(−u) = Φ(u) gives
  H_0(z) = ½ ∫_ℝ Φ(u) e^{izu} du.
  - Integrability on u ≥ 0: |Φ(u)| ≤ C e^{9u} exp(−(π/2)e^{4u}) and |e^{izu}| ≤ e^{|z|u}, and
    the double-exponential factor wins.
  - Integrability on u ≤ 0 follows by reflection to −z.
  - Evenness (`Φ_neg`) is a DBNDefs theorem. It is derived from Mathlib's
    `jacobiTheta₂_functional_equation`, differentiated twice. I re-checked it numerically:
    Φ(u) − Φ(−u) is about 1e-41 at u = 0.3, 1/7 and 0.05 with 40-digit arithmetic. **Correct.**
- **L1b (termwise Gamma).** With x = e^{4u}, ∫_ℝ e^{wu} exp(−c e^{4u}) du = ¼ c^{−w/4} Γ(w/4)
  for Re w > 0 and c > 0. Write E = exp(−πn²e^{4u}). The n-th term is
  a_n e^{izu} = 2π²n⁴ e^{(9+iz)u} E − 3πn² e^{(5+iz)u} E.
  - (9+iz)/4 = s/2 + 2 and (5+iz)/4 = s/2 + 1.
  - So the integral is ¼(πn²)^{−s/2}[2Γ(s/2+2) − 3Γ(s/2+1)].
  - The bracket is Γ(s/2)·(s/2)[2(s/2+1) − 3] = Γ(s/2)(s/2)(s−1).
  - Result: (1/8) s(s−1) π^{−s/2} Γ(s/2) n^{−s}. **Correct.** The step
    (πn²)^{−s/2} = π^{−s/2} n^{−s} is valid because both bases are positive reals.
- **L1c (Tonelli/Fubini).** |e^{izu}| = e^{−Im z · u}, so the n-th absolute integral is at most
  a constant times n⁴·n^{−(9−Im z)/2} + n²·n^{−(5−Im z)/2}, which is O(n^{(Im z − 1)/2}).
  - That series converges exactly when Im z < −1.
  - `hasSum_integral_of_summable_integral_norm` then swaps sum and integral.
  - Summing the n^{−s} terms gives ζ(s), since Re s > 1.
  - Result: H_0(z) = (1/16) s(s−1) π^{−s/2} Γ(s/2) ζ(s). This agrees with the classical
    normalisation H_0 = ξ/8 with ξ = ½ s(s−1)π^{−s/2}Γ(s/2)ζ(s). **Correct.**
- **L1d.** When Re s > 1, none of the factors vanish:
  - s ≠ 0 and s ≠ 1;
  - π^{−s/2} ≠ 0;
  - Γ(s/2) ≠ 0, since Re(s/2) > 0;
  - ζ(s) ≠ 0, by Mathlib's `riemannZeta_ne_zero_of_one_lt_re` (Euler product).

  So H_0 ≠ 0 whenever Im z < −1. By `H_neg` (cos is even, so H_0(−z) = H_0(z)), H_0 ≠ 0
  whenever Im z > 1 too. Therefore any zero has −1 ≤ Im z ≤ 1, and hence Im z² ≤ 1
  (`nlinarith`). **Correct.**

Nothing looked wrong. The Lean follows exactly the argument above, and the constant cone confirms
that it rests only on this argument.

## 5. Numerical check of the half-plane identity from the Lean definitions

I computed H_0 directly from the DBNDefs definitions: ∫_0^∞ Φ(u) cos(zu) du, with Φ taken as the
literal ℕ+ series, using mpmath quadrature at 30 digits. I compared it with
(1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s):

| z | Im z | H_0 by quadrature | right-hand side | abs. difference |
|---|---|---|---|---|
| −2i | −2 | 0.063591379840790494753 | 0.063591379840790494753 | 0 |
| 3 − 1.5i | −1.5 | 0.059685236920961376204 + 0.0031140779441424473041i | same | 4.6e-33 |
| −7.25 − 3i | −3 | 0.046749916843169827499 − 0.012226129297417468526i | same | 1.5e-32 |

The identity holds to working precision at three points with Im z < −1, where two were required.

**C2 is not used.** I checked this two ways:

- DBNStrip's import closure is {DBNDefs, Mathlib, Lc.LiCriterion.Basic}. It does not include
  DBNXi, DBNXiCos, DBNXiIBP, DBNGKernel, DBNXiRiemann, DBNRealZerosIff or
  DBNRealZerosIffFinal.
- The constant-cone walk found no C2 (`dbn_H0_eq_xi`) constant, no `H0EqXi` constant, and nothing
  from LiCriterion.

Nothing RH-strength appears either. The only zeta facts used are the Dirichlet-series identity and
the non-vanishing of ζ on Re s > 1.

## 6. Establishes / does not establish

**Establishes** (kernel-checked, axioms are exactly [propext, Classical.choice, Quot.sound], and
no `sorry`):

- every zero of H_0 lies in the closed strip |Im z| ≤ 1;
- as by-products:
  - the half-plane identity H_0(z) = (1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s) for Im z < −1;
  - H_0 is not identically zero (`H0_ne_zero`, witnessed at z = −2i).

All of this is proved without the representation theorem H_0 = ξ/8 (C2).

**Does not establish:**

- anything about zeros inside the strip, including that they are real;
- the open-strip refinement |Im z| < 1, which would need ζ ≠ 0 on Re s = 1;
- C2 (H_0 = ξ/8 everywhere);
- C4, or de Bruijn's t ≥ 1/2 theorem (C3), which only consumes this lemma;
- any bound on Λ;
- RH.

conjecture1_proved = False.

## Non-blocking issues noted

1. The node's `title` in `nodes/RH_dbn_H0_zero_strip.toml` still says "STATED ONLY, not proved
   (obligation L1, ~950 lines)". The artifact now proves it in about 500 lines, so the title is
   out of date. It is registry metadata and has no effect on correctness.
2. Mathlib's `riemannZeta` is the analytically continued function, and its Dirichlet-series lemma
   goes through `completedRiemannZeta` internally. So "no analytic continuation of zeta" is true
   of the argument (the identity is only ever used on Re s > 1), but not of the Mathlib
   definitions it depends on. This does not affect soundness or C2-freedom.
3. The artifact's docstring says it has one transitive functional-equation input: `Φ_neg` via
   the Jacobi theta functional equation. That is accurate, and the cone confirms it.

Verdict: **PASS**.
