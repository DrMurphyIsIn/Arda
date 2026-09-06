# Emitter designs: the complex-analysis gaps (2026-09-04)

Five emitter designs for the confirmed gaps. The real-algebraic positivity space is saturated
(71 emitters); these open the complex-analysis category that RH's zero-free-region program needs.
Each design gives: the certificate shape, the Python entry, the emitted Lean, what it REUSES, the
gate, and honest scope. `conjecture1_proved = False`.

Grounding checked against the tree: `residue_logDeriv` is PROVEN (`ZeroFreeBridge.lean:70`);
`emit_halfplane_disk` already ships the Borel–Carathéodory Möbius core; `emit_dominated_integrability`
ships `integrableOn_bounded_div_cpow`. So three of the five are largely ASSEMBLY/PACKAGING, not new
mathematics — the cheap wins. Two (`euler_maclaurin`, and the exact-factorization half of
`spectral_factorization`) carry genuine new content.

---

## 1. `emit_spectral_factorization` (a.k.a. `emit_fejer_riesz`) — cheap win

**Certificate shape.** Given a nonnegative trig polynomial `P(θ) = Σ_{k=0}^d a_k cos kθ ≥ 0`
(cosine tuple `a`, not necessarily all `a_k ≥ 0`), emit the exact Fejér–Riesz SOS on `x = cosθ`:
`p(x) := Σ a_k T_k(x) = A(x)² + (1 − x²)·B(x)² ≥ 0` on `[−1,1]`.

**What's new vs. what exists.** `emit_mt_cosine.fejer_riesz_sos(b)` already does `b → (A,B,p,a)` (the
EASY direction: a factorization is given). The new content is the SPECTRAL FACTORIZATION `a → b`:
find `Q(z)=Σ b_j z^j` with `|Q(e^{iθ})|² = P`. Algorithm: form the para-conjugate polynomial
`Σ a_{|k|} z^{d+k}` (k=−d..d), find its roots, keep one of each conjugate-reciprocal pair (those in
the closed unit disk), and read off `b`. Rationalize `b`; because `P=|Q|²` for ANY `b`, a rationalized
`b` yields an EXACT rational SOS for the nearby tuple `a' = autocorr(b')`.

**Python entry.**
```
spectral_factor(a, *, tol) -> b            # numeric roots -> b (raise if P not >= 0 on the circle)
emit_spectral_factorization_cert(name, a, *, target='nearby'|'exact') -> str
```
`target='nearby'` certifies the exact rational `a'` from a rationalized `b` (always succeeds, `a'≈a`).
`target='exact'` attempts an exact rational factorization (succeeds when the para-poly has rational /
quadratic-surd root structure); else raises and the caller falls back to `nearby` or `emit_rational_sos`.

**Emitted Lean.** Identical shape to `mt_cosine_deg4_nonneg`:
`theorem <name> (x:ℝ) (h1:-1≤x)(h2:x≤1): 0 ≤ <p> := by nlinarith [sq_nonneg <A>, mul_nonneg hsq (sq_nonneg <B>)]`.

**Reuse.** `fejer_riesz_sos` (the `b→SOS` half, verbatim). New code = the root-finding factorizer only.
**Gate.** None — buildable now. **Scope.** `target='exact'` is best-effort; document the fallback so a
non-factorable `a` never silently ships a wrong tuple. Test: round-trips `MT_DEG4`, the VP family, and a
random admissible `a`; guard-rejects a sign-indefinite tuple.

---

## 2. `emit_order_residue` — package the proven `residue_logDeriv`

**Certificate shape.** For a meromorphic `f` with `f(s) = (s − s₀)^m · g(s)`, `g(s₀) ≠ 0`, certify
`ord_{s₀}(f) = m` via the residue identity `lim_{s→s₀} (s − s₀)·(f'/f)(s) = m` (the general-order
`residue_logDeriv`).

**What's new.** Nothing to PROVE — `residue_logDeriv` is proven at `ZeroFreeBridge.lean:70`
(`(z−z₀)·logDeriv f z → order`). The emitter is the PACKAGING skill: given `(f, s₀, m)` and a witness
of `g(s₀) ≠ 0`, instantiate `residue_logDeriv` and emit the term — the reusable, upstreamable wrapper the
plan calls for.

**Python entry.**
```
emit_order_residue_cert(name, f_expr, s0, m, g_nonzero_proof) -> str
```
Emits `theorem <name> : Filter.Tendsto (fun s => (s - s₀) * logDeriv f s) (𝓝[≠] s₀) (𝓝 m) := residue_logDeriv <args>`
(and/or the `Meromorphic.order f s₀ = m` corollary once the order↔limit bridge is in place).

**Reuse.** `residue_logDeriv` (proven). New code = the sympy→Lean instantiation + the `g(s₀)≠0` plumbing.
**Gate.** None for the limit form; the `Meromorphic.order` corollary is gated on that Mathlib bridge lemma.
**Scope.** Complex-analysis certificate (not SOS). Upstreamable to Mathlib. Test: `f=(s−1)^{−1}` (ζ pole,
m=−1), `f=(s−s₀)²·unit` (m=2). Honest: this is a WRAPPER; the mathematical content lives in the proven
theorem it invokes.

---

## 3. `emit_borel_caratheodory` — assembly over the existing Möbius core

> **UPDATE 2026-09-05 — BC IS UPSTREAM.** Mathlib v4.32 now ships the full theorem (`Mathlib.Analysis.Complex.BorelCaratheodory`, `Complex.borelCaratheodory` + `_zero`, author M. Radziwill). Design #3 is therefore NOT a ~500-line build — `emit_borel_caratheodory` is a PACKAGING wrapper (built, tested; dogfood `bc_general_emitted`/`bc_zero_emitted` kernel-verified in EmittedShapes.lean). The gate the plan worried about is gone: the zero-free region assembly can cite Mathlib's BC directly.

**Certificate shape.** Value form: `f` analytic on `ball 0 R`, `|z| ≤ r < R` ⟹
`‖f(z) − f(0)‖ ≤ (2r/(R−r))·(A − Re f(0))`, `A = sup_{|w|=R} Re f(w)`. Plus the derivative form
`‖f'(z)‖ ≤ (2R/(R−|z|)²)(A − Re f(0))`.

**What's new / what's reused.** The hard island — the Möbius map `w = g/(2A−g)` sending `Re g ≤ A` into
the unit disk — is ALREADY the emitter `emit_halfplane_disk`, whose Positivstellensatz identity
`‖2A−g‖² − ‖g‖² = 4A(A − Re g)` is exactly BC2/BC3. So BC is ASSEMBLY:
BC1 (`A` exists: `IsCompact.exists_forall_ge`) → BC2/BC3 (`emit_halfplane_disk`) → BC4 (Schwarz:
`Complex.norm_le_norm_of_mapsTo_ball`) → BC5 (invert `g = 2Aw/(1+w)`) → BC6 (assemble) → BC7 (derivative
form via `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`).

**Python entry.**
```
emit_borel_caratheodory(name, *, form='value'|'deriv') -> str   # emits the assembled theorem
```

**Reuse.** `emit_halfplane_disk` (BC2/BC3); Mathlib `Analysis.Complex.Schwarz`, `…AbsMax`, `…Liouville`.
New code = the BC5 inversion island (constrained-SOS, ~1 lemma) + the BC1/BC4/BC6/BC7 assembly.
**Gate.** Two-step: the Lean BC theorem must LAND first (~500–800 lines, the plan's Phase 3), THEN the
emitter packages it for reuse. The emitter design here is the wrapper; the proof is the prerequisite.
**Scope.** The single missing Mathlib theorem for the classical zero-free region; highest durable value.
Upstreamable. Test: the region-critical instantiation (`f = log(ζ/pole)` on a disk near `σ=1`).

---

## 4. `emit_parametric_integral_analytic` — bundle the 7-hypothesis derivative-under-integral

**Certificate shape.** Certify `s ↦ ∫ F(s,x) dx` is analytic/`HasDerivAt` on a region, with the
differentiated integrand `∫ ∂_s F(s,x) dx`. Target: RH Phase 1's `integral_fract_analytic`
(`∫ {x}/x^{s+1}` analytic on `0 < Re s`).

**What's reused.** The dominating-integrability hypothesis is `emit_dominated_integrability`'s
`integrableOn_bounded_div_cpow` (`∫ B·x^{−σ−1} < ∞` for `σ > 0`). The emitter BUNDLES the seven
hypotheses of `hasDerivAt_integral_of_dominated_loc_of_lip`: (i) `AEStronglyMeasurable F(s,·)`,
(ii) `Integrable F(s₀,·)`, (iii) `AEStronglyMeasurable ∂_sF`, (iv) the a.e. `HasDerivAt` of `s↦F(s,x)`,
(v) the Lipschitz-in-`s` bound with an integrable Lipschitz constant (← `emit_dominated_integrability`),
(vi) integrability of the bound, (vii) the neighborhood.

**Python entry.**
```
emit_parametric_integral_analytic(name, F, dsF, dominator, region) -> str
```
Emits the assembled `HasDerivAt (fun s => ∫ F s x) (∫ dsF s x) s` (and the `DifferentiableOn`/
`AnalyticOnNhd` corollary), with each hypothesis discharged by the reusable brick or a supplied witness.

**Reuse.** `emit_dominated_integrability` (hyps v/vi); Mathlib `Calculus.ParametricIntegral`.
New code = the measurability + a.e.-HasDerivAt + Lipschitz plumbing (the "7-hypothesis grind").
**Gate.** None structurally, but it's the heaviest assembly. **Scope.** Reusable across analytic-
continuation arguments, not just ζ. Test: `integral_fract_analytic` (the RH Phase-1 target) end-to-end.

---

## 5. `emit_euler_maclaurin` — sharp truncated-ζ magnitude, the hardest

**Certificate shape.** Certify the sharp near-`σ=1` bound `|ζ(σ+it)| ≤ C·log|t|` (improving the crude
`≪|t|`), via the Euler–Maclaurin expansion `ζ(s) = Σ_{n<N} n^{−s} + N^{1−s}/(s−1) − ½N^{−s} + R`, with
`N ∼ |t|` and a CERTIFIED finite remainder `|R| ≤ (explicit)`.

**What's reused.** The finite-sum and tail-integral magnitude bricks already in the bridge
(`norm_riemannZeta_le_re`, `zeta_repr_integral_bound`, `norm_one_div_natAddOne_cpow`). The emitter
certifies the E-M REMAINDER bound (a finite sum bound + a `B₂/2·∫|f''|` tail via the existing rpow-
domination), then assembles the `log|t|` bound by taking `N = ⌈|t|⌉`.

**Python entry.**
```
emit_euler_maclaurin_bound(name, order=1, *, N_rule='ceil_abs_t') -> str
```
Emits `theorem <name> {σ t} (h : 1-δ ≤ σ) (ht : 2 ≤ |t|) : ‖riemannZeta (σ+it)‖ ≤ C*(1+Real.log |t|)`.

**Reuse.** the bridge magnitude bricks + `emit_dominated_integrability` (tail). New code = the E-M
remainder certificate (the genuine new content; the `Σ n^{−s}` head bound is elementary).
**Gate.** None structurally, but this is the deepest (real E-M machinery, `N∼|t|` bookkeeping);
~3–4× the other four. **Scope.** Only SHARPENS the region constant `c` — the region is already
formalizable with the crude `≪|t|`. Lowest priority by leverage, highest by effort.

---

## Sequencing & recommendation

| # | Emitter | New content | Gate | Effort | Value |
|---|---|---|---|---|---|
| 1 | `spectral_factorization` | root-find factorizer | none | S | reusable trig-SOS front-end |
| 2 | `order_residue` | wrapper only | none (limit form) | S | upstreamable, feeds Phase 4 |
| 3 | `borel_caratheodory` | BC5 island + assembly | **Lean BC must land first** | M (after gate) | the missing Mathlib theorem |
| 4 | `parametric_integral_analytic` | 7-hyp bundle | none | M | reusable analytic-continuation |
| 5 | `euler_maclaurin` | E-M remainder cert | none | L | sharpens `c` only |

**Build order:** 1 → 2 (both cheap, no gate, finish this session's thread + open the RH chain) →
4 (unblocks Phase 1) → 5 → 3-emitter (after the BC Lean theorem lands). The BC THEOREM itself (Phase 3)
is the true long pole and is proof work, not emitter work — its positivity islands (BC2/BC5) are the
only certificate-shaped parts and BC2 is already `emit_halfplane_disk`.
