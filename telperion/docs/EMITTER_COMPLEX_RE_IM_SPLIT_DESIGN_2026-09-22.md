# `complex_re_im_split` -- emitter design (2026-09-22)

conjecture1_proved = False.  Nothing in this document, and nothing the emitter produces,
bears on RH: every theorem it emits is a finite polynomial identity between the components
of a complex expression and real polynomials (or the cast identity of a real-valued one),
the bookkeeping steps that the islands' analytic proofs consume.

**Module** `telperion/src/telperion/emit_complex_re_im_split.py` ·
**Emitter** `ComplexReImSplitEmitter` (kind `complex_re_im_split`) ·
**Dogfood** `telperion/examples/complex_re_im_split/generate.py` ->
`examples/rvm_bridge/lean/Probes/Dogfood_complex_re_im_split.lean` ·
**Adapter** `negctrl_adapters/adapter_complex_re_im_split.py` ·
**Stance** `CERTIFICATE_SENSITIVE` (`checked_in = emit_complex_re_im_split`) +
`NEG_CONTROL_ADAPTER` ·
**Tests** `tests/test_emit_complex_re_im_split.py`, `tests/test_negctrl_complex_re_im_split.py`.

## 1. Provenance

The 48-hour shapes audit (`docs/SHAPES_AUDIT_48H_2026-09-22.md`, section 2.1 merges and
rank 4 of section 2.2; build order section 7, sprint 1 item 2) merged four audit findings
into this one kind:

| Source | What it saw |
|---|---|
| B N3 (`SHAPES_AUDIT_B_WEIL_WALL_2026-09-22.md`) | "the smallest and most frequent shape in the cluster": `(p z).re = P_re`, `(p z).im = P_im`, `‖p z‖^2`, `‖exp (q z)‖ = exp (q z).re`, closed by `simp only [Complex.mul_re, ...]; ring`; eight-plus sites in `E6Bridge6..11` |
| B D7 | the cast face: "this complex expression is the cast of that real expression, so its `.re` is that real" (`push_cast; ring` then `Complex.ofReal_re`); six sites |
| C 2.10 (`SHAPES_AUDIT_C_B7_PARTIAL_FRACTION_2026-09-22.md`) | `E6Bridge16.lean:272-291`, the `(s i - c)^2` real/imaginary split, "COVERED (`identity`), BESPOKE (cast plumbing)" |
| D 2.2 (`SHAPES_AUDIT_D_LI_FACE_2026-09-22.md`) | `E6Bridge28.lean:755-807`, `Re (a + b i)^N` for `N = 2..5` by `simp; ring`, "BESPOKE (complex-real bookkeeping)" |

The work was started by an earlier session (worktree `wf_132b7269-642-3`, based on
`8b2b76009`) that died before committing.  Its polynomial face (the four split modes, the
certificate, the adapter, the tests, the E6Bridge7 / E6Bridge28 dogfood) was salvaged
verbatim; this session added the audit's CAST FACE with natural-number atoms (section 2),
re-derived every line number against the current island, and ran every kernel check in
section 9 on a private built copy of the island.

## 2. Statement family

Let `p` be a polynomial over `C` in

* an optional complex variable `z` (Lean binder `(z : C)`),
* real parameters `c_1, ..., c_k` (binder `(c_1 ... c_k : R)`, cast `(c_i : C)` inside `p`),
  some of which may be declared NATURAL-NUMBER atoms (`nat_params`: binder `(m : N)`,
  rendered `(m : C)` -- a `Nat.cast` -- on the complex side and `(m : R)` on the real side),
* the imaginary unit `Complex.I`, and rational constants (non-integers cast from `R`),

and let `P_re(x, y; c) + i P_im(x, y; c) = p(x + i y)`.  With `x`, `y` rendered as `z.re`,
`z.im`, the emitter states one of six faces:

| mode | statement | claim `P` must be ring-equal to | proof skeleton |
|---|---|---|---|
| `re` | `(p : C).re = P` | `P_re` | `simp only [<components>]` / `all_goals ring` |
| `im` | `(p : C).im = P` | `P_im` | same |
| `norm_sq` | `‖(p : C)‖ ^ 2 = P` | `P_re^2 + P_im^2` | `rw [Complex.sq_norm, Complex.normSq_apply]`, then the same |
| `norm_exp` | `‖Complex.exp (p : C)‖ = Real.exp (P)` | `P_re` | `have hre : (p : C).re = P := <re skeleton>`; `rw [Complex.norm_exp, hre]` |
| `cast` | `(p : C) = ((P : R) : C)` | `P_re` (and `P_im = 0`) | `push_cast` / `all_goals ring` |
| `cast_re` | `(p : C).re = P` | `P_re` (and `P_im = 0`) | `have hcast : (p : C) = ((P : R) : C) := <cast skeleton>`; `rw [hcast, Complex.ofReal_re]` |

The two cast modes are the B D7 face: `p` must be REAL-VALUED BY CONSTRUCTION -- no complex
variable and no `I` -- so the statement is the hand proofs' `hcast` identity (`cast`), or its
real part obtained exactly the way the hand proofs obtain it (`cast_re`, the audit's
"`push_cast; ring` then `Complex.ofReal_re`" verbatim).  Every B D7 site casts a natural
number (`(WeilExplicit.zeroMult ρ : C)`), which is why the natural-number atoms exist; in the
split modes those atoms project through `Complex.natCast_re` / `natCast_im` (the pair
`E6Bridge12.lean:122-126` rewrites with by hand).

When `p` has no complex variable (the Li-face instances `Re (a + b i)^N`, the cast face) the
statement is purely in the atoms.  The claim is the statement's right-hand side, rendered
from the supplied expression (sympy's automatic argument order, then a deterministic term and
factor order; never expanded or collected): the emitter CHECKS it, it does not rewrite it.  The binders list the atoms in declared order, consecutive atoms of one type
grouped (`(c lam : ℝ)`, `(m : ℕ) (u : ℝ)`), then `(z : ℂ)`.

After every theorem the emitter writes the statement-match gate
`example : ∀ <binders>, <statement> := <name>`, and, when the instance names a hand lemma
(`tie_to`, which must be a dotted Lean identifier), the tie gate
`example : ∀ <binders>, <statement> := <hand lemma>`: the kernel then certifies that the
regenerated statement IS the hand statement (a type mismatch is a compile error; section 9
shows a reordered claim tripping it).

## 3. Certificate and its re-verification

`complex_re_im_split_certificate(p, mode=..., claim=..., z=..., params=..., nat_params=...,
tie_to=...)` builds a frozen `ComplexReImSplitCert(p, z, params, re_sym, im_sym, mode, claim,
p_re, p_im, tie_to, nat_params)` and returns it with the number of checks passed.  Everything
is exact (sympy `Rational`, Python `Fraction`); nothing is sampled on floats.

1. **Polynomial contract** -- a tree walk admitting only `Add`, `Mul`, `Pow` with a positive
   integer exponent, `Symbol` in `{z} ∪ params`, `Rational`, `I`.  Natural-number atoms must
   be declared parameters with sympy assumptions `integer=True, nonnegative=True`, so the
   binder `(m : ℕ)` is what sympy splits.
2. **The split, three ways** -- `P_re, P_im := re, im` of `expand(p(x + i y))` with every
   symbol real; re-verified by (a) `expand(P_re + i P_im - p(x + i y)) == 0`, (b) sympy's
   second route `as_real_imag()`, (c) an INDEPENDENT exact evaluator
   (`eval_complex_exact`, complex arithmetic written out by hand over `Fraction` pairs on the
   tree) at three seeded rational points -- the dual-engine discipline of
   `HONESTY_PATTERNS.md` #1.
3. **Degree cap** -- total degree of the split at most `max_degree` (default 10).
4. **The claim** -- `expand(claim - target) == 0` for the mode's target, else REFUSED; for
   the cast face additionally `P_im == 0` exactly.
5. **Load-bearing** -- `nonvacuity.assert_certificate_sensitive`: the residual vanishes for
   the certificate and is broken by `claim + 1` and by `claim - x` (or `claim - c_1`), so
   the theorem cannot collapse into a tautology.

`certify_complex_re_im_split_point` reads the spec dict
`{"p", "mode", optional "claim"/"z"/"params"/"nat_params"/"re_sym"/"im_sym"/"tie_to"/
"max_degree"}` from `family.special[1](pt)`; `complex_re_im_split_family(name, grid,
lean_name, spec)` is the family helper.

## 4. Frozen tactic skeleton

```
theorem <nm> (<atoms> : R/N) (<z> : C) :
    <statement> := by
  simp only [<component lemmas>]          -- re / im
  all_goals ring

  rw [Complex.sq_norm, Complex.normSq_apply]   -- norm_sq, then the two lines above

  have hre : (p : C).re = P := by         -- norm_exp
    simp only [<component lemmas>]
    all_goals ring
  rw [Complex.norm_exp, hre]

  push_cast                               -- cast
  all_goals ring

  have hcast : (p : C) = ((P : R) : C) := by   -- cast_re
    push_cast
    all_goals ring
  rw [hcast, Complex.ofReal_re]
```

The canonical component set is the union of the hand proofs' sets
(`E6Bridge7.lean:78-120`, `E6Bridge28.lean:786-807`, `E6Bridge6.lean:408-421`, and the
natural-cast pair of `E6Bridge12.lean:122-126`):
`Complex.add_re/add_im, sub_re/sub_im, mul_re/mul_im, neg_re/neg_im, ofReal_re/ofReal_im,
natCast_re/natCast_im, I_re/I_im, re_ofNat/im_ofNat, one_re/one_im, zero_re/zero_im,
pow_succ, pow_zero, one_mul`.  Per instance `simp_set_for` restricts it, in canonical order,
to the lemmas `simp` will actually rewrite with, by simulating the projection propagation
through the rendered tree (`(u * v).re` needs `mul_re` and both projections of `u`, `v`; a
leading negation only its own projection; a literal power unfolds to a left-associated
product; the power unfolders are kept when a literal power occurs on either side).  This never
drops a lemma that can fire (89 kernel-compiled instances, section 9), and it keeps the emitted
file free of `linter.unusedSimpArgs` warnings.

Why `all_goals ring` and not `ring`: `simp only` (and `push_cast`) closes the goal outright
when the claim is syntactically what the rewriting produces (`(z + 1).re = z.re + 1`), and a
bare `ring` then fails with no goals -- the `rational_identity` emitter's `field_simp` footgun
of 2026-08-20, same remedy.  In exactly those cases Lean's unusedTactic linter notes that
`all_goals ring` does nothing: a warning, never an error (none in the dogfood or the twins).
No search tactic appears anywhere (`simp only` and `push_cast` are fixed rewrite sets, `ring`
is a decision procedure); the certificate fixes every symbol the proof mentions.

## 5. Refusals (the phantoms)

Every refusal raises `ValueError("complex_re_im_split REFUSED: <reason>")`; nothing is
widened, repaired or replaced silently.

| Refusal | Why it is a phantom |
|---|---|
| non-polynomial `p`: division (`1/z`, `(z - c)^(-1)`, `J / (2 pi)`), `exp`, `conjugate`, `re`/`im`, `Abs`, a symbolic or fractional exponent | B N3 phantom 1; the component lemmas do not apply and a declared-nonzero-denominator face is a documented follow-on, NOT applied silently |
| a supplied claim with `expand(claim - target) != 0` | B N3 phantom 2, THE FORGE CASE (`Re (a + b i)^2 = a^2 + b^2`; on the cast face `m u^2 = m u^2 + 1`) |
| the cast face on a `p` with a complex variable | `z` is not real: the cast identity would be false |
| the cast face on a `p` carrying `I` (even a real-valued one such as `(a + b i)(a - b i)`) | `push_cast; ring` treats `I` as an atom and cannot use `I^2 = -1`; such an expression is the re / im modes' business |
| a symbol of `p` that is neither `z`, a declared parameter nor `I` | the binder list would not bind it |
| a parameter not declared `real=True`; a complex variable declared real | the sympy split would not be what the binder `(c : R)` / `(z : C)` states |
| a natural-number atom that is not a declared parameter, not `integer=True, nonnegative=True` (a merely real, or a possibly negative integer, symbol), or listed twice | the binder `(m : N)` would not be what sympy splits |
| `p` written in `x`/`y`; a claim mentioning `z.re`/`z.im` without a complex variable; a claim with `I` or an undeclared symbol; a claim with non-polynomial structure | the statement would not type-check or would not be the split |
| a float literal anywhere | it would smuggle in a binary expansion |
| total degree above `max_degree` (10) | the `pow_succ`/`ring` skeleton is sized for the island degrees (5 today); raise it explicitly |
| a degenerate `p`: bare `z`, a bare constant, or a bare atom (`(c : C).re = c` IS `Complex.ofReal_re`; `(c : C) = ((c : R) : C)` is reflexive) | nothing to split; the reflexive class the nonvacuity lint refuses (the bare-atom case was found by the kernel stress run, section 9) |
| a `tie_to` that is not a dotted Lean identifier | it is rendered verbatim after `:=`, so it could otherwise smuggle a proof term into the tie gate |
| a binder named with a Lean keyword, `Complex` / `Real`, or `hre` / `hcast` | a keyword is not an identifier; under a binder `(Complex : ℝ)` the emitted `Complex.I` elaborates as field access on that real and fails (kernel-checked); `hre` / `hcast` are the proofs' own hypotheses |
| `re_sym`/`im_sym` clashing with a parameter or `z`; duplicate parameters; unknown mode | malformed instance |

## 6. Negative control and registry stance

`adapter_complex_re_im_split.py` hand-mints the FALSE certificate `Re ((a + b i)^2) = a^2 +
b^2` (true value `a^2 - b^2`, `E6Bridge28.re_pow_two`; at `a = 0, b = 1` it reads `-1 = 1`)
and the TRUE twin with the honest claim; both are plain `import Mathlib` statements.  Layer 1
refuses the forgery (`claim - target = 2 b^2`); Layer 2 is the kernel: after `simp only` the
goal is `a ^ 2 - b ^ 2 = a ^ 2 + b ^ 2`, which `ring` cannot close.  That is the REGISTERED
control (the B N3 forge case the audit names).  The adapter module also exports the cast
face's pair, `make_false_cast_cert` / `make_true_cast_cert` (`(m : C) * (u : C)^2 = (((m : R) *
u^2 + 1 : R) : C)` against the honest `hcast` of `E6Bridge5`), pinned offline by
`tests/test_negctrl_complex_re_im_split.py` and run through the kernel in section 9.

Registry: `CERTIFICATE_SENSITIVE` (the claimed polynomial is the statement's corruptible
right-hand side, exactly as `IdentityEmitter` / `RationalIdentityEmitter`), with
`assert_certificate_sensitive` wired (`checked_in`), and `NEG_CONTROL_ADAPTER`.

## 7. Dogfood

`examples/complex_re_im_split/generate.py` (`--check` is the drift gate; the test suite
regenerates it byte for byte) writes `examples/rvm_bridge/lean/Probes/Dogfood_complex_re_im_split.lean`:
a banner, the frozen emitter output (15 theorems, each with its statement-match gate), the
hand-written gates, and a `#print axioms` line per emitted theorem.  It imports the five
modules it regenerates from (`E6Bridge5`, `E6Bridge7`, `E6Bridge11`, `E6Bridge14`,
`E6Bridge28`) and modifies none of them.  It is the island lean_lib `DogfoodComplexReImSplit`,
so the island's `lake build` (the CI job `rvm-bridge-compiles`) compiles it and the island
AxiomGuard prints its axioms.  Line numbers are the CURRENT island's (E6Bridge7
moved by +2 since the audit when it began importing `RvMBridgeGauss`; E6Bridge7's cast site
and E6Bridge11's moved with the prelude hoist).

| emitted theorem | hand site | mode | gate against the hand content |
|---|---|---|---|
| `e6b7_hre` | `E6Bridge7.lean:78-82` (`norm_gaussTest`, `hre`; also `hEre` at `:113-116`) | `re` | consumer gates 1 and 2 |
| `e6b7_hsq` | `E6Bridge7.lean:83-86` (`hsq`) | `norm_sq` | consumer gate 1 |
| `e6b7_hexp` | `E6Bridge7.lean:88` (the `Complex.norm_exp` step of `norm_gaussTest`) | `norm_exp` | consumer gate 1 |
| `e6b7_hw2re`, `e6b7_hw2im` | `E6Bridge7.lean:105-112` (`re_gaussTest`) | `re`, `im` | consumer gate 2 |
| `e6b7_heim` | `E6Bridge7.lean:117-120` (`hEim`) | `im` | consumer gate 2 |
| `e6b28_re_pow_two..five` | `E6Bridge28.lean:786-807` | `re` | tie gates `:= RvMBridge28.re_pow_two..five` |
| `e6b5_hcast` | `E6Bridge5.lean:110-114` (`term_re_nonneg`, `have hcast`) | `cast` | instantiation gate |
| `e6b7_pair_hcast` | `E6Bridge7.lean:491-494` (`re_zeroSide_le`, the inner `have`) | `cast` | instantiation gate |
| `e6b7_pair_hre` | `E6Bridge7.lean:489-495` (`re_zeroSide_le`, `have hre`) | `cast_re` | instantiation gate |
| `e6b11_arch_hcast` | `E6Bridge11.lean:940-941` and `:1336-1337` (the first `show` of `re_archSide_ge` and of `re_weilForm_gauss_nonneg_of_large_c`) | `cast` | instantiation gate (one statement, two sites) |
| `e6b14_centre_hcast` | `E6Bridge14.lean:155-161` (`re_term_centre`) | `cast` | instantiation gate |

The E6Bridge28 statements render byte-identically to the hand lemmas (modulo `Complex.I` for
`I` under the island's `open Complex` and the outer `( : C)` ascription), which is what makes
the tie gates meaningful (`test_li_face_statements_are_byte_identical_to_the_hand_lemmas`).

### 7.1 Consumer gates (the E6Bridge7 split sites)

A local `have` has no name to tie to, so the probe ties the CONSUMERS instead.  The footer
(`CONSUMER_GATES` in `generate.py`: hand-written, frozen there, explicitly NOT emitter output,
covered by the same byte-for-byte drift gate) does two things per hand lemma:

1. **statement pin** -- `example : <restated goal> := RvMBridge7.norm_gaussTest` and the same
   for `re_gaussTest`.  If the restated goal were not the hand lemma's statement this is a
   type error, so the kernel certifies that the probe is talking about the hand lemma;
2. **re-proof** -- the same goal proved from the emitted theorems ALONE:
   `norm_gaussTest` from `e6b7_hsq` + `e6b7_hexp`, `re_gaussTest` from `e6b7_hw2re`,
   `e6b7_hw2im`, `e6b7_hre`, `e6b7_heim`.

The residual glue is declared, small and search-free, and it is the honest price of the
sympy round trip: `neg_mul` (sympy flattens `-(2 lam) * w` and `-(2 lam w)` into the same
`Mul`, so the emitted statement can only ever carry the second grouping) and three `ring`
reshapings (`-(x - c)^2 + y^2` versus `y^2 - (x - c)^2`, `4 y lam (x - c)` versus `4 lam (x -
c) y`).  That is why these rows carry no tie gate and cannot: byte-identity with those
`have`s is unreachable through sympy, and this design does not pretend otherwise.

### 7.2 Instantiation gates (the B D7 cast sites)

The cast sites are local `have`s too, but here no glue is needed.  Each gate restates the hand
`have` VERBATIM (whitespace aside; `test_cast_site_gates_restate_the_island_verbatim` pins the
text against the island source, including that E6Bridge11 writes its `show` twice) and closes
it with the emitted theorem applied to the island's atoms, e.g.

```lean
example (g : ℝ → ℂ) (ρ : ℂ) :
    (WeilExplicit.zeroMult ρ : ℂ) * ((‖paperFT g ρ.im‖ : ℂ)) ^ 2
        = (((WeilExplicit.zeroMult ρ : ℝ) * ‖paperFT g ρ.im‖ ^ 2 : ℝ) : ℂ) :=
  e6b5_hcast (WeilExplicit.zeroMult ρ) ‖paperFT g ρ.im‖
```

so the kernel confirms the hand statement IS an instance of the emitted one (the reals do not
unfold, so this is a syntactic match up to instances, not a hidden computation; section 9 shows
a factor-order swap tripping it).

### 7.3 The audit's other cited sites: reached, and NOT reached

REACHED by the family but not in the probe (each certified and rendered by
`_audit_reached_cases` / `test_audit_cited_instances_outside_the_probe_are_covered`; the
emitted Lean for all fourteen elaborates against Mathlib alone, section 9).  The audits'
line numbers predate the prelude hoist (`RvMBridgeGauss`, `RvMBridgeXi`), so the current
position is given too:

| audit site (now) | instance | note |
|---|---|---|
| `E6Bridge6.lean:408-421` (`:411`) | `hre` under `set x y`; its `hsq` is the probe's `e6b7_hsq` verbatim | the same shapes as the E6Bridge7 rows |
| `E6Bridge8.lean:84-85` (now `RvMBridgeGauss.lean:111`) | `(-b x^2 + c x).re = -b x^2 + c.re x` | the COMPLEX atom `c` is the split variable; `b`, `x` are the real parameters |
| `E6Bridge8.lean:308-311` (`:193`) | `(I z u).re = -(z.im u)` | |
| `E6Bridge8.lean:409-410` (`:294`) | `(-B u^2 - I c u).re = -B u^2` | `B` is a bound real parameter STANDING FOR the atom `gaussB lam`; the consumer instantiates it |
| `E6Bridge10.lean:430-431` (`:419`) | `((s - 1/2) u).re = (s.re - 1/2) u` | |
| `E6Bridge11.lean:396` (`:397`) | `(-(I c u)).re = 0` | the `= 0` face is a first-class claim |
| `E6Bridge11.lean:533` (`:534`) | `((k) (u)).re = k u` | |
| `E6Bridge11.lean:649-652` (`:671-673`; also `RvMBridgeGauss.lean:218-220`, `E6Bridge16.lean:112-114`) | `(-(a) x^2).re = -a x^2`, `(I w x).re = 0`, and the complex-frequency twin `(I w x).re = -(w.im x)` | |
| `E6Bridge11.lean:762-765` (`:789`) | `(1/4 + (r/2) I).re = 1/4` | a rational coefficient on `I` |
| `E6Bridge12.lean:122-126` (`:125-126`) | `((m : C) * w).re = (m : R) * w.re` | `re` mode with a natural-number atom and the complex variable `w` standing for the `gaussTest` value; the emitted statement carries sympy's canonical factor order (`w * (m : ℂ)`), so it is not a literal instance of the hand's rewrite chain, which stays |
| `E6Bridge16.lean:282-290` (`:191`) | the PURE split `((s i - c)^2).re = c^2 - s^2` and its `im` face | see the next list for the hand lemma as written |

NOT REACHED (the honest counter-list; each refusal is pinned by
`test_audit_cited_instances_the_family_does_NOT_reach`):

* `E6Bridge6.lean:408-421` `hnormSq` -- `Complex.normSq z = (x + c)^2 + y^2` is the `normSq`
  face, which is not a mode (`norm_sq` states `‖p‖ ^ 2 = ...`), and its expression is the
  bare variable, refused as degenerate.
* `E6Bridge6.lean:382-392` `gaussTest_axis` -- a COMPLEX-valued cast identity carrying
  `Complex.exp` (`gaussTest c lam (c + y i) = ((real) : C)`); a transcendental `p` is refused.
* `E6Bridge16.lean:282-290` (now `:191`) `hre` AS WRITTEN -- the hand lemma substitutes the hypothesis
  `hsq : s^2 = 1/4` into the split, so its right-hand side is `-(2 lam)(c^2 - 1/4)`, not the
  split `-(2 lam)(c^2 - s^2)`.  REFUSED (`claim - target = -2 lam s^2 + lam/2`): a hypothesis
  may not be laundered into an identity.  The pure split is reached, and a consumer rewrites
  with `hsq` afterwards exactly as the hand proof does.
* `E6Bridge11.lean:942` / `:1338-1339`, the SECOND `show` of the same two `archSide` sites,
  `(1 / (2 * (π : C))) * (J : C) = (((1 / (2 π)) * J : R) : C)` -- it divides by the real atom
  `π`; no division face, refused.
* `E6Bridge28.lean:755-774`, `one_sub_inv_eq_div_normSq` and `liKernel_re_eq` -- a division by
  `ρ` and by `normSq ρ ^ N` with a SYMBOLIC exponent `N`; both refused.  (The four
  `re_pow_N` lemmas that follow them are the tied rows above.)

## 8. What it does NOT do

* No division: a rational `p` is refused; the declared-nonzero-denominator face the audit's
  refusal wording anticipates ("non-polynomial `p` without a declared nonzero-denominator
  hypothesis") is NOT implemented, and no cited site in the probe needs it (the two that
  divide are listed in 7.3).
* No symbolic exponents, no `conjugate`, no `normSq` of a product, no statements over `K`
  other than `C`, no trigonometric or exponential components (`Complex.exp_re`, `cos_arg`):
  the `re_gaussTest` assembly consumes the emitted splits by hand (consumer gate 2).
* The cast face does not accept `I` or a complex variable, even where the expression happens
  to be real-valued; those go through `re` + `im`.
* No control over factor order: sympy's `Mul` is commutative and canonically sorted, so the
  rendering follows a fixed order (complex variable first, then atoms in declared order).  Where
  a hand statement uses another order (E6Bridge7's split `have`s, E6Bridge12's chain) the
  consumer pays `ring` reshapings, declared as such.
* It does not produce deep facts.  In the sense of `HONESTY_PATTERNS.md` #11 every emitted
  identity is tier 1 to 2: `simp` with the component lemmas and `ring` close it, which is
  exactly why the hand proofs were seventeen copies of one skeleton.  The value is mechanical:
  the claimed polynomial is certified (three routes, exact) before Lean sees it, the forge
  case and the phantoms are refused with reasons, and the gates tie the output to the hand
  content it replaces.
* Nothing about zeta, its zeros, Weil positivity or Li coefficients: it is a polynomial
  bookkeeping emitter.  conjecture1_proved = False.

## 9. Verification status (2026-09-22, this worktree's private built rvm island, toolchain `v4.33.0-rc2`)

Every Lean command below ran under the machine-wide build-slot wrapper; `lake build --no-build`
reported the island up to date (8883 jobs) before any of them.

* **Offline**: `PYTHONPATH=src python3 -m pytest -q tests/test_emit_complex_re_im_split.py
  tests/test_negctrl_complex_re_im_split.py tests/test_negative_control.py
  tests/test_certificate_sensitivity.py` -- 65 passed, 41 skipped (the skips are the
  kernel-gated harness tests, which need a built `examples/log_combination/lean`); the registry
  consistency tests (`test_emitter_registry.py`, `test_negctrl_adapter_exports.py`,
  `test_hardening2.py`) -- 233 passed, 62 skipped; the whole suite minus the four modules that
  run `lake exe cache get` / `lake build` unguarded (`tests/rh_jensen`, `test_dvp_box.py`,
  `test_rhinbox.py`, `test_zeroloc_end_to_end.py`) -- 2651 passed, 121 skipped;
  `generate.py --check` OK, and the sibling drift checks (`examples/rvm_bridge/generate.py
  --check`, `dogfood_exp_threshold.py --check`) still pass.
* **Dogfood**: `lake env lean Probes/Dogfood_complex_re_im_split.lean` exits 0 with no errors
  and no warnings; all fifteen emitted theorems print `[propext, Classical.choice, Quot.sound]`;
  the four tie gates, two statement pins, two consumer re-proofs and five instantiation gates
  type-check.  So `RvMBridge7.norm_gaussTest` and `RvMBridge7.re_gaussTest` are DERIVABLE
  from the emitted splits plus the declared glue, and the five B D7 hand `have`s are instances
  of the emitted cast theorems.
* **Island build and guard**: the probe is registered as the lean_lib
  `DogfoodComplexReImSplit` (root `Probes.Dogfood_complex_re_im_split`, in `defaultTargets`)
  and `AxiomGuardRvMBridge.lean` imports it and prints its fifteen theorems.  `lake build`:
  `Build completed successfully (8885 jobs)`, nothing but the probe and the guard rebuilt (no
  Mathlib compile).  The CI guard step replayed locally (`lake env lean AxiomGuardRvMBridge.lean`):
  exit 0, 839 axiom lines (CI floor 45), no `sorryAx`, every group exactly
  `[propext, Classical.choice, Quot.sound]`.  (The `exp_threshold` probe is NOT registered this
  way; this lane followed the lane rule that delivered Lean is built and guarded.  Dropping the
  lakefile / guard hunks returns to the probe-only convention without touching anything else.)
* **Gate positive control** (HONESTY_PATTERNS #9): the probe plus two perturbed gates -- the
  E6Bridge5 hand statement with its real factors swapped, and `re_pow_two`'s claim reordered
  to `-(b ^ 2) + a ^ 2` (both ring-equal, neither the stated term) -- fails with `Type
  mismatch` at exactly those two gates; the fifteen theorems still print clean.
* **Negative control through the kernel**: the generic harness
  (`generic_negative_control(adapter, env_dir=<rvm island>)`) reports `kernel REJECTED the
  forged FALSE proof | TRUE twin compiled clean` (`okay = True`).  Raw runs: the `re` forgery
  fails with `unsolved goals ⊢ a ^ 2 - b ^ 2 = a ^ 2 + b ^ 2` (`sorryAx` in its axioms), the
  cast forgery with `unsolved goals ⊢ ↑m * ↑u ^ 2 = 1 + ↑m * ↑u ^ 2` (`sorryAx`); both TRUE
  twins print `[propext, Classical.choice, Quot.sound]`.
* **Stress** (scratch, `import Mathlib`): 89 instances -- 29 hand edge cases (a projection-shaped
  claim, the `= 0` face, `I` alone, nested powers, rational coefficients, degree 10, a
  factored claim, natural-number atoms in every mode, mixed binders, the cast face with
  rationals, negatives, two natural atoms and a reordered claim) and 60 seeded random
  expressions over every mode -- all elaborate with exit 0 and print the three standard
  axioms; the 89 hand-minted twins with the claim shifted by `+1` ALL fail (89 errors, 89
  `sorryAx`, 0 clean).  The only diagnostics in the clean run are the unusedTactic warnings of
  the two instances where `simp only` closes the goal outright (section 4).  An earlier pass
  of the same run, before the bare-atom refusal existed, had six such instances, five of them
  bare atoms (`((c : ℂ) : ℂ).im = 0` and the like): that is what the bare-atom refusal in
  section 5 came from.
* **Reached sites outside the probe** (section 7.3): the fourteen instances of
  `_audit_reached_cases` emitted into one `import Mathlib` file elaborate with exit 0, no
  diagnostics, and the three standard axioms each.
