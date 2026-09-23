# `zero_sum_majorant` -- a zero-supported family is summable through a finite window plus the local-count tail (2026-09-22)

`conjecture1_proved = False`. Every theorem this kind writes is a summability or pointwise-majorant
fact about a family indexed by the nontrivial zeros of zeta, true whatever their real parts are,
plus one rational inequality on the open strip `0 < Re rho < 1`. Nothing here says where the zeros
are, and nothing here is a step toward RH.

Source: `SHAPES_AUDIT_48H_2026-09-22.md` section 2 (rank 2), merging
`SHAPES_AUDIT_C_B7_PARTIAL_FRACTION_2026-09-22.md` 3.1 (shape A) with
`SHAPES_AUDIT_B_WEIL_WALL_2026-09-22.md` N5 (the tail envelope, emitted as a second mode). Build
order: sprint 2, item 4, after the P1 prelude `RvMBridgeXi` (landed).

## The shape that had no certificate type

A term family `f : C -> C` supported on the nontrivial zeros is shown summable, at thirteen sites
on the rvm_bridge / li / Zeta23 islands, by the same three steps: `f rho = 0` off the zeros (the
hypothesis-free `zeroMult_eq_zero_of_not_nontrivial` rewrite); the finitely many zeros of a centred
ordinate window `|Im rho - a| < h` absorbed by a `Set.indicator` (`zetaSeam.finite_window`); every
other zero bounded by the local-count majorant `m(rho) C/(1 + |gamma_rho|^2)`, summed by
`RvMBridgeGauss.summable_mult_div_one_add_normSq`. Since the P1 prelude those three steps are ONE
atom (`RvMBridgeXi.zeroBoundAt`, `norm_le_zeroBoundAt`, `summable_zeroBoundAt`). What each site
still re-proves by hand is the input to the last step, one two-variable strip inequality:

| site (audit C 2.1) | term family | strip inequality | `C_far` |
|---|---|---|---|
| `E6Bridge19` `zbound` (audit lines 324-355) | `zterm k` on a ball | `1/\|rho\|^2 <= (9/4)/(1 + \|gamma\|^2)`, `\|Im rho\| >= 1` | `(k+1)! 2^(k+2) (9/4)` |
| `E6Bridge18` `polBound` (116-184) | `m/(s - rho)^2` | `1/(Im rho - Im s)^2 <= (13/4 + 2 (Im s)^2)/(1 + \|gamma\|^2)`, `\|Im rho - Im s\| >= 1` | `13/4 + 2 (Im s)^2` |
| `E6Bridge15` `liBound` (349-410) | `m Re K_n(rho)` | the 9/4 inequality again (re-proved inline) | `(9/4) 2^n` |
| `E6Bridge22` `lcTerm` (49-69) | `m/(1 + (Im rho - a)^2)` | `h = 0`, `D = 1 + (Im rho - a)^2` | `13/4 + 2 a^2` |
| `E6Bridge19` 586-595, 743-773; `E6Bridge17` 266-289; `E6Bridge20` 186-286; `E6Bridge24` 815-821 | segment / reflection / Gaussian pair / uniform-on-a-ball / tsum comparison | the same family of strip inequalities | see audit C 2.1 |

Audit C 5.3 counts 79 hand `nlinarith` strip calls in the cluster. The certificate is exact and
tiny (three or four terms for every dogfood site), so the emitted proof no longer depends on an
`nlinarith` hint list.

## Statement family

**Mode `zero_window`.** Inputs: a centre `a` (a rational, or a polynomial in declared real
parameters such as `Im s`, each bound by a `(name : ℝ)` or `(name : ℂ)` binder), a near radius
`h in {0, 1, 2}`, a far constant `C >= 0` and numerator `N >= 0` (polynomials in the parameters
that `positivity` closes: nonnegative coefficients, even powers), a denominator `D` in
{`normSq rho`, `(Im rho - a)^2`, `1 + (Im rho - a)^2`}, and a `prefactor` flag. Each instance `nm`
emits up to three faces, each consuming the previous one:

```
theorem nm_strip <binders> {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ) (him : (h : ℝ) ≤ |ORD|) :
    N / D ≤ C / (1 + Complex.normSq (Zeta23.gammaOf ρ))

theorem nm_le <binders> {f : ℂ → ℂ} {b : ℂ → ℝ} [{K : ℝ} (hK : 0 ≤ K)]
    (hzero : ∀ ρ, ¬ Zeta23.IsNontrivialZero ρ → f ρ = 0)
    (hwin : ∀ ρ, Zeta23.IsNontrivialZero ρ → |ORD| < (h : ℝ) → ‖f ρ‖ ≤ b ρ)
    (hshape : ∀ ρ, Zeta23.IsNontrivialZero ρ → (h : ℝ) ≤ |ORD| →
      ‖f ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ([K *] (N / D)))
    (ρ : ℂ) :
    ‖f ρ‖ ≤ RvMBridgeXi.zeroBoundAt a h ([K *] C) b ρ

theorem nm_summable <binders> {f : ℂ → ℂ} [{K : ℝ} (hK : 0 ≤ K)] (hzero) (hshape) : Summable f
```

`ORD` is `ρ.im` for centre 0 (the island's own `|ρ.im|` spelling) and `ρ.im - a` otherwise. The
prefactor `K` (`2^n` for the Li kernel, `(k+1)! 2^(k+2)` for the Taylor ladder) multiplies BOTH the
far-shape hypothesis and the emitted constant, so it never touches the certified inequality. The
term family's own analysis -- that `norm f` has the shape `m * N/D` off the window, and the window
bound `b` -- is NOT emitted: it enters as the named hypotheses `hwin` / `hshape`. `nm_summable`
instantiates `b := ‖f‖`, so it needs only `hzero` and `hshape`.

**Mode `tail_envelope`** (the B N5 consumer face):

```
theorem nm_envelope {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) [{E : ℝ} (hE : 0 ≤ E)]
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x

theorem nm_rate {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ P) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * P) * Real.exp (2 * φ)
      ∧ Real.exp (2 * (lam - 1) * P) ≤ 1
```

`E` is a rational `>= 0` (re-checked by `norm_num`) or symbolic (then the face IS the prelude's
`norm_tsum_subtype_le_mul_tsum`). `P` is a rational `< 0`. The first conjunct of `nm_rate` holds
for every `P`; the second is what `P < 0` buys (the envelope factor does not grow with `lam`), and
it is FALSE for every `P > 0` at `lam = 2`, so a forged sign cannot compile.

## The certificate

`ZeroSumMajorantCert` carries the instance data and, for `zero_window`, the load-bearing `terms`:
exponent vectors over the generators

```
g0 = x,   g1 = 1 - x,   g2 = (w - a)^2 - h^2,   p^2 (each parameter),   S^2 (declared squares)
```

(`x = Re rho`, `w = Im rho`) with NONNEGATIVE rational coefficients whose expansion is EXACTLY the
cleared residual

```
R(x, w) = C * D(x, w) - N * (1 + w^2 + (1/2 - x)^2)   >= 0   on {0 < x < 1} cap {(w - a)^2 >= h^2}.
```

Untrusted Python finds it by the audit's route, in exact arithmetic (sympy `Rational`, floats
refused): shift to `y = w - a`; remove the odd-in-`y` part with a nonnegative rational multiple of a
declared square (the default square for `a != 0` is `(w - 2a)^2`, which is exactly the island's
`sq_nonneg (ρ.im - 2 * s.im)` hint in `E6Bridge18`); substitute `y^2 -> h^2 + t`; expand every
`(t, parameter)`-coefficient in the Bernstein basis `x^i (1-x)^(d-i)` of `[0, 1]`, elevating the
degree up to a cap (8) until the weights are nonnegative. Verification is one exact
`sympy.expand` equality. `certify` also runs `nonvacuity.assert_certificate_sensitive` on the
identity (bumping any coefficient or dropping a term must break it), so the registry lists the
kind as CERTIFICATE_SENSITIVE and wired.

The dogfood certificates, exactly:

| instance | certificate `R = ...` |
|---|---|
| 9/4 (zbound, liBound) | `(5/4) t + 1 * x (1 - x) + (9/4) x^2`, `t = (Im rho)^2 - 1` (audit C 2.1's "`(5/4) t + (5/4) x^2 + x`") |
| polBound | `(Im rho - 2 Im s)^2 + (5/4) t + 2 (Im s)^2 t + x (1 - x)`, `t = (Im rho - Im s)^2 - 1` |

## Tactic skeleton

The strip face (the regenerated `zbound_regen_strip`, verbatim):

```
  have hre : (0 : ℝ) < ρ.re := hz.2.1
  have hre1 : ρ.re < 1 := hz.2.2
  have hx0 : (0 : ℝ) ≤ ρ.re := hre.le
  have hu0 : (0 : ℝ) ≤ 1 - ρ.re := by linarith
  have ht0 : (0 : ℝ) ≤ ρ.im ^ 2 - 1 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) him 2
    rw [sq_abs] at h2
    linarith
  have hg : Complex.normSq (Zeta23.gammaOf ρ) = ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hn : Complex.normSq ρ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  have hden : (0 : ℝ) < (ρ.re ^ 2 + ρ.im ^ 2) :=
    add_pos_of_pos_of_nonneg (pow_pos hre 2) (sq_nonneg _)
  have hγ : (0 : ℝ) < (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2)) := by positivity
  rw [hn, hg, div_le_div_iff₀ hden hγ]
  have key : (9 / 4) * (ρ.re ^ 2 + ρ.im ^ 2) - 1 * (1 + (ρ.im ^ 2 + (1 / 2 - ρ.re) ^ 2))
      = (5 / 4) * (ρ.im ^ 2 - 1) + 1 * (ρ.re * (1 - ρ.re)) + (9 / 4) * ρ.re ^ 2 := by
    ring
  have t1 : (0 : ℝ) ≤ (5 / 4) * (ρ.im ^ 2 - 1) := mul_nonneg (by norm_num) ht0
  have t2 : (0 : ℝ) ≤ 1 * (ρ.re * (1 - ρ.re)) := mul_nonneg (by norm_num) (mul_nonneg hx0 hu0)
  have t3 : (0 : ℝ) ≤ (9 / 4) * ρ.re ^ 2 := mul_nonneg (by norm_num) (pow_nonneg hx0 2)
  linarith only [key, t1, t2, t3]
```

The `hg` rewrite is `RvMBridgeXi.inv_im_sq_le_majorant`'s own line. `key` is the certificate: the
coefficients are load-bearing (`ring` fails on a corrupted one), each summand is nonnegative by an
explicit `mul_nonneg` term whose type is exactly the rendered summand, and `linarith only` sums the
listed facts -- no hint search. `ORD = ρ.im - a` gives `hden : 0 < (ρ.im - a) ^ 2 := by linarith`
(from `ht0`, `h >= 1`); `D = 1 + ORD^2` gives `by positivity`; `h = 0` gives
`ht0 := sq_nonneg _` and an unused `_him`.

The majorant face is the audit's skeleton (a parameterised copy of `E6Bridge19.lean:147-175`):
`refine RvMBridgeXi.norm_le_zeroBoundAt hzero hwin (fun ρ hz him => ?_) (by positivity) ρ`, then
`(hshape ρ hz him).trans`, `mul_le_mul_of_nonneg_left` against `Nat.cast_nonneg`, and (with a
prefactor) `rw [mul_div_assoc]` + `mul_le_mul_of_nonneg_left (nm_strip ...) hK`; for centre 0 the
two window hypotheses are converted from `|ρ.im - 0|` by `simpa`. The summable face is
`Summable.of_norm_bounded (RvMBridgeXi.summable_zeroBoundAt a h C (fun ρ => ‖f ρ‖)) (nm_le ...)`.
The envelope is the audit's `norm_tsum_le_tsum_norm` + `tsum_le_tsum` + `tsum_subtype_le` +
`tsum_mul_left` chain (Mathlib only, the prelude's own proof); the rate face is `Real.exp_add` +
`Real.exp_le_exp` + `nlinarith [mul_le_mul_of_nonneg_left hφ hl]`, then `Real.exp_le_one_iff` +
`mul_nonpos_of_nonneg_of_nonpos` with `P <= 0` by `norm_num`.

## Refusals (the forge face)

| phantom | why it is refused |
|---|---|
| `C < 0`, or `C` / `N` with a negative coefficient or an odd parameter power | `positivity` cannot close `0 <= C`; the majorant is meaningless |
| Polya / Bernstein check fails with a located rational point where `R < 0` | the claim is FALSE (reported with the exact point). The audit's named phantom -- `h = 0` with `1/\|rho\|^2` -- is located at `Re rho = 1/1000`, `Im rho = 0`; `C = 2 < 9/4` at `Im rho = 1` |
| Polya / Bernstein check fails with no located point | OBSTRUCTED (unproved, not refuted), with the elevation cap; e.g. the TRUE polBound claim with its hand square withheld keeps an odd ordinate part |
| `h` not in `{0, 1, 2}`; `window != "ordinate"` | the near set must be a bounded ordinate window (finiteness only from `zetaSeam.finite_window`) |
| `support != "hypothesis_free"` | the support fact must be the `zeroMult_eq_zero_of_not_nontrivial` rewrite |
| unknown `den_kind`; `ordinate_sq` with `h = 0` | `D = (Im rho - a)^2` vanishes on the strip: no `Summable` claim survives a zero denominator |
| `N = 0` | nothing to certify |
| supplied terms with a negative / zero coefficient, a malformed or negative exponent vector, or an expansion that is not the residual | the identity IS the certificate (a forged list is also checked for a FALSE claim and says so) |
| tail: `P >= 0`, `E < 0`, `rate` without `P`, `P` without `rate` | no decay / meaningless envelope / ill-formed |
| floats anywhere (including `"2.25"`); symbols in `C`, `N` or the centre that are not declared parameters; non-rational coefficients (`I`, `pi`) | exactness |
| parameter / binder names that are not ASCII Lean identifiers or collide with a name the proofs bind (`hz`, `key`, `t1`, `K`, `f`, `b`, ...); a parameter whose head is not bound; binder types other than `ℝ`, `ℂ` | hygiene: a shadowing name is refused rather than emitted |
| `summable` without `majorant`, `majorant` without `strip`, unknown / duplicate faces; keys of the other mode | ill-formed |

## Negative control (`negctrl_adapters/adapter_zero_sum_majorant.py`)

FALSE twin: the 9/4 strip instance with its terms, forged to `C = 1` (`dataclasses.replace`,
past Layer 1). Cleared, the claim reads `Re rho >= 5/4`: false at every point of the strip (at
`rho = 1/2 + i`: `4/5 > 1/2`), hence at every nontrivial zero on the line or off it. TRUE twin:
`C = 9/4`. Only the statement line and the `key` left-hand side differ (the test pins this). The
twins elaborate over `import Mathlib` with stand-ins in the prelude: `Zeta23.IsNontrivialZero` keeps
the two strip conjuncts the proof reads (`True ∧ 0 < ρ.re ∧ ρ.re < 1`), and `Zeta23.gammaOf` is
`(ρ - 1/2)/I` written by components so `gammaOf_re` / `gammaOf_im` are `rfl` on any Mathlib.

Run against the built rvm_bridge env through `generic_negative_control`: `kernel_rejects = True`
(the forged `key` leaves unsolved goals after `ring`; the declaration falls back to `sorryAx`),
`true_compiles = True` (`[propext, Classical.choice, Quot.sound]`), `okay = True`.

## Dogfood (`examples/rvm_bridge/lean/Probes/Dogfood_zero_sum_majorant.lean`)

Generated by `examples/rvm_bridge/dogfood_zero_sum_majorant.py` (`--check` for drift; the test
`test_dogfood_file_is_regenerable_byte_for_byte` pins the bytes). It imports `E6Bridge12`,
`E6Bridge15`, `E6Bridge18`, `E6Bridge19` and `RvMBridgeXi`, states the regenerated lemmas under NEW
names, and modifies nothing:

```
cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_zero_sum_majorant.lean
```

| emitted | regenerates | kernel cross-check appended |
|---|---|---|
| `zbound_regen_{strip,le,summable}` | `E6Bridge19` `zbound`, `norm_zterm_le_zbound` | the strip proves `RvMBridgeXi.inv_normSq_le_majorant`'s statement and vice versa; `_le` with `K := (k+1)! 2^(k+2)` proves `norm_zterm_le_zbound` VERBATIM (the emitted constant `K * (9/4)` is `zbound`'s on the nose; `zeroBound_eq`); `_summable` gives the k-th terms summable on the ball |
| `polBound_regen_{strip,le,summable}` | `E6Bridge18` `polBound`, `norm_polTerm_le`, `summable_polTerm` | strip + glue proves `norm_polTerm_le_majorant` (and the original proves the same statement); `_le` proves `norm_polTerm_le` VERBATIM (`polBound s` IS `zeroBoundAt (Im s) 1 ...` definitionally); `_summable` proves `summable_polTerm` |
| `liBound_regen_{strip,le,summable}` | `E6Bridge15` `liBound`, `norm_liPaired_le`, `summable_liPaired` | `_le` with `K := 2^n` proves `norm_liPaired_le` VERBATIM (`liBound n = zeroBoundAt 0 1 (2^n (9/4))` by `simp only` + `ring`); `_summable` proves `summable_liPaired` |
| `tail_regen_{envelope,rate}` | `E6Bridge12` `tail_bound_window` (B N5) | the envelope and the prelude's `norm_tsum_subtype_le_mul_tsum` prove each other's statement; `tail_bound_window` re-derived line for line with the envelope swapped in (and the original proves the same statement); the rate face's first conjunct is `exp_two_mul_le_of_le` at `P = -1/4` |

The instance GLUE (`Glue.zterm_shape`, `zterm_window`, `polTerm_shape`, `liPaired_shape`) is each
family's own far-region analysis copied from the hand proof; it is hand-written, not emitted.

The probe is registered as the island `lean_lib` `DogfoodZeroSumMajorant` (root
`Probes.Dogfood_zero_sum_majorant`, in `defaultTargets` before the guard) and its eleven emitted
theorems are anchors in `AxiomGuardRvMBridge.lean`, so CI's `lake build` + guard step re-check it
against the live prelude, not only against the emitter bytes. (The `exp_threshold` probe is not
registered; the lead may align the two either way.)
Compiled on the island (2026-09-22): all eleven emitted theorems and the four glue lemmas print
exactly `[propext, Classical.choice, Quot.sound]`, every cross-check elaborates; the island
`lake build` completes (8885 jobs) and the guard prints 835 axiom lines, every one exactly the
three, no `sorryAx`. A scratch variety
file (rational centre `3/2` with `h = 2`, a real-parameter centre with `h = 0` and a prefactor,
`normSq` at `h = 2`, a parameter-dependent numerator `1 + c^2`, a rational tail `E = 3/2`,
`P = -2`, a strip-only instance, a `ℂ` binder with a `Re s` parameter) compiled the same way, 18
theorems, no warnings.

## What it does NOT do

* It proves nothing about zeros or about RH. Every dogfood instance was already kernel-checked by
  hand; the value is the regeneration and the kernel gate on the next island.
* It does not prove a family's norm shape (`hshape`) or its window bound (`hwin`): those are the
  instance's analysis and stay hand-written (the dogfood glue is exactly that part).
* It does not prove countability, window finiteness or the local-count summability: those are the
  prelude atom `RvMBridgeXi.zeroBoundAt` it calls (`requires_prelude`; `emit()` refuses a profile
  with no import that could carry it).
* The `zero_window` faces are island-pinned to the rvm_bridge vocabulary (`Zeta23`,
  `WeilExplicit.zeroMult`, `RvMBridgeXi`); the li island has no `RvMBridgeXi`, so "the li island
  reuses the same atom" needs the prelude ported first. The tail faces are Mathlib-only.
* Not regenerated here (the other audit C 2.1 rows): `E6Bridge19` 586-595 / 743-773,
  `E6Bridge17` 266-289 (window as a Finset `if`), `E6Bridge20` 186-286 (uniform-in-`w` face),
  `E6Bridge22` `lcTerm` (its certificate is tested in Python, not compiled against the site),
  `E6Bridge24` 815-821. B N5's `E6Bridge7.lean:465-483` now calls the prelude's
  `norm_tsum_subtype_le_tsum` (not the E-scaled face); it was not cross-checked.
* The rate face takes a RATIONAL `P < 0` (the audit's certificate datum). E6Bridge12's own
  `P = 1/4 - D^2` is symbolic and not sign-certified at the site; the prelude lemma covers it.
* It does not touch `E6Bridge12` / `15` / `18` / `19`; the standing-order REGEN of those sites is
  the lead's call once the probe is green.

## Provenance

Salvaged from an interrupted session (`.claude/worktrees/wf_132b7269-642-5`, base `d2e9befb1`: an
untracked first draft of `emit_zero_sum_majorant.py` and the `certify.py` / `__init__.py`
registration hunks; no adapter, tests, docs or dogfood). Reworked before shipping: fully qualified
Lean names (the draft relied on `open Zeta23`); the certificate stated as an exact `ring` identity
closed by `linarith only` (the draft handed product hints to `nlinarith`, so the coefficients were
not load-bearing); a general window bound `b` in `_le` (the draft fixed `b := ‖f‖`, which cannot
reproduce `zbound`'s ball-uniform window); an optional prefactor; the island spellings `|ρ.im|` and
`Complex.normSq ρ`; the Mathlib-only envelope and the decay conjunct on the rate face; the
sensitivity wiring, adapter, tests, docs and dogfood are new.
