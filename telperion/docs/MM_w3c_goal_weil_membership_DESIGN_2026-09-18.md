# W3c: the concrete membership goal for MIRRORMERE — design memo

*2026-09-18. Node: `MM_zeta_comb_membership` (kind `goal`, status `draft`, permanently).
Replaces the 2026-09-14 placeholder `theorem zeta_comb_membership : RiemannHypothesis`.
No RH progress is claimed anywhere in this memo or in anything it describes.
`conjecture1_proved = False`.*

---

## 0. The statement, as re-authored

`telperion/missions/mirrormere/lean/Statements/MM_zeta_comb_membership.lean` (written through
the registry writer `telperion.missions.statements.write_statement`; header hash regenerated;
`regen_diff` clean):

```lean
import Mathlib
import Statements.MMDefs

theorem zeta_comb_membership :
    ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by sorry
```

In words: for every smooth compactly supported complex test function `g`, the Weil functional
**read from the primes side** is nonnegative on the Hermitian autocorrelation `g ⋆ g̃`.

This is defect-0 membership of the **regularized triple** — roadmap A5, which is the D11 wall
form, and the "support reality" clause of `QC_TORUS_MEMO` §2.2 — written in the program's own
diffraction vocabulary instead of as a pointer at Mathlib's `RiemannHypothesis`.

**It is RH-equivalent.** Weil (1952); Bombieri (2000) states the criterion on exactly this
class, `C_c^∞(ℝ)`. So the node is registered as the campaign goal and nothing else: never
attempted, never decomposed (roadmap A5 refuses decomposition, precedent-mandated), status
`draft` forever. The classical equivalence with `RiemannHypothesis` is **not** proved and
**not** registered as a lemma — it would be RH ↔ RH.

---

## 1. Why this is now authorable (it was not on 2026-09-14)

The 2026-09-14 placeholder existed because the "regularized triple" had no formal referent:
the raw dual comb is **unconditionally non-tempered** (`Σ_{n ≤ e^R} Λ(n) n^{-1/2} ~ 2 e^{R/2}`,
roadmap §1) and carries an absolutely continuous archimedean component, so no naive clause list
can carry membership.

E8 changed that. `RvMBridge4.limit_explicit_formula`
(`telperion/examples/rvm_bridge/lean/E6Bridge4.lean`, on `main`, kernel-checked, axioms
`[propext, Classical.choice, Quot.sound]`; registry node `RH_limit_explicit_formula`) proves the
unconditional Guinand–Weil identity for every `f` in this class, in exactly three pairings:

| diffraction object | paired with | E8 term |
|---|---|---|
| zero comb `Σ_ρ m(ρ) δ_{γ_ρ}` | `h` | `HasSum (zeroMult · weilKernel f)` |
| archimedean density `(1/2π) Re ψ(1/4 + ir/2) dr`, plus `-log π · δ_0` | `h`, resp. `f` | `archSide f` |
| prime comb `Σ_n Λ(n)/√n (δ_{log n} + δ_{-log n})` | `f` | `primeSide f` |

So `archSide f - primeSide f` **is** the zero-side sum. Naming it `weilForm f` and evaluating it
at `f = autocorr g` gives a sentence about the zero comb that mentions no zero: the statement is
written entirely in prime-side and archimedean data. That is what "membership of the regularized
triple" means concretely, and it is the whole content of this authoring item.

The positivity content: with `H_f(s) = weilKernel f s`,

```
weilKernel (autocorr g) s = weilKernel g s * conj (weilKernel g (1 - conj s)),
```

(one Fubini; verified numerically in §6), so on the critical line `s = 1/2 + ir`, `r` real,
`1 - conj s = s` and the value is `‖h_g(r)‖² ≥ 0`. Zeros on the line contribute nonnegatively;
an off-line quadruple is exactly what can make the sum negative. Defect 0 ⟺ positivity ⟺ RH.

---

## 2. Vocabulary

### 2.1 Mirrored verbatim (six defs)

`MMDefs.lean` gains the `WeilExplicit` namespace as a **verbatim** copy of
`telperion/missions/rh/lean/Statements/RHDefs.lean` lines 118–167 (branch `rh/e8-statement`):
`IsWeilTest`, `weilKernel`, `zeroMult`, `archIntegrand`, `archSide`, `primeSide`. Same
discipline as the existing `RHInBoxAnalytic` / `DiffractionCore` cross-island blocks; line range
cited in the file.

`Complex.digamma` exists at the v4.32.0 pin
(`Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean` is present in the island's Mathlib), so
the v4.32 statements island suffices — no new toolchain. The island was built once with
`lake exe cache get` (allowed there; no cache existed) and `lake build` succeeds: **8675 jobs**.

**Second-copy risk, closed mechanically.** The mirror is a second copy of a block the `rh`
campaign owns. `examples/rvm_bridge/generate.py` — already the drift gate for the four bridges —
gained check **(7)**: the six `WeilExplicit` defs in `MMDefs.lean` must match
`E6Bridge4.lean` def-for-def (comment- and whitespace-normalised). It passes today, and
`E6Bridge4.lean` is itself gated against `RHDefs.lean` whenever that file is in the checkout. So
a future edit on either side fails CI instead of silently forking the vocabulary. (`build_mmdefs.py`
remains the grant-pass deliverable; this gate is the interim, and it is stronger than a
regeneration script because it compares against the *kernel-checked artifact*.)

### 2.2 Authored (two defs, flagged AUTHORED in the file)

```lean
noncomputable def autocorr (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g v * (starRingEnd ℂ) (g (v - u))

noncomputable def weilForm (f : ℝ → ℂ) : ℂ := archSide f - primeSide f
```

* `autocorr` is `g ⋆ g̃` with `g̃ u = conj (g (-u))`: `(g ⋆ g̃)(u) = ∫ g(v) conj(g(v-u)) dv`.
  Hermitian, **not** even — its imaginary part is odd, which is precisely why the mirrored class
  keeps `g` complex-valued with no parity hypothesis (E8 memo §3.4, decision (3)).
* `weilForm` is the functional **read from the primes side**. Writing it as the zero-side sum
  would smuggle the zeros into the statement; writing it this way keeps the sentence about the
  regularized triple, with E8 supplying the identification.

Normalisation decision (2): `autocorr` must agree with D2's `crossCorr` at `i = j` when the D2
node is authored. D2 does not exist yet, so the constraint is recorded here rather than encoded;
the convention pinned here is `crossCorr g h u = ∫ g v * conj (h (v - u))`, i.e. no `1/2π`, no
normalising factor, conjugate on the **second** argument.

---

## 3. Decisions taken (and the ones refused)

1. **`.re` on the conclusion.** The zero-side sum is real by the `ρ ↦ 1 - conj ρ` symmetry of the
   zero multiset; taking `.re` avoids carrying an imaginary-part lemma inside the statement.
   Independently, `autocorr g` is Hermitian, which is *proved* in the probe file
   (`autocorr_hermitian`, sorry-free, axiom-clean), so the `.re` is not hiding anything.
2. **No support bound.** A clause `supp g ⊆ [-L, L]` with `L` fixed (the B9 `2L ≤ log 2` shape) is
   *still* the wall at every height, so it is not a milestone and is not added.
3. **Deps.** The node keeps its full existing dependency list unchanged. The work item asks for
   the D2/D3 nodes to be added; they are **not registered yet**, and a dangling dependency fails
   `mission verify`. Recorded as the follow-up: add `MM_weil_gram_trace` (D2) and the
   certified-height node (D3) to `depends_on` at the moment they are registered.
4. **`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, never `ContDiff ℝ ⊤`.** The latter means *analytic*,
   which with compact support collapses the class to `{0}` and makes the statement vacuous. The
   probe file proves `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ⊤`.
5. **Re-authored through the registry writer**, never by hand-editing the generated file
   (the #543 precedent); the goal's `kind` and `status` are untouched.

**Refused, explicitly.**

* The Selberg-class / B-mult-twisted "growth-carrier" form (arithmetic FQ ⟺ Selberg element) is
  **substrate-blocked**: `ARITHMETIC_FQ_MEMBERSHIP_SPEC` §4 — no Fourier transform of measures,
  no almost-periodicity, no `∏_p S¹` in Mathlib. Registering it behind an `opaque` def would fail
  that spec's own vacuity check *by construction*. The growth clause stays prose in
  `mission.toml`'s description/sources.
* Decomposition of this node into sub-milestones (roadmap A5).
* Any attempt. The node is never claimed and never worked.

---

## 4. Vacuity and triviality traps, and how the statement avoids each

| hazard | where it bites | how it is avoided | evidence |
|---|---|---|---|
| junk Bochner integrals (a non-integrable integrand integrates to `0`, making the sentence `0 ≤ 0`) | `archSide`, `primeSide`, `autocorr` | `autocorr g` is `C_c^∞` for `g` in the class (Mathlib compact-support convolution smoothness), so every term is an honest value | numeric read-back §6: the value is `≈ 1.5708`, not `0`, and matches the zero-side sum to 18 digits |
| vacuous `∀` (empty test class) | `IsWeilTest` | probe `test_class_nonvacuous` proves `∃ g, IsWeilTest g ∧ g ≠ 0` from a `ContDiffBump` | probe file, axiom-clean |
| `ContDiff ℝ ⊤` = analytic ⇒ class `{0}` | `IsWeilTest` | index written `((⊤ : ℕ∞) : WithTop ℕ∞)` | probe `smoothness_index_is_not_analytic` |
| the statement closes by `simp`/`aesop`/`norm_num` | whole goal | it does not; see the battery in §5 | 7 probes, all fail to close |
| the right-hand side is simp-trivially `0` | `weilForm` | `weilForm f = 0` is *not* provable by `simp` | probe 6 |
| `autocorr` collapses to `0` | `autocorr` | `simp [autocorr]` makes no progress on `autocorr g = 0` | probe 7 |
| the degenerate witness `g = 0` makes it contentless | instance | true and contentless *at that point only*; the class contains nonzero elements and the value there is order one | `degenerate_witness_is_contentless` + §6 |
| a dropped `conj`, or `ρ` vs `1 - conj ρ`, silently changing the sentence | `autocorr`, `weilKernel` | the Arb backend re-derives `autocorr`, `weilKernel`, and the factorisation identity **from the defining integrals as written in MMDefs**, at 30 digits, and aborts on mismatch | `telperion.weil_gauss.anchor_check`, §6 |
| the mirrored block drifting from the rh campaign's copy | `MMDefs` | `examples/rvm_bridge/generate.py` check (7) | green |
| an evenness/parity hypothesis quietly excluding B7's odd imaginary parts | class | no parity hypothesis anywhere | §2.2, E8 memo §3.4 |

---

## 5. Trivial-close probes (run, recorded)

Island `telperion/missions/mirrormere/lean` at `leanprover/lean4:v4.32.0` / Mathlib `v4.32.0`,
each probe as a standalone file via `lake env lean`. Verbatim results are in the probe file
`lean/Probes/MM_zeta_comb_membership_WIP_PROBE.lean` (outside `defaultTargets`, outside every
axiom guard):

| probe | tactic | result |
|---|---|---|
| 1 | `simp [all eight defs]` | `error: unsolved goals` (fully unfolded goal displayed) |
| 2 | `simp_all [...]` | `error: unsolved goals` |
| 3 | `aesop (add simp [...])` | `aesop: failed to prove the goal after exhaustive search` |
| 4 | `intro g hg; norm_num [...]` | `error: unsolved goals` |
| 5 | `intro g hg; positivity` | `failed to prove positivity/nonnegativity/nonzeroness` |
| 6 | `weilForm f = 0` by `simp` | `error: unsolved goals` (RHS not simp-trivial) |
| 7 | `autocorr g = 0` by `simp [autocorr]` | ``simp`` made no progress` |

Probes that **succeed**, and are therefore live, sorry-free, axiom-clean code in the probe file
(`[propext, Classical.choice, Quot.sound]`, and `[propext, Quot.sound]` for the `decide` one):
`test_class_nonvacuous`, `smoothness_index_is_not_analytic`,
`degenerate_witness_is_contentless`, `autocorr_hermitian`, `autocorr_zero_nonneg`,
`instance_of_enclosure`, `neg_enclosure_refutes_rh`. Only the WIP restatement of the goal itself
carries `sorryAx`, and it is quarantined in that file.

---

## 6. The numeric read-back (mandatory, run — not assumed)

The risk on this item is that a normalisation slip turns the sentence into something false or
trivial. Two independent checks were run.

**(a) Derivation-level, mechanised.** `telperion.weil_gauss.anchor_check` recomputes, by direct
quadrature of the definitions exactly as written in `MMDefs.lean`, the values of
`autocorr g u` (at `u = 0, 0.7, -1.3`), `weilKernel (autocorr g) s` (at `s = 0, 1, 1/2 + 2i`) and
the factorisation `h_{g⋆g̃}(r) = ‖h_g(r)‖²`, and compares them against the closed forms used by the
certificate at 30 digits with a `1e-20` relative tolerance. A missing conjugate, `g (u - v)` in
place of `g (v - u)`, or `e^{(1/2-s)u}` in place of `e^{(s-1/2)u}` fails this gate, which
**aborts** before any certificate is produced. It passes.

**(b) Value-level, against the other side of the explicit formula.** For
`g(u) = exp(-(u-c)²/(2a²)) e^{iωu}` every term is closed-form:

```
W(g) = 4π a² e^{a²(1/4 - ω²)} cos(a²ω)  −  a√π log π
       + a² ∫ e^{-a²(r+ω)²} Re ψ(1/4 + ir/2) dr
       − 2 a√π Σ_{n≥2} Λ(n) n^{-1/2} e^{-(log n)²/(4a²)} cos(ω log n).
```

Certified with Arb (python-flint 0.6.0, 256-bit, rigorous `acb_calc` quadrature, elementary
tail bounds for both truncations), against the **independent zero-side reading**
`Σ_ρ m(ρ) h_f(γ)` over the first 40 zero pairs (mpmath, 25 digits):

| test function | certified enclosure of `W` | zero-side sum | agreement |
|---|---|---|---|
| `a = 1/2`, `ω = -14.1347` (first zeta ordinate) | `[1.5708074408338, 1.5708074408348]` | `1.5708074408343442739` | 18 digits |
| `a = 1/2`, `ω = -21.02` (second ordinate) | `[1.6001063093678, 1.6001063093688]` | `1.6001063093683198989` | 18 digits |
| `a = 1/2`, `ω = -0.3` (off the comb) | `[-5.05e-13, 5.05e-13]` | `≈ 1e-22` | **refused**: straddles zero |

Three things are established. The value is **positive and of order one** (`≈ 2πa² = π/2` — the
instrument is literally reading the first Bragg peak of the zero comb), so the sentence is not a
junk-integral `0 ≤ 0`. The primes-side reading and the zero-side reading of the same functional
**agree**, so the mirrored vocabulary carries the intended normalisation. And a test function
aimed *away* from the comb returns `0` to working precision — which is the honest refusal in the
third row, and is the strongest available evidence that the certificate is measuring zeros and
not an artefact.

---

## 7. Consumers, and the certificate shape

The goal node itself has **no consumers** — nothing may depend on a wall. Its finite faces are:

* **D2** — the primes-side Weil–Gram matrix `G_ij = weilForm (crossCorr g_i g_j)`; its inertia is
  what the defect instrument counts. Certificate shape: `tool-interval-gram-inertia` (not yet
  built).
* **D3** — the certified-height bound: positivity of the Gram form below an explicit height, with
  the constant `C_g` supplied by the effective-constant corridor form. Certificate shape:
  `tool-weil-form-enclosure`.
* **The defect instrument** — `offline_pairs_le_defect` counts the negative inertia of exactly
  this Hermitian form.

### 7.1 New tool built for this item: emitter kind `weil_form_enclosure`

The survey found the D3-shaped face (and this goal's own read-back) had **no certificate type in
the registry**, so one was built rather than hand-waved:

* `telperion/src/telperion/weil_gauss.py` — the Arb backend of §6 (closed forms, anchor gate,
  rigorous quadrature, explicit prime-side and archimedean tail bounds, exact outward rational
  readout).
* `telperion/src/telperion/emit_weil_form_enclosure.py` — the emitter. Per instance it emits the
  rational implication `lo ≤ W → W ≤ hi → 0 < W ∧ W ≤ hi` (or the negative branch), the sign
  decided by `norm_num`; the enclosure is the documented non-kernel trust seam, exactly as in the
  Li ladder and the Bragg floor, so a forged enclosure falsifies the hypothesis and leaves the
  implication kernel-valid. **Three honest refusals**: an inconsistent enclosure; an enclosure
  that **straddles zero** (sign undecided — do not emit); and an enclosure **disjoint from the
  independent zero-side reading** of the same functional (the two sides of the explicit formula
  disagreeing is a normalisation bug, not a certificate). The third refusal is the E8 identity
  used as a cross-instrument gate, and is new in this emitter.
* **Falsifiability face** `weil_form_neg_refutes_rh`: given Weil's criterion in the forward
  direction as an **undischarged** hypothesis (classical; not in Mathlib), a certified strictly
  negative value at an admissible `g` refutes RH. The instrument could have falsified; it does
  not. **Membership face** `weil_form_instance_of_enclosure`: a certified positive value gives the
  goal's conclusion at that one `g` — and nothing more (roadmap §1: no finite family of test
  functions approaches a wall form). Both faces are stated over abstract parameters so the emitted
  file needs no registry vocabulary; the probe file instantiates them at
  `WeilExplicit.weilForm ∘ autocorr`.
* `telperion/examples/weil_form_enclosure/` — the island, registered in `telperion.toml`
  (`group = "quick"`, so the manifest stays complete); its generated
  `lean/WeilFormEnclosure.lean` compiles clean against bare Mathlib.
* `telperion/tests/test_weil_form_enclosure_emitter.py` — 15 tests: wiring, the three refusals,
  both rendering branches, byte-stability, and the flint-gated backend check that the enclosure
  contains the zero-side reading.
* `telperion/src/telperion/negctrl_adapters/adapter_weil_form_enclosure.py` plus the stance in
  `emitter_sensitivity.REGISTRY` (`STRUCTURALLY_NONVACUOUS`, `NEG_CONTROL_ADAPTER`). The
  kernel-gated two-layer control was **run**:
  `negative[kernel REJECTED the forged FALSE proof] | positive[TRUE twin compiled clean]`,
  `okay = True`.

---

## 8. What this does NOT do

It does not prove, approach, or weaken RH. It replaces one placeholder sentence with a faithful
one, in the campaign's own vocabulary, and builds the finite instrument that reads that
sentence's values. The goal node stays `draft`, is never attempted, and is never decomposed.
Every file touched carries the line `conjecture1_proved = False`.
