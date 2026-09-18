# MM_weil_form_certified_height — design memo (routes-roadmap D3, reformulated)

*2026-09-18. Statement authored, NOT proved. The node is registered `draft`, its
statement file ends in the by-design `sorry`, and nothing here is evidence for or
against RH.*
**`conjecture1_proved = False`.**

Work item: `mm-d3-certified-height-weil-bound` (contested; §1 records the re-check
of the contested premise and the shape change it forced). Campaign: MIRRORMERE.
Node kind `lemma`, deps `MM_rvm_unbounded_mean_density` (proved) and
`MM_rect_trace_reading` (open, D1).

---

## 0. The statement (as registered)

`missions/mirrormere/lean/Statements/MM_weil_form_certified_height.lean`,
vocabulary in `MMDefs.lean` (§3):

```lean
theorem weil_form_certified_height
    (g : ℝ → ℂ) (hg : IsWeilTest g) (hf : IsWeilTest (autocorr g)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ∃ P : ℂ,
        HasSum (zeroSideBelow (autocorr g) T) P ∧
        ‖weilForm (autocorr g) - P‖ ≤ C * Real.log T / T ^ 3 ∧
        ((∀ ρ : ℂ, zeroMult ρ ≠ 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1 / 2) →
          0 ≤ P.re ∧ -(C * Real.log T / T) ≤ (weilForm (autocorr g)).re)
```

In words: for every smooth compactly supported `g` whose autocorrelation
`f = g ⋆ g̃` is again a test function there is a constant `C = C(g) ≥ 0` such that
at every height `T ≥ 2`

* **unconditionally** the zero side truncated at `|Im ρ| ≤ T` is summable, with
  value `P`, and `‖W(f) − P‖ ≤ C log T / T³`, where `W(f) = archSide f − primeSide f`
  is the **primes-side** Weil functional; and
* **given the certified-ladder hypothesis at that height** (every zero with
  ordinate in `(0, T]` lies on the critical line), `Re P ≥ 0` and hence the
  consumer-facing face `−(C log T / T) ≤ Re W(f)`.

---

## 1. The contested premise, re-checked — and what it cost

The work item proposed the headline-only shape

```lean
∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
  (∀ ρ, zeroMult ρ ≠ 0 → |ρ.im| ≤ T → ρ.re = 1/2) →
    -(C * Real.log T / T) ≤ (weilForm (autocorr g)).re
```

and argued it is non-trivial because "the trivial choice `C := −2W/log 2` does not
close it for `T > 2`". **That triviality check was incomplete, and the skeptic was
right about the shape** (though not about the node: the g-coordinate reformulation
itself survives, see §2). The conclusion `W` does not depend on `T`, and the
hypothesis family is downward closed in `T`, so:

* if `W ≥ 0`, `C := 0` closes it;
* if `W < 0`, then the hypothesis confines `T` to `[2, B]` for `B` the ordinate of
  the lowest off-line zero, and on that bounded range `log T / T` has a positive
  minimum, so a large enough constant closes it.

Classically one of the two always holds, so the shape is a theorem of excluded
middle. The registry has no tool for this failure mode, so this pass **built one**
(§5): the emitter `bounded_hypothesis_collapse` (kind registered in
`certify.py`/`emitter_sensitivity.py`, dogfooded by `examples/shape_audit/`) emits
the *collapse witness*, a real Lean theorem exhibiting the closing constant. The
witness and the D3-specific reduction were compiled against the mirrormere island
(Mathlib v4.32.0) and are axiom-clean:

```
'Telperion.ShapeAudit.headline_alone_is_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Telperion.ShapeAudit.headline_alone_is_trivial_cubed' depends on axioms: [propext, Classical.choice, Quot.sound]
'headline_shape_carries_only_the_trivial_direction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`headline_alone_is_trivial` (emitted): for **every** `W`, every hypothesis family
`Pr` and every `B ≥ 2` above which `Pr` fails, the explicit constant
`max 0 (−W) · B / log 2` closes the headline shape. `headline_shape_carries_only_the_trivial_direction`
(hand-written on top of it): given only downward-closedness of the hypothesis
family and the *classical trivial direction* "`Pr` at every height ⇒ `W ≥ 0`"
(i.e. RH ⇒ Weil positivity — which the work item itself refuses as a node), the
headline shape follows. So the headline shape adds **nothing** to the trivial
direction: no certified height, no effective constant, no tail estimate.

**Verdict: not `blocked`.** The item's premise has two parts. The part the skeptic
hit — the exact quantifier shape — is refuted, and this memo replaces it. The part
the item is actually about — that D3's Paley–Wiener refutation is repaired by
working in `g`-coordinates, where off-line values of `H_g` are literal — is
correct and is confirmed by the E8 design memo §2.3. A statement author's job is
to fix the shape, so the node is authored with the repaired shape rather than
abandoned.

**The repair.** Hoist every conjunct that does *not* need the hypothesis *out* of
the implication. Summability and the tail bound are unconditional facts (§4), so
they must hold at every `T ≥ 2` whether or not RH is true, and the case split
cannot supply them. What remains inside the implication (`0 ≤ Re P`) is precisely
the certified ladder's contribution, and it is genuine mathematics at every height
where the ladder holds — including the finitely many where it is *known* to hold.

---

## 2. Why `g`-coordinates (the D3 refutation, and why this is not it)

Roadmap §5 refuted D3 *as stated*: a band-limited `h` on the zero side cannot see
an off-line zero, because seeing `ρ = β + it` means evaluating the transform at the
complex ordinate `γ = t − i(β − ½)`, so `h` must be analytic in `|Im r| ≤ ½`; a
function given only on the real line has no canonical value there.

This node never puts a function on the zero side. The primitive object is `g` on
the **prime** side, and `weilKernel g s = ∫ g(u) e^{(s−½)u} du` is one Bochner
integral of a compactly supported continuous integrand, defined by the same formula
at every `s ∈ ℂ`. The value at an off-line zero is literal, not a continuation.
That is exactly the E8 class and the E8 memo's §2.3 defence; this node inherits it.

Two further refutation traps from the roadmap, and how the statement avoids them:

* **PNT growth (§1 of the roadmap).** `primeSide` pairs the `Λ(n)n^{−1/2}` comb
  with a compactly supported test function, so it is a finite sum. No temperedness
  of any comb is asserted.
* **All-height claims in disguise.** The statement never quantifies the ladder
  hypothesis over all `T` (that would be RH ⇒ Weil positivity, the trivial
  direction of the wall — refused), and it does not claim `W ≥ 0` for tests with
  certified support `2L ≤ log 2` (that is B9, an all-height claim in disguise).
  Every claim is indexed by a height and degrades as `T → ∞` exactly as the
  instrument does.

**What this node is compatible with.** An off-line zero whose signal enters only
beyond any fixed height (roadmap §1). The node *measures reach*; it does not
approach a wall.

---

## 3. Vocabulary

`MMDefs.lean` is the hand-authored vocabulary mirror (not a generated statement
file: it carries no `DO NOT EDIT` header and no sha256, unlike the per-node files,
which were produced only by `telperion mission add`). Two blocks were added.

**MIRROR block `WeilExplicit`** — the six E8 definitions carried **verbatim** from
`missions/rh/lean/Statements/RHDefs.lean` (branch `rh/e8-statement`, v4.34), which
`examples/rvm_bridge/lean/E6Bridge4.lean` (v4.33.0-rc2) also mirrors verbatim:
`IsWeilTest`, `weilKernel`, `zeroMult`, `archIntegrand`, `archSide`, `primeSide`.
Carrying them verbatim at v4.32 is what makes a future cross-island grant possible
(the gate is normalized containment), and it is what the work item's risk note
demands for `zeroMult`. All six elaborate unchanged at v4.32.0 (`Complex.digamma`,
`MeromorphicOn.divisor`, `ArithmeticFunction.vonMangoldt` are all present at that
pin); the island builds.

**AUTHORED block `MMWeil`** — three definitions:

```lean
noncomputable def autocorr (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => ∫ v : ℝ, g (u + v) * (starRingEnd ℂ) (g v)

noncomputable def weilForm (f : ℝ → ℂ) : ℂ :=
  WeilExplicit.archSide f - WeilExplicit.primeSide f

noncomputable def zeroSideBelow (f : ℝ → ℂ) (T : ℝ) (ρ : ℂ) : ℂ :=
  if |ρ.im| ≤ T then (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel f ρ else 0
```

`autocorr g` is `g ⋆ g̃` with `g̃(u) = conj(g(−u))`, written as the correlation
integral. The transform factors (computed by Fubini on the compactly supported
integrand):

```
H_{autocorr g}(s) = H_g(s) · conj (H_g (1 − conj s)),
```

so on `Re s = ½` (where `1 − conj s = s`) it is `‖H_g(s)‖²` — the on-line square
channel, the `emit_unit_modulus_sos` shape — and off the line it is the pairing of
`ρ` with its functional-equation partner `1 − ρ̄`, which is exactly where positivity
is lost. `weilForm` is Weil's functional read off the primes side; by E8
(`RH_limit_explicit_formula`, proved on the rvm_bridge island) it equals the
zero-side sum, which is what makes the node's two sides comparable at all.

---

## 4. Decisions

**(1) Quantifier order: `∃ C, ∀ T`, with the unconditional conjuncts hoisted.**
`C` depends on `g` only. The hoisting is what defeats the collapse of §1: the
classical case split can make the *implication* cheap only where the hypothesis
fails, and the hoisted conjuncts must hold there too.

**(2) Hypothesis spelling: the ladder in its artifact shape.**
`∀ ρ, zeroMult ρ ≠ 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1/2`. This matches the
conclusion of `AllZeros_h100.lean` (`∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100 → ρ.re = 1/2`)
after one seam, so the ladder artifacts can discharge it. **The seam, pinned:**

```lean
-- E6Bridge4.zeroMult_eq_zero_of_not_nontrivial (contrapositive):
--   zeroMult ρ ≠ 0 → riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
```

i.e. `WeilExplicit.zeroMult` is supported on the nontrivial zeros, so a ladder
statement about `riemannZeta ρ = 0` in the strip implies the `zeroMult` form. The
alternative (symmetric `|ρ.im| ≤ T` hypothesis) was **rejected**: discharging it
from the artifacts would additionally require ruling out a real zero in `(0,1)`,
which Mathlib v4.32 does not have, so the node would be un-dischargeable by the
very ladder it is about.

The cost of this choice is that the *prover* of the node owes two unconditional
classical inputs, named here so a later session does not discover them by surprise:

* conjugate symmetry `riemannZeta (conj s) = conj (riemannZeta s)` — **available**
  (`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458`), to move the hypothesis from
  `0 < Im ρ ≤ T` to `|Im ρ| ≤ T` for `Im ρ ≠ 0`;
* `ζ(σ) ≠ 0` for real `σ ∈ (0,1)` — **not in Mathlib v4.32** (classical, via
  `ζ(s) = η(s)/(1 − 2^{1−s})` with `η > 0` on the real segment). Needed only for
  the `Im ρ = 0` slice of the truncated sum.

**(3) The constant stays existential.** Exposing `C_g = e^{R/2} ∫|g''|` times an
RvM constant waits for the effective-constant corridor/RvM forms, per the work
item. Note the `∃ C` is *not* a triviality here (§1): the hoisted conjuncts are
uniform in `T`, so `C` cannot be chosen after the fact.

**(4) Exponents: `T³` for the tail, `T` for the headline face.** The estimate gives
`T³`: two integrations by parts give `|H_g(ρ)| ≤ C_g/|ρ − ½|²`, hence
`|H_{autocorr g}(ρ)| ≤ C_g²/|ρ − ½|⁴ ≤ C_g²/t⁴`, and
`Σ_{|t|>T} m(ρ)/t⁴ = 4∫_T^∞ N(t) t^{−5} dt = O(log T / T³)` from
`N(t) ≤ A t log t` (`RH_rvm_unconditional`, proved). The headline conjunct is
registered at the safe exponent 1 (`log T / T`), which follows from the other two
since `T ≥ 2`; it is the citable face for consumers and is robust if the `T³`
constant chase is later refined. The redundancy is deliberate and documented.

**(5) `T ≥ 2`.** Safe: `N(2) = 0`, and the hypothesis is satisfiable at `T = 100`
(kernel, ZZL island) and `T = 640000` (climb), so the implication is not vacuous.

**(6) `IsWeilTest (autocorr g)` is a hypothesis, not a claim.** It is a classical
convolution fact (smoothness and compact support are preserved), but it is not in
the corpus, so it is carried explicitly rather than smuggled in. It is satisfiable
(probe 11 proves the degenerate case `IsWeilTest (autocorr 0)`); the non-degenerate
case is the named seam, routed through Mathlib's `HasCompactSupport`/`ContDiff`
convolution lemmas.

**(7) Deps.** The work item proposed `[MM_weil_gram_trace, MM_rvm_unbounded_mean_density]`.
`MM_weil_gram_trace` **does not exist**: D2 (the primes-side Weil–Gram matrix) is
still in the authoring queue, and the roadmap's skeptic correction (the bridge has
no archimedean term) is precisely why. The registered deps are therefore
`MM_rvm_unbounded_mean_density` (the count input, proved) and `MM_rect_trace_reading`
(D1, the registered ancestor of the D1 → D2 → D3 chain). When D2 is authored, this
node's dep list should gain it.

---

## 5. New tool built for this pass: the `bounded_hypothesis_collapse` emitter

`src/telperion/emit_bounded_hypothesis_collapse.py` (kind
`bounded_hypothesis_collapse`; dispatch in `certify.py`; stance in
`emitter_sensitivity.py` as `CERTIFICATE_SENSITIVE` +
`NEG_CONTROL_DECLARED_UNWIRED`; exercised by `tests/test_bounded_hypothesis_collapse.py`;
dogfooded and manifest-registered as the `shape_audit` check in `telperion.toml`).

It is a **triviality certificate for a statement shape**, a category the registry
did not previously have: given an audited shape
`∃ C ≥ 0, ∀ T ≥ T₀, P T → −(C log T / T^k) ≤ W`, it emits the Lean theorem that the
explicit constant `max 0 (−W) · B^k / log T₀` closes it for every `W`, every `P`
and every finite failure height `B ≥ T₀`. The constant lives in the emitted
*statement*, so it is the corruptible certificate: a wrong exponent, base or factor
breaks the proof.

Refusals (negative controls, all at certify time, all unit-tested): `k ≤ 0` (no
decay — not this family); `T₀ ≤ 1` (`log T₀ ≤ 0`); `B < T₀` (the hypothesis range is
empty, i.e. *vacuity*, a different defect, named rather than folded in); `W ≥ 0`
(collapse by `C := 0`, the benign route); a probe height outside `[T₀, B]`; no
samples at all.

Frozen output: `examples/shape_audit/frozen/ShapeAudit.lean` (2 witnesses, input
hash `e60369f39226c4f8`, 5 generation-time self-checks), instantiated at the D3
shape `(T₀, k) = (2, 1)` and at `(2, 3)` to show the collapse is not an artifact of
the weak exponent. Adversarial samples include the ladder's real certified heights
(`B = 640000`, `T = 100`).

Honesty line carried in the emitter, the emitted Lean and the example: **it refutes
a sentence, never a theorem.** It says nothing about whether the intended
inequality is true.

---

## 6. Trivial-close probes (run, not assumed)

Run with `lake env lean` against the built `Statements.MMDefs` at the island pin
`leanprover/lean4:v4.32.0` (Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`).
Probes 1–8 must leave goals open; 9–11 must succeed.

| probe | tactic / claim | result |
|---|---|---|
| 1 | `simp [weilForm, autocorr, zeroSideBelow, zeroMult, weilKernel, archSide, primeSide]` | **unsolved goals** (the full statement, terms unfolded) |
| 2 | `simp_all [weilForm, autocorr, zeroSideBelow, zeroMult]` | **unsolved goals** |
| 3 | `aesop (add simp [...])` | **fails**: `(deterministic) timeout at simp, maximum number of heartbeats (200000)` |
| 4 | `norm_num [...]` | **unsolved goals** |
| 5 | degenerate witness `C := 0`, `P := 0`, then `simp` | **fails**: `simp made no progress` on the `HasSum` goal; `case refine_3` left open (`⊢ (∀ ρ, ¬zeroMult ρ = 0 → …) → 0 ≤ (weilForm (autocorr g)).re`) |
| 5a | `HasSum (zeroSideBelow (autocorr g) T) 0` by `simp` | **fails**: `simp made no progress` |
| 5b | `‖weilForm (autocorr g) - 0‖ ≤ 0 * Real.log T / T ^ 3` by `simp` | **unsolved**: `⊢ weilForm (autocorr g) = 0` |
| 5c | ladder-conditional conjunct at `C := 0, P := 0` by `simp` | **unsolved**: `⊢ (∀ ρ, ¬zeroMult ρ = 0 → …) → 0 ≤ (weilForm (autocorr g)).re` |
| 6 | `zeroMult ρ = 0` by `simp [zeroMult]` | **unsolved**: `⊢ (MeromorphicOn.divisor riemannZeta {s | 0 < s.re ∧ s.re < 1}) ρ ≤ 0` |
| 7 | `zeroSideBelow f T ρ = 0` by `simp [zeroSideBelow]` | **unsolved**: `⊢ |ρ.im| ≤ T → zeroMult ρ = 0 ∨ weilKernel f ρ = 0` |
| 8 | `weilForm (autocorr g) = 0` by `simp [weilForm]` | **unsolved**: `⊢ archSide (autocorr g) - primeSide (autocorr g) = 0` |
| 9 | `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ⊤` | **proved** (the class is smooth, not analytic — an analytic compactly supported function is `0`, which would make the class `{0}`) |
| 10 | `∃ g, IsWeilTest g ∧ g ≠ 0` | **proved** (`ContDiffBump`, `rIn = 1`, `rOut = 2`) — the class is nonempty and not a singleton |
| 11 | `IsWeilTest (autocorr 0)` | **proved** — decision (6)'s hypothesis is satisfiable |

Nothing closes the statement; the statement was not changed by the probes. The
probe file is scratch (`MMD3TrivialClose.lean`), deliberately not committed into
`missions/` since it is expected to error by construction.

Hazard table (the junk-value audit):

| hazard | where | how the statement avoids it |
|---|---|---|
| `tsum` of a non-summable family is `0` | zero side | stated as `HasSum` with an explicit `∃ P`, so summability is part of the claim (probes 1–5) |
| the collapse of §1 | the whole shape | unconditional conjuncts hoisted out of the ladder implication; the collapse witness is kernel-checked so the failure mode is documented, not folded away |
| `zeroMult` simp-trivial | weight | probe 6 fails as required; same divisor expression as `RvMCount.zetaZeroCount` |
| `zeroSideBelow` simp-trivial | truncation | probe 7 fails as required |
| divisor negative at a pole hidden by `.toNat` | `zeroMult` | ζ's only pole is `s = 1`, outside the open strip |
| empty test class (vacuous `∀`) | `IsWeilTest` | probe 10 |
| `ContDiff ℝ ⊤` meaning analytic | `IsWeilTest` | index written `((⊤ : ℕ∞) : WithTop ℕ∞)`; probe 9 |
| unsatisfiable second hypothesis | `IsWeilTest (autocorr g)` | probe 11 (degenerate); non-degenerate case named as a seam |
| vacuous implication (no `T` satisfies the ladder) | ladder hypothesis | satisfiable at `T = 100` (kernel) and `T = 640000` (climb); `N(2) = 0` |
| the all-height collapse into RH ⇒ Weil positivity | quantifier placement | the ladder is never quantified over all `T`; §1 proves what that shape would be worth |

---

## 7. Consumers

* **D7** (evidence-grade operator vs. zero data): the `T³` conjunct is the error
  term to compare against; `P` is the finite object the data actually determines.
* **D11 finite face / B4 windows**: the headline face at a certified height.
* **D2**: when the Weil–Gram matrix statement is authored, `weilForm` and
  `archIntegrand` are its vocabulary; this node's dep list should then gain it.
* **The goal node's finite face**: this is the D-route's "what the ladder buys"
  measurement; it is *not* on a path to the wall (§2).
* **Effective-constant corridor / RvM**: this node is that item's first consumer —
  it is where an explicit `C_g` would land (decision (3)).

## 8. Certificate shape (for a later session)

Per-`g` numeric instances: a concrete bump, an Arb enclosure of `W(autocorr g)` and
of the certified partial sum `P` built from the ladder's ordinate enclosures — the
`tool-weil-form-enclosure` item. That tool does **not** exist yet (checked: no
`weil_form_enclosure` module in the tree); the shape-audit emitter built in this
pass is a different instrument and does not substitute for it. The theorem itself
is a Lean artifact for the rvm_bridge island (it consumes E8 and
`RH_rvm_unconditional`, both proved there at the v4.33.0-rc2 pin), which will need
the same verbatim `MMWeil` block mirrored there when it is attempted.

## 9. Status

`draft` (as `mission add` creates it). A blind read-back is required before it
becomes `open`; this session authored the statement and therefore did not run
`mission audit`. `mission verify mirrormere`: **OK**. The goal node
`MM_zeta_comb_membership` was not touched.
