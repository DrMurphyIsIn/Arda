# D2, the primes-side Weil-Gram matrix: design memo for `MM_weil_gram_trace`

*Authored 2026-09-18. Statement authored, **NOT proved**. The node is `draft`, its statement
file ends in the by-design `sorry`, and nothing here is evidence for or against RH.*
**`conjecture1_proved = False`.**

Routes-roadmap item D2 (`RH_ROUTES_ROADMAP_2026-09-16.md` section 5) is one line long —
"primes-side Weil-Gram matrix" — plus a skeptic's correction that killed the obvious
reading. This memo does the three things that had to happen before D2 could be registered:
it fixes the object (which matrix, built from what), it fixes the conjuncts (what is
asserted about it and, more importantly, what is *not*), and it shows the statement survives
the traps that a Gram-matrix statement invites. Sections 6 and 7 record checks that were
actually run, including one **correction to the work item's own proposed third conjunct,
which is false as written** (section 6, TRAP 4).

---

## 0. The statement (as registered)

Node `MM_weil_gram_trace`, kind `lemma`, deps `MM_rect_trace_reading`, `MM_bragg_bridge`,
`MM_offline_pairs_le_defect`. Vocabulary in the `WeilExplicit` block of
`missions/mirrormere/lean/Statements/MMDefs.lean` (section 2).

```lean
theorem weil_gram_trace (k : ℕ) (g : Fin k → ℝ → ℂ) (hg : ∀ i, IsWeilTest (g i)) :
    (weilGram g).IsHermitian ∧
    (∀ i j : Fin k,
      HasSum (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel (g i) ρ
          * (starRingEnd ℂ) (weilKernel (g j) (1 - (starRingEnd ℂ) ρ)))
        (weilGram g i j)) ∧
    (∀ (x : Fin k → ℂ) (G : ℝ → ℂ),
      G = (fun v => ∑ i, (starRingEnd ℂ) (x i) * g i v) →
      RHLinalg.hermForm (weilGram g) x
        = (archSide (crossCorr G G) - primeSide (crossCorr G G)).re) := by sorry
```

In classical notation, with `h_i(r) = ∫ g_i(u) e^{iru} du`, `H_i(s) = weilKernel (g i) s`,
`W(f) = archSide f - primeSide f` the Weil functional and `W_ij = W(g_i ⋆ g̃_j)`:

```
W = (W_ij) is Hermitian;
W_ij = Σ_ρ m(ρ) H_i(ρ) conj(H_j(1 - conj ρ));            (on the line: Σ_ρ m(ρ) h_i(γ) conj(h_j(γ)))
x* W x = W( autocorrelation of Σ_i conj(x_i) g_i )        (real, by Hermitian-ness)
```

D1 (`MM_rect_trace_reading`) read the **finite** Bragg bridge at one box as a trace identity.
D2 packages the **infinite-height** trace identity (E8, `RH_limit_explicit_formula`) as a
**finite Hermitian matrix** over a test family — the object the defect instrument
(`MM_offline_pairs_le_defect`) is able to read.

---

## 1. Why a matrix, and why this one

Three facts force the shape.

1. **The defect instrument eats matrices.** `offline_pairs_le_defect` is a statement about
   `Matrix n n 𝕜` with `NegativeWitness`/`posIndex`/`defect`. The Weil functional `W` is a
   functional on one test function; to hand it to the instrument one must first *compress* it
   to a finite family. The compression is the Gram matrix of the polarised functional, and
   Bombieri (2000, quoted in Alpöge-Furman §1.3/§7.1 and verified in
   `RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md` CLAIM 2) is exactly the statement that the
   negative index of such a finite compression counts the off-line pairs *seen by* it.

2. **Polarisation must be the cross-correlation, not any bilinear pairing.** Weil's positivity
   functional is `W(f ⋆ f̃)`, `f̃(u) = conj (f (-u))`; its polarisation in a family `{g_i}` is
   `W(g_i ⋆ g̃_j) = W(crossCorr g_i g_j)`. Any other pairing (for example `W(g_i · g_j)`, or a
   Gram of transform values at a fixed height) is not the object Weil's criterion is about and
   does not reduce to the autocorrelation on the diagonal.

3. **The archimedean term is not optional** (the roadmap D2 skeptic's correction, carried
   verbatim in the work item's risk field). `rect_explicit_formula_bragg` is stated for the
   *uncompleted* `ζ` with edge remainders and therefore has **no** `Γ` term. Building a Gram
   from `braggTerm` would give a matrix that is neither Hermitian nor the Weil form: the
   missing `Re ψ` density is precisely the piece that makes `crossCorr g₂ g₁ u = conj (crossCorr
   g₁ g₂ (-u))` propagate to `W_ji = conj (W_ij)`. The memo's `archSide` carries that integral
   (`archIntegrand` is the registry's named archimedean object, authored for E8 on
   2026-09-18), which is why D2 is built on E8's vocabulary and not on W3b's.

---

## 2. Vocabulary: the `WeilExplicit` block of `MMDefs.lean`

`MMDefs.lean` is the registry's hand-authored vocabulary mirror (it carries no generated
`DO NOT EDIT` header and is not a node statement; the generated statement files' headers were
not touched). The block added for D2 has two halves.

**Mirrored verbatim (six definitions)** from the AUTHORED `WeilExplicit` block of
`missions/rh/lean/Statements/RHDefs.lean` on branch `rh/e8-statement` — `IsWeilTest`,
`weilKernel`, `zeroMult`, `archIntegrand`, `archSide`, `primeSide`. They are copied character
for character, with a comment saying so, so that a future `examples/rvm_bridge/generate.py`
drift check (the `E6Bridge4` pattern, which already compares the rh registry's block with the
island's mirror) can compare the two registries' blocks directly. **Re-word them in
`RHDefs.lean` and re-mirror; never re-word them here.**

**Authored for D2 (two definitions).**

```lean
noncomputable def crossCorr (g₁ g₂ : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, g₁ v * (starRingEnd ℂ) (g₂ (v - u))

noncomputable def weilGram {k : ℕ} (g : Fin k → ℝ → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => archSide (crossCorr (g i) (g j)) - primeSide (crossCorr (g i) (g j))
```

Two facts fix `crossCorr`'s normalisation; both are theorems on the proof island, neither is
hypothesised in the node:

* **reflection-conjugation**: `crossCorr g₂ g₁ u = conj (crossCorr g₁ g₂ (-u))` (substitute
  `v ↦ v + u`). This is the whole content of conjunct 1 — see section 3.
* **kernel factorisation**: `weilKernel (crossCorr g₁ g₂) s = weilKernel g₁ s * conj (weilKernel
  g₂ (1 - conj s))` (Fubini on compact supports). Derivation: substitute `w = v - u` in
  `∫_u ∫_v g₁(v) conj(g₂(v-u)) e^{(s-1/2)u} dv du` to get
  `[∫ g₁(v) e^{(s-1/2)v} dv] · [∫ conj(g₂(w)) e^{-(s-1/2)w} dw]`, and the second factor is
  `conj (∫ g₂(w) e^{((1 - conj s) - 1/2) w} dw)` because `-(conj s - 1/2) = (1 - conj s) - 1/2`.
  This is what conjunct 2 reads.

`crossCorr g g` **is** the Weil autocorrelation `autocorr g` of the positivity vocabulary
(`f ⋆ f̃`), definitionally, so the diagonal `weilGram g i i` is the Weil form of an honest
autocorrelation. It is spelled through `crossCorr` in the node rather than through an
`autocorr` alias (decision 4, section 5).

---

## 3. Why Hermitian-ness costs nothing (and why that matters)

`W_ji = conj (W_ij)` follows from the **primes side alone**. Write `f̃(u) = conj (f (-u))`;
then term by term:

| term of `W(f̃)` | value |
|---|---|
| `primeSide f̃ = Σ Λ(n)/√n (conj f(-log n) + conj f(log n))` | `conj (primeSide f)` (`Λ(n)/√n` real) |
| `weilKernel f̃ s = ∫ conj(f(-u)) e^{(s-1/2)u} du` | `conj (weilKernel f (1 - conj s))`, so the pole pair `weilKernel f̃ 0 + weilKernel f̃ 1` is `conj` of itself swapped |
| `f̃(0) log π` | `conj (f 0) log π` (`log π` real) |
| `archIntegrand f̃ r` | `conj (archIntegrand f r)` (since `1 - conj(1/2 + ir) = 1/2 + ir`, and `Re ψ` is real) |

Hence `W(f̃) = conj (W f)`, and with the reflection-conjugation identity
`crossCorr g₂ g₁ = (crossCorr g₁ g₂)~`, `W_ji = conj (W_ij)`.

**No zero symmetry is used.** In particular the statement does not need `zeroMult (1 - conj ρ)
= zeroMult ρ` (which is the functional equation plus conjugate symmetry) and does not need any
zero to be on the line. This is deliberate: an auditor can confirm conjunct 1 without granting
anything about zeta's zeros, and a future reader cannot mistake Hermitian-ness for a
zero-distribution fact. It is also the reason the third conjunct is *meaningful*: `hermForm`
is real-valued by definition, but here the matrix really is Hermitian, so the form is the
honest quadratic form and not a projection of a non-Hermitian object.

---

## 4. The trace conjunct: what genuine zeta data enters

Conjunct 2 is E8 applied to `crossCorr (g i) (g j)`, rewritten through the kernel
factorisation. Three things are worth stating plainly.

* **The index set is all of `ℂ`.** As in E8, the `HasSum` runs over `ρ : ℂ` with the registry
  weight `zeroMult ρ`, which vanishes off the open critical strip and at non-zeros. The
  alternative — summing over a carrier subtype `{ρ | IsNontrivialZero ρ}` — was rejected
  (decision 3): the weight already does that work, and a subtype index would force every
  consumer to transport along `hasSum_subtype_iff_of_support_subset` (exactly the seam
  `E6Bridge4` had to build for E8).
* **Off-line zeros are seen literally.** `weilKernel g` is one Bochner integral of a compactly
  supported continuous integrand, defined by the same formula at every `s ∈ ℂ`; at an off-line
  zero `ρ = β + it` the summand is `h_i(γ) conj(h_j(γ))` with the *complex* ordinate
  `γ = t - i(β - 1/2)`. No analytic continuation is invoked, which is the Paley-Wiener
  obstruction (roadmap D3) being sidestepped by the coordinate choice, not evaded.
* **On the line the summand is a rank-one Gram entry.** For `ρ = 1/2 + iγ` with `γ` real,
  `1 - conj ρ = ρ`, so the summand is `m(ρ) h_i(γ) conj(h_j(γ))` and the `ρ`-th contribution to
  the whole matrix is `m(ρ)` times a rank-one positive semidefinite block. Off-line zeros come
  in pairs `{ρ, 1 - conj ρ}` and contribute a signature-`(1,1)` block — Alpöge-Furman item (Z).
  **That reading is not a conjunct**; it is what D3/D7 are for.

---

## 5. Decisions

1. **`Fin k` rather than an arbitrary `Fintype`.** `Fin k` carries `Fintype` and `DecidableEq`
   definitionally, keeps the emitter instances simple (the certificate tools of section 8 index
   entries by `(i, j)` integers), and loses nothing: any finite family reindexes.
2. **Complex Hermitian rather than real symmetric.** The instruments' `RHLinalg` block is
   `RCLike`-generic and `hermForm`/`posIndex`/`defect` are stated over `𝕜`; the test class is
   complex-valued with no evenness hypothesis (E8 memo section 3.4), so a real-symmetric
   restriction would need a separate parity lemma and would exclude the odd imaginary parts
   that Weil's `f ⋆ f̃` produces.
3. **`HasSum` over `ℂ`, not over a carrier subtype.** See section 4.
4. **`crossCorr G G`, not an `autocorr` alias.** The Weil-positivity item ("item 1" of the D2
   work batch) authors `autocorr g u = ∫ g v * conj (g (v - u))` in the same `WeilExplicit`
   block; `crossCorr g g` is that function *definitionally*, so this node's third conjunct is
   normalisation-compatible with it while not depending on which branch lands first. **Merge
   seam:** when both branches land, `autocorr` should be added once as
   `noncomputable def autocorr (g : ℝ → ℂ) : ℝ → ℂ := crossCorr g g` and this node left
   unchanged (its statement hash covers the `crossCorr` spelling).
5. **The third conjunct is included** (the work item made it optional). It is the only conjunct
   that mentions `RHLinalg.hermForm`, hence the only one a defect-instrument consumer can use
   without re-deriving polarisation; and it is what makes the goal-node reading of section 9
   expressible. Its cost is bilinearity of `archSide`/`primeSide`, which is finite-sum and
   linear-integral bookkeeping.
6. **`IsWeilTest (crossCorr (g i) (g j))` is NOT a conjunct and NOT a hypothesis.** It is a
   theorem (`crossCorr_isWeilTest`, proof island) needed by conjunct 2 anyway; as a hypothesis
   it would open a vacuity hole (section 6, TRAP 1), and as a conjunct it would add nothing an
   auditor cannot read off the proof.
7. **No inertia conjunct.** `posIndex (weilGram g) = k`, `defect (weilGram g) = 0`, or any
   positivity of `hermForm` is *absent by design*: for all `g` that is Weil's criterion and
   therefore RH (roadmap B10/D11); for one `g` it is numeric data for the instruments
   (section 8). Putting either in the statement would either make the node RH-hard or make it a
   disguised data claim.

---

## 6. Traps: how the statement could be trivially true, false, or empty

| # | hazard | where it bites | how the statement avoids it | checked by |
|---|---|---|---|---|
| 1 | junk Bochner integrals (`∫` of a non-integrable function is `0`) | `archSide`/`primeSide` at `crossCorr` | `crossCorr` of two `C_c^∞` functions is `C_c^∞` (support in `supp g₁ - supp g₂`, smoothness from `HasCompactSupport.contDiff_convolution_*`), a THEOREM — and it is not hypothesised, so a vacuous instantiation cannot satisfy the node | section 5 decision 6; probes 1-4 leave the goal open |
| 2 | `tsum` of a non-summable family is `0` | zero side | conjunct 2 is `HasSum`, so summability is part of the claim | probes 1-4 |
| 3 | `zeroMult ≡ 0` collapse | zero side | `simp` cannot reduce `zeroMult`; note the collapse would make conjunct 2 assert `weilGram = 0`, i.e. make the node **false**, not vacuous | probe 7 (fails, as required) |
| 4 | **the conjugation convention in the quadratic-form conjunct** | conjunct 3 | see below — the work item's proposed form is FALSE; the registered form conjugates the coefficient vector | section 6a + probe battery |
| 5 | `k = 0` as a "witness" | whole statement | true and contentless (empty matrix, empty sums); the node deliberately states nothing extra at `k = 0` | probe 10 (proves the empty instance, so it cannot be mistaken for evidence) |
| 6 | empty test class (vacuous `∀`) | `IsWeilTest` | the class contains a nonzero function | probe 8 (proves `∃ g, IsWeilTest g ∧ g ≠ 0`) |
| 7 | `ContDiff ℝ ⊤` meaning *analytic*, collapsing the class to `{0}` | `IsWeilTest` | index is `((⊤ : ℕ∞) : WithTop ℕ∞)` | probe 9 |
| 8 | Hermitian-ness smuggling in zero symmetry | conjunct 1 | proved on the primes side alone (section 3) | section 3 table |
| 9 | a Gram built from the finite Bragg comb | the whole object | `weilGram` is built from `archSide`/`primeSide`, which carry the `Re ψ` integral; `braggTerm` is not mentioned | section 1 item 3 |
| 10 | an inertia claim sneaking in | conjuncts | none present (decision 7) | by inspection; the certificate tools of section 8 also refuse to emit `PosDef`/`posIndex`/`defect` |
| 11 | entrywise `simp` closing the matrix | conjunct 1 | fails | probes 5, 6 |

### 6a. TRAP 4 in detail — a correction to the work item

The work item proposed the third conjunct as

```
∀ x, hermForm (weilGram g) x = (weilForm (autocorr (fun u => ∑ i, x i * g i u))).re
```

**That identity is false in general.** `hermForm A x = Re (∑_{i,j} conj(x_i) A_ij x_j)`, while
`crossCorr` is conjugate-linear in its *second* argument, so

```
autocorr (∑_i a_i g_i) = ∑_{i,j} a_i conj(a_j) crossCorr(g_i, g_j),
```

and `W` being linear, `W(autocorr (∑ a_i g_i)) = ∑_{i,j} a_i conj(a_j) W_ij`. Matching that
with `∑_{i,j} conj(x_i) W_ij x_j` forces `a_i = conj(x_i)`, not `a_i = x_i`. Both quantities are
real when `A` is Hermitian, so the error does not show up as a type error or a complex residue;
it shows up as a **sign/conjugation twist**. Concretely with `k = 2`,
`A = [[0, i], [-i, 0]]` (Hermitian) and `x = (1, i)`:

```
∑ conj(x_i) A_ij x_j = -2,   ∑ x_i conj(x_j) A_ij = +2.
```

So the two readings differ by a sign on that vector, and the work item's version of the
conjunct would have registered a statement that no proof can close. The registered conjunct
uses `G = fun v => ∑ i, conj (x i) * g i v`, which is the identity that actually holds; the
`∀ G, G = … →` spelling is a named abbreviation (logically `P(expr)`) that keeps the statement
readable without repeating the combination four times.

Sanity check at `k = 1`: `G = conj(x₀) g₀`, `crossCorr G G = |x₀|² crossCorr g₀ g₀`, so the
right side is `|x₀|² Re W₀₀`, and `hermForm A x = |x₀|² Re A₀₀`. Equal.

### 6b. Trivial-close probe results

Probe module `missions/mirrormere/lean/Probes/MMWeilGramTraceProbes.lean` — **outside
`defaultTargets`**, no `sorry`, no node statement. Every probe is a *kernel-checked record*:
the negative ones are `fail_if_success` blocks, so the file compiles only while the tactic
really does fail. Built with `lake build Probes` at `leanprover/lean4:v4.32.0`; **the whole
`Probes` library builds clean, zero warnings**.

| probe | content | result |
|---|---|---|
| 1 | `simp` with all eight definitions unfolded, on the full statement | does not close |
| 2 | `simp_all [...]` | does not close |
| 3 | `aesop (add simp [...])` | does not close |
| 4 | `norm_num [...]` | does not close |
| 5 | `(weilGram g).IsHermitian` by `simp [weilGram, crossCorr, archSide, primeSide, Matrix.IsHermitian]` | does not close |
| 6 | `weilGram g i j = 0` by `simp [...]` | does not close |
| 7 | `zeroMult ρ = 0` by `simp [zeroMult]` | does not close |
| 8 | `∃ g, IsWeilTest g ∧ g ≠ 0` | **proved** (a `ContDiffBump (0 : ℝ)` with `rIn = 1`, `rOut = 2`, composed with `ofRealCLM`; non-vacuity of the hypothesis) |
| 9 | `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞)` | **proved** by `decide` (the smoothness index is `C^∞`, not `ω`) |
| 10 | `(weilGram g).IsHermitian` for `g : Fin 0 → ℝ → ℂ` | **proved** (the `k = 0` instance is true and contentless) |
| 11 | the section-9 goal-node proposal, by `simp` | does not close |

The statement was not changed by the probes (the correction of section 6a was found by hand
before the node was authored, and is recorded here because it changes the work item's spec).

---

## 7. Consumers

* **D3** (Weil positivity below a certified height, reformulated): needs the identity on the
  strip-analytic admissible class in `g`-coordinates; D2 gives it the compression object.
  Positivity stays D3's problem.
* **D7** (evidence-grade finite-rank operator vs zero data): consumes the Gram matrix directly
  — the matching is between `weilGram` inertia data and computed zero data, and the
  certificate tools of section 8 are what make that comparison kernel-legible.
* **D8** (Hermite-Biehler finite dictionary): consumes the diagonal entries.
* **D10** (certified GUE pair correlation): consumes the rank-one-per-on-line-zero reading of
  section 4.
* **A2c / T3** (defect instrumentation on genuine zeta data): the composite
  `weilGram` → `NegativeWitness` → `offline_pairs_le_defect` / `defect_eq_offline_pairs` is
  Bombieri's "off-line pairs seen by the truncation" reading, now with a concrete truncation.
* **B4** (windows) and the goal node: section 9.
* Certified-height bounds (D3's numeric half) use the diagonal entry `weilGram g i i`, which is
  the Weil form of an honest autocorrelation by decision 4.

---

## 8. Certificate shape, and the two tools built for it

The identity itself is a Lean theorem (proof island `examples/rvm_bridge`, v4.33.0-rc2, where
E8 already lives as `E6Bridge4.limit_explicit_formula`; grant would be cross-island, the
`E6Bridge`/`dlvp` precedent). The *numbers* are a different matter, and the work item named two
tools that did not exist. Both were built in this change, with unit tests
(`telperion/tests/test_weil_gram_certs.py`, 14 tests) and a compiled Lean sample.

### 8.1 `weil_form_enclosure` (`src/telperion/emit_weil_form_enclosure.py`)

**The missing shape:** every existing Telperion enclosure emitter certifies a single scalar
rung (`bragg_floor`, `li_positivity_ladder`, `enclosure_interval_fold`); none folds a *signed,
multi-component* analytic functional — an archimedean part minus an exactly-finite prime part —
into one certified rational interval. That fold is what a Gram entry is.

Emits two theorems per entry:

1. the **prime-side fold** as an exact rational identity (`norm_num`): the claimed endpoints
   *are* the sum of the supplied per-prime-power term endpoints, spelled out. Corrupt an
   endpoint and the kernel rejects it — this is the certificate-sensitive half;
2. the **entry enclosure** (`linarith`): for every real `arch` in the certified archimedean
   interval and every real `prime` in the folded interval, `lo ≤ arch - prime ≤ hi`.

Refusals (checked in tests): inverted interval anywhere; an **incomplete prime-power list** for
the declared support radius `R` (an omitted in-range `n` makes the finite-sum claim *false*, not
merely loose — `supp (crossCorr g₁ g₂) ⊂ [-R, R]` gives exactly the `n ≤ e^R`, and
`Λ(0) = Λ(1) = 0`); non-positive `R`; a supplied fold disagreeing with the re-derivation.

Trust seam, stated in the emitted comment: the archimedean interval (the two pole terms, the
`-f(0) log π` term and the digamma integral, enclosed as **one** Arb interval) and each
`Λ(n)/√n (f(log n) + f(-log n))` term come from Arb (python-flint). The kernel checks the fold
and the implication, never the analysis — the `BraggFloor` / Li-ladder posture.

### 8.2 `interval_gram_inertia` (`src/telperion/emit_interval_gram_inertia.py`)

**The missing shape:** `RayleighGramEmitter` reads a Gram form at *exact* rational entries;
`EnclosureIntervalFoldEmitter` folds enclosures but reads no inertia. Nothing could read the
inertia of a Hermitian matrix whose entries are known only as *intervals* — which is the only
way a Weil-Gram matrix is ever known.

The key observation making this kernel-cheap: for a Hermitian `A` with `A i i = a_ii` real and
`A i j = a_ij + i b_ij` (`i < j`), and a rational complex witness `x`,

```
hermForm A x = Σ_i |x_i|² a_ii + Σ_{i<j} ( 2 Re(conj(x_i) x_j) · a_ij  −  2 Im(conj(x_i) x_j) · b_ij ),
```

a **linear** functional of the entry data with rational coefficients. Two modes:

* `negative`: maximise that functional over the entry box in exact rational arithmetic; if the
  maximum is `< 0`, emit `⟨the linear form⟩ ≤ box_max` from the box hypotheses by `linarith`.
  Reading: every Hermitian matrix in the enclosure has a negative direction, so `1 ≤ defect`
  via `NegativeWitness.ofNegDir` + `offline_pairs_le_defect`. **On genuine zeta data this is the
  falsifiability face** — it is not expected to fire, and it exists so the instrument could.
* `dominance`: per off-diagonal a rational modulus bound (`a_ij² + b_ij² ≤ m_ij²`, from the box,
  by `nlinarith`) plus the constant row inequalities `Σ_{j≠i} m_ij < dLo_i`. Reading (stated in
  the comment, **not emitted as a claim**): strict Hermitian diagonal dominance with positive
  diagonal is positive definiteness, so this enclosed family has `defect = 0`.

The emitter **never emits `Matrix.PosDef`, `posIndex` or `defect`**: the dominance → PosDef
lemma belongs to the consuming island's `RHLinalg` prelude, and `defect = 0` for one family is
data while for every family it is RH. Refusals: zero witness; a box whose maximum is `≥ 0`
("the instrument says it sees no off-line pair here" — an honest refusal, never a false
theorem); non-positive diagonal lower bound; a row whose modulus budget does not clear it; a
missing off-diagonal enclosure; an unknown mode.

### 8.3 Wiring, and what is deliberately left undone

Both are registered in `certify._SPECIAL_KINDS` / `_SPECIAL_DISPATCH`, exported from
`telperion/__init__.py`, and classified in `emitter_sensitivity.REGISTRY`
(`WeilFormEnclosureEmitter` = `certificate_sensitive` with `checked_in=None`;
`IntervalGramInertiaEmitter` = `structurally_nonvacuous`; both
`NEG_CONTROL_DECLARED_UNWIRED` — the honest state: a forged certificate *is* kernel-rejected,
but no adapter exists yet in `negative_control_harness.ADAPTERS`). The emitted Lean was
compiled against Mathlib at the mirrormere pin: samples for all three shapes (fold + enclosure,
`k = 3` negative direction, `k = 3` dominance) are in
`missions/mirrormere/lean/Probes/MMWeilGramCertSamples.lean`, regenerable by
`Probes/regen_samples.py`, and **`lake build Probes` is clean**.

**Not done, and named rather than papered over:** no `examples/<name>/generate.py` harness, no
`telperion.toml` `[[check]]` entry, no `<name>-compiles` CI job, no README "Certificate shapes"
row (that table's preamble promises a CI-compiled example for every row, so a row would be a
false claim today), and no `negctrl_adapters/` adapter. Those five are the remaining wiring for
these two kinds, and they need a Lean island of their own — which in turn wants the real Arb
data, i.e. the D3/D7 numeric campaign, not this statement-authoring pass.

---

## 9. The goal node `MM_zeta_comb_membership` — proposal only

The goal node's registered statement is the **flagged placeholder** `RiemannHypothesis`
(`Statements/MM_zeta_comb_membership.lean`), and per the work item its status, statement and
file are **unchanged by this pass**. What D2 adds is that the D-route half of the replacement
is now expressible in registry vocabulary:

```lean
def GoalProposal : Prop :=
  ∀ (k : ℕ) (g : Fin k → ℝ → ℂ), (∀ i, IsWeilTest (g i)) →
    ∀ (x : Fin k → ℂ), 0 ≤ RHLinalg.hermForm (weilGram g) x
```

("no finite Weil-test family has a negative direction"). By Weil's criterion — positivity of
`W` on all of `C_c²(ℝ)`, Alpöge-Furman §1.2 — together with the polarisation of conjunct 3,
this is RH-equivalent; it is *not* proved, *not* claimed, and it is recorded here only because
it makes the D2 instrument's honest scope legible: `GoalProposal` for ONE family is data, for
ALL families it is the wall. Probe 11 records that `simp` does not close it.

This does **not** settle the W3c authoring problem the goal node actually names (the concrete
Selberg-class / B-mult-twisted growth-carrier membership form): `GoalProposal` is a Route-B/D
sentence, the goal node is a Route-A sentence, and merging them is its own authoring job. It is
offered as a *candidate second conjunct or cross-check*, not as the replacement.

---

## 10. Registry mechanics done in this change

* `telperion/missions/mirrormere/nodes/MM_weil_gram_trace.toml` and
  `lean/Statements/MM_weil_gram_trace.lean` written by `telperion mission add` (generated
  `sha256` header, never hand-edited); `lean/Statements.lean` imports the new module.
* `lean/Statements/MMDefs.lean` gains the `WeilExplicit` block (section 2). `MMDefs` is the
  hand-authored mirror, not a generated statement file; no generated header was touched.
* `lean/lakefile.toml` gains a `Probes` `lean_lib` **outside `defaultTargets`** plus
  `lean/Probes.lean`; `lake build` still builds only the statements.
* `lake exe cache get` (allowed once here — no cache existed for this island) then
  `lake build`: success, the only warnings are the by-design `sorry`s on the 20 statement files
  and the pre-existing flagged support `sorry` in `MMDefs`. `lake build Probes`: clean.
* `telperion mission verify mirrormere`: **OK**.
* `telperion mission attempt MM_weil_gram_trace …`: recorded, verdict `Stalled` (authored, not
  proved).
* Not done, by instruction: no proof, no push, no PR, **no `mission audit`** (blind read-back
  is the next gate, and the node stays `draft` until it passes).

**`conjecture1_proved = False`.**
