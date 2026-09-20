# W2b quadruple audit — what one functional-equation quadruple actually costs in defect

*2026-09-19. Artifact: `telperion/examples/zeta_zero_localization/lean/QuadrupleDefect.lean`
(kernel-clean, `[propext, Classical.choice, Quot.sound]`, guarded in `AxiomGuardDefect.lean`).
`conjecture1_proved = False`.*

This closes the two skeptic caveats standing against the MIRRORMERE W2b cluster in
`RH_ROUTES_ROADMAP_2026-09-16.md` — the **quadruple caveat** (Route A §2) and the **A2a
synthetic-2×2 caveat** — and it corrects the advertised reading of a proved node.

---

## 1. The question, and the answer

> A genuine off-line zero of ζ at ρ forces three companions by the functional equation and by
> reflection: `1−ρ`, `conj ρ`, `1−conj ρ`. If the defect functional counts PAIRS, what does one
> genuine off-line zero actually cost in defect?

**Answer, in two parts, both kernel-checked.**

**(a) The pair count is exactly 2.** `DefectDictionary`'s counter `p` counts orbits of the
involution `σ ρ = 1 − conj ρ` (reflection across the critical line) — *not* zeros and *not*
quadruples. `QuadrupleDefect.offline_quadruple_sigma_pair_count` proves that for `re ρ ≠ 1/2` and
`im ρ ≠ 0` the quadruple `{ρ, 1−ρ, conj ρ, 1−conj ρ}` has **four distinct members** and splits into
**exactly two disjoint σ-orbits**, `{ρ, 1−conj ρ}` and `{conj ρ, 1−ρ}`. So **one genuine off-line
zero costs `p = 2`**.

Both degenerations are kernel-checked too, because nothing in `DefectDictionary` excludes them:

| case | quadruple | σ-orbits (`p`) | theorem |
|---|---|---|---|
| `re ρ ≠ 1/2`, `im ρ ≠ 0` (genuine) | 4 points | **2** | `offline_quadruple_sigma_pair_count` |
| `re ρ ≠ 1/2`, `im ρ = 0` (real off-line) | 2 points `{ρ, 1−ρ}` | **1** | `quad_real_offline` |
| `re ρ = 1/2` (on-line) | 2 points `{ρ, conj ρ}`, both σ-fixed | **0** | `quad_online`, `quad_online_card` |

**(b) The witness dimension is NOT determined by the quadruple.** It is `dim span {y₁, y₂}`, the
rank of the imaginary-channel span, which is **1 or 2**. `quadruple_witness_dimension_not_determined`
exhibits two configurations *in the same ambient dimension `Fin 4`, with the same on-line channel,
and with two nonzero off-line channels in both cases* (so `p = 2` in both) whose defects are **1**
and **2**.

The degenerate one is not a contrivance: it is what the **reflection-degenerate evaluation
relation** `v(conj ρ) = conj(v ρ)` produces. Under that relation (`degenerate_channels`) the second
σ-pair has `x₂ = x₁` and `y₂ = −y₁`, so both σ-pairs of the quadruple carry the *same* rank-one
negative channel and the quadruple leaks **one** negative direction while contributing `p = 2`.
The relation holds whenever the compression's node set is pointwise invariant under `τ ↦ −τ` —
e.g. a single node at the origin. For a general symmetric node set the relation is
`v(conj ρ) = conj(P v(ρ))` with `P` the node-flip permutation, so `y₂ = −P y₁` and the contribution
is 2 unless `P y₁ = ±y₁`.

**Bottom line for the bookkeeping.** For a window with `q` genuine off-line quadruples:

* `p = 2q` (pair count), **proved**;
* `defect ≤ 2q`, **unconditional** (`defect_quadruple_block_le`);
* `defect = 2q` **only** under an independence-plus-separation witness for all `2q` imaginary
  channels (`defect_sumPairBlock_eq`);
* `defect` can be as low as `q` on genuine off-line data (`defect_parallel_channels_eq_one`), and
  as low as `0` if the on-line channels absorb the off-line ones
  (`orthogonality_is_load_bearing`).

There is no unconditional lower bound on the defect in terms of the quadruple count. That is the
honest state of the instrument.

---

## 2. Is `offline_pairs_le_defect` correct, undercounting, or overcounting?

**The theorem is CORRECT as stated.** `p ≤ defect hA` is proved from an explicit
`NegativeWitness hA p` hypothesis — a `p`-dimensional subspace on which `A` is negative definite —
via Sylvester's hard direction on `−A`. Nothing about it is wrong, and it was not weakened.

**The GLOSS around it overclaims**, in two distinguishable ways.

1. *"The instrument COUNTS off-line pairs."* Not unconditionally. The `NegativeWitness` is
   load-bearing and can **fail for a genuine off-line quadruple**:
   `defect_parallel_channels_eq_one` is a two-nonzero-channel configuration with `p = 2` and
   `defect = 1`, so `p ≤ defect` is simply false there, and no `NegativeWitness` of dimension 2
   exists. The instrument *detects* and *upper-bounds*; it counts only when handed a witness.

2. *"Independent off-line pairs contribute independently … (Vandermonde-type test vectors keep them
   linearly independent)"* — the parenthetical in the node's migration readback is an **unproved
   assertion stated as fact**, and it is **false in general**: for a flip-invariant node set the
   two channels of a single quadruple are anti-parallel, not independent.

**Undercount or overcount?** Neither, *for the theorem*. But for the dictionary's *translation* to
zeros, the risk is an **overcount by up to a factor of 2**: reading `defect = p` as "the defect
equals the number of genuine off-line zeros" is wrong — `p` is twice that count — and reading it
as "the defect equals `2 ×` the number of off-line zeros" is also wrong whenever the reflection
degeneracy bites. The only safe reading is `defect ≤ p = 2q`.

**A convention trap worth naming.** If a future author builds the compression from the *upper
half-plane only* (`γ > 0`, evenness of the test function absorbing the other half), one quadruple
supplies a *single* σ-orbit and `p = 1`. The block matrix in that convention is (in the
flip-degenerate case) exactly half the full-sum block, so the two conventions yield the **same
defect** but **different `p`**. At most one of them can satisfy `defect = p`. `DefectDictionary`
does not fix the convention; it must, before any `defect = p` claim is made about ζ.

---

## 3. What do the existing theorems actually quantify over?

Read against disk:

* **`DefectDictionary.offline_pairs_le_defect` / `R2Rigidity.lean:86`** — fully general: any
  `RCLike 𝕜`, any `Fintype n`, any Hermitian `A`, any `p`, given a `NegativeWitness`. The A2a
  skeptic caveat does **not** apply to this theorem. It is Sylvester's law, dualized.
* **`PairDecomp.defect_eq_offline_pairs` / `R2Rigidity.lean:209`** — also abstract, over an
  arbitrary `PairDecomp d`; but `PairDecomp` is a *declared* decomposition carrying `p` as a field
  with `rank imPart ≤ p` as an axiom of the structure. It is not tied to ζ, to zeros, or to any
  node set.
* **`BraggDefect.bragg_defect_eq_one`** — a `2×2` block `pairBlock (xvec f) (yvec d)` on `Fin 2`
  with `f` and `d` universally quantified reals. The "29 certified zeros" appear **only in the
  docstring**: the certified amplitude `F₁₀₀(u*)` is not a hypothesis, not a constant, and not
  referenced by the statement. The A2a caveat is accurate; the sharper objection is not the size
  but that (i) the entire on-line contribution is compressed into one scalar square `f²`, and
  (ii) the coordinate-diagonal layout makes the independence/orthogonality hypothesis trivially
  true by construction.
* **`BraggDefect.defect_eq_two`** — same, on `Fin 4` with two pairs on orthogonal coordinate axes.
  It is the `p = 2` count for *two independent pairs*, i.e. two quadruples' worth of channels in
  the degenerate reading, or one generic quadruple in the corrected reading.

**The extension.** `QuadrupleDefect.sumPairBlock` is the pair block with an arbitrary finite number
`m` of on-line channels, an arbitrary finite number `k` of off-line channels, in an arbitrary
finite ambient dimension `d`. At that generality:

* `defect_sumPairBlock_le : defect ≤ k` — **unconditional**;
* `defect_sumPairBlock_ge_of_subspace` — for any `W ≤ span{y_j}` killed by every on-line channel
  functional, `dim W ≤ defect` (this is the honest general lower bound, with the load-bearing
  hypothesis exposed rather than hidden in a coordinate layout);
* `defect_sumPairBlock_eq : defect = k` — under linear independence of the `k` channels **and**
  their orthogonality to the on-line channels. Both are finite kernel checks for any concrete node
  set.
* `sumPairBlock_two` identifies the `m = k = 2` case with the island's own `twoPairBlock`, so the
  results speak about the object `BraggDefect.defect_eq_two` is stated on.

**The extension is free in size and count; it is NOT free in the separation hypothesis.**
`orthogonality_is_load_bearing` proves that with the on-line channel equal to the off-line channel
the block is identically zero and `defect = 0` although `k = 1`: no unconditional `k ≤ defect`
exists.

---

## 4. Named residual obligation

**`QuadrupleChannelIndependence`** (open, finite, checkable, *not* RH-hard):

> For the zeta comb and a given finite node set `{τ₁,…,τ_d}`, the `2q` imaginary evaluation
> channels `y` of the `q` genuine off-line quadruples in a window are linearly independent and
> orthogonal to the span of the on-line channels.

This is exactly the hypothesis `defect_sumPairBlock_eq` consumes, and exactly what the
`MM_offline_pairs_le_defect` readback asserts without proof. It is **false** for node sets
pointwise invariant under `τ ↦ −τ` (`degenerate_channels`), so any future discharge must constrain
the node set. Discharging it for a concrete node set would upgrade the W2b rung from "defect ≤ 2q"
to "defect = 2q" *for that node set* — and would still say nothing about RH.

---

## 5. Registry correction (explicit, not silent)

Node `MM_offline_pairs_le_defect` — status left `proved` (the theorem is true as stated), statement
module untouched, **no `mission grant` run**. Title and readback corrected:

**Title, BEFORE:**

> W2b, the publishable rung: the defect instrument COUNTS off-line pairs (offline_pairs_le_defect)
> -- a p-dimensional negative-definite witness subspace forces p <= defect; independent off-line
> pairs contribute independently

**Title, AFTER:**

> W2b, the CONDITIONAL rigidity direction: a p-dimensional negative-definite witness subspace
> forces p <= defect (offline_pairs_le_defect). The witness is load-bearing and is NOT supplied by
> the off-line pair count -- one functional-equation quadruple carries p = 2 sigma-pairs but can
> leak only ONE negative direction (QuadrupleDefect.quadruple_witness_dimension_not_determined),
> so the defect does not unconditionally COUNT off-line pairs; unconditionally defect <= p

**Readback, BEFORE (excerpt):**

> Consequence: off-line zero pairs, each of which supplies an independent negative direction
> (Vandermonde-type test vectors keep them linearly independent), are COUNTED by the defect, not
> merely detected -- the R2 defect-k rigidity direction.

**Readback, AFTER (excerpt):**

> Consequence: off-line zero pairs are COUNTED by the defect *exactly when a witness of that
> dimension exists*; they are otherwise only detected and upper-bounded. The parenthetical
> "Vandermonde-type test vectors keep them linearly independent" of the 2026-09-14 migration
> readback was an unproved assertion and is FALSE in general (2026-09-19 quadruple audit).

Node `MM_bragg_defect_witness` — untouched. Scope caveat recorded as a `mission attempt` only: its
single synthetic off-line pair is **one σ-pair**, i.e. half of one functional-equation quadruple,
so `bragg_defect_eq_one` is not the defect cost of a genuine off-line zero of ζ.

---

## 6. Anti-triviality probes (all run)

| probe | target | result |
|---|---|---|
| `rfl` / `simp` / `decide` | `(quad s).card = 4` | all fail |
| `rfl` / `simp` / `decide` | `(quadSigmaPairs s).card = 2` | all fail |
| `rfl` / `simp` / `decide` | `defect (sumPairBlock …) ≤ k` | all fail |
| `rfl` / `simp` | `defect (sumPairBlock …) = k` | both fail |
| `rfl` / `simp` / `decide` | both halves of `quadruple_witness_dimension_not_determined` | all fail |
| `rfl` / `simp` | `defect_parallel_channels_eq_one` | both fail |
| `decide` | `(quad (1/2 + i)).card = 4` (non-vacuity) | fails — and `quad_online_card` proves the card is 2 |
| degenerate specialization `k = 0` | `defect ≤ 0` | **succeeds, as expected and documented** — the empty configuration is the one vacuous instance |

The `p = 0` specialization of `offline_pairs_le_defect` itself is `0 ≤ defect`, vacuous; that has
always been true of the node and is not a new finding.

`conjecture1_proved = False`.
