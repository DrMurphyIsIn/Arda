# RH ASCENT PLAN — the faceted assault on the wall

*2026-09-18. Branch `wall/ascent-plan`, base `origin/main` @ `2b419fd04`. Written by
the ascent-plan integrator from the facet packages, the two barrier packages, the
backlog map, and an independent read of the corpus on disk. Every corpus claim below
that carries a file:line was re-verified in this worktree; every claim that could not
be re-verified is marked UNVERIFIED and is not load-bearing.*

**`conjecture1_proved = False`.** Nothing in this plan proves, approaches, or reduces
the Riemann Hypothesis. Section 3 draws a hard line; nothing above it is progress
toward RH, and nothing below it is staffed.

---

## 0. Corrections to the brief, before anything else

The run brief's registry inventory is stale in three places. Re-counted on
`origin/main` @ `2b419fd04` in this worktree, `mission verify` green on all four
campaigns:

| campaign | proved | open | draft | other |
|---|---|---|---|---|
| rh | 17 | **2** (`RH_bl_explicit_formula`, `RH_li_rung0_kernel`) | 4 | — |
| mirrormere | **11** | **5** | 2 | — |
| anduril | 6 | 3 | 1 | — |
| bg | 9 | 3 | 1 | 1 refuted, 1 deprecated |

* rh has **two** open nodes, not one: the brief listed `RH_bl_explicit_formula`
  separately in prose but counted only `RH_li_rung0_kernel`.
* mirrormere is **11 proved / 5 open**, not 10 / 6: `MM_zeta_ordinates_not_uniformly_discrete`
  was granted (status `proved` on disk) when `grant/w2c` merged as #571, ahead of
  `origin/main` @ `2b419fd04`.
* `MM_weil_gram_trace` (D2) and `MM_weil_form_certified_height` (D3) are **not on main**;
  they live on `mm/d2-weil-gram-trace` and `mm/mm-d3-certified-height-weil-bound`. The
  brief's "two further drafts authored last run" are off-main and do not appear in any
  count above.

Two facets reached this integrator only as worktrees, not as JSON packages, and their
results are carried in §2 and §3 on the strength of a direct read of their commits:
`wall/rate-frontier` @ `e363d520b` and `wall/route-c-debruijn` @ `2bc20cab1`.

One package arrived **truncated**: the route-B facet JSON ends mid-sentence
("…with support L in pl"). Its `provable_now`, `registry_ops` and `work_items` were
never delivered. Per the same discipline the route-A skeptic applied to the same
failure: **this plan does not execute or recommend any operation it was not shown.**
Route-B work items below are reconstructed only from the parts of that package that
are quoted in full and independently verifiable on disk, and are marked as such.

---

## 1. THE WALL, STATED ONCE, EXACTLY

### 1.1 The four route clauses, side by side

**A5** (`RH_ROUTES_ROADMAP_2026-09-16.md` §2 table, `rh-hard-wall`, deps A0/A1e/A2c/A3):

> Defect-0 membership of the regularized Guinand–Weil triple of the zeta comb ⟺ RH.
> Refused decomposition (precedent-mandated).

Its only rendering that is a Lean proposition today is the one authored on
`mm/w3c-goal-weil-membership` @ `289c68c8`, which replaced the 2026-09-14 placeholder
`theorem zeta_comb_membership : RiemannHypothesis`:

```lean
theorem zeta_comb_membership :
    forall g : R -> C, WeilExplicit.IsWeilTest g ->
      0 <= (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re
```

**B10** (roadmap §3 table, `rh-hard-wall`, deps B1/B2/B7/B9): "the uniform tail: all-n /
all-support ⟺ RH." Its corpus face is a Lean proposition that is not merely formalizable
but **already formalized**, as the right-hand side of an unconditional pinned iff. Read
in this session at
`/Users/peterwmurphy/arda-gw-finite/telperion/examples/li_positivity/lean/.lake/packages/LiCriterion/Lc/LiCriterion/XiOrderBridge.lean:68`:

```lean
theorem li_criterion_rh_iff :
    RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) :=
  biconditional_rh_li_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one
```

So the wall clause on route B is literally `∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re`,
and the campaign owns, kernel-clean, the theorem that this clause *is* RH.

**C10** (roadmap §4 table, `rh-hard-wall`, dep C8): `Λ ≤ 0`, with Rodgers–Tao
`Λ ≥ 0` (Forum Math. Pi 8 (2020) e6) giving RH ⟺ Λ = 0.

**D11** (roadmap §5 table, `rh-hard-wall`, deps D3/D6/D7/D8/D9): "Operator-with-completion
⟺ Weil positivity ⟺ RH (**merged with B10**)" — the merge is the roadmap's own word, and
§5 states the reason as identity rather than analogy: "Li's λₙ are the Weil form on the
test family attached to (1−(1−1/s)ⁿ); B certifies the wall on a countable subfamily, D on
band-limited subfamilies — the same Hermitian form whose negative inertia
`offline_pairs_le_defect` counts."

### 1.2 What they share

All four are RH-equivalent by named classical theorems, and the roadmap says so in §1
("THE WALL — one clause, graded identifications") before this run began. The novel part
is not that they are equivalent — every face is RH-equivalent, so any cross-face
equivalence routed through RH is vacuous, which the roadmap §1 also already records.
The novel part is how much of the four-route structure survives being made precise.

### 1.3 Verdict: are they the same clause in different coordinates?

**Three of the four are one clause. One is not. The temperedness face is not a
coordinate at all.**

1. **B10 = D11, by the roadmap's own construction.** Not a finding of this run; §5 already
   says "merged with B10," and §3's B10 row already carries the "all-support" face.

2. **A5 = B10/D11, once A5 is made precise.** This is the route-A facet's central
   result and this plan endorses it: the authored `zeta_comb_membership` on
   `mm/w3c-goal-weil-membership` is *verbatim* the Weil-positivity clause. The facet's
   own words: "A5-W is verbatim the B10/D11 wall. Route A, made precise, has no wall of
   its own." Consequence for the registry: `MM_zeta_comb_membership` and the rh-side
   Weil face are **one wall registered twice**, and the plan below treats them as one.

3. **C10 is genuinely different.** Its equivalence to RH runs through Newman 1976 +
   de Bruijn 1950 + Rodgers–Tao, none of which is in the corpus or in Mathlib; nothing on
   route C reduces to a Weil form; and it is the only route whose distance-to-RH is a
   single certified real number with a published record (Λ ≤ 0.2, P15 Table 1 row 2 +
   Platt–Trudgian). Treating C10 as "the same clause in another coordinate" would be
   averaging, and this plan refuses it. C is a second wall, not a second view of the first.

4. **The temperedness face (A5-FQ) is not a fourth coordinate — and here the facet and
   its skeptic disagree, so both are recorded rather than averaged.**

   * The **facet** holds: unregularized, the clause is unconditionally FALSE (dual-comb
     unit-window mass ~ e^{u/2} by PNT partial summation); regularized to a compactly
     supported test class, temperedness is automatic and the clause is VACUOUS; therefore
     "there is NO temperedness-graded statement of A5 under ANY regularization," and the
     face should be retired from roadmap §1.
   * The **skeptic** holds: part (i) is already in roadmap §1 as a load-bearing
     correction, so it is not new; the "vacuous after regularization" step conflates the
     regularized *object* with its *pairing* against a restricted test class, and
     subtracting a Γ′/Γ-scale density cannot cancel an atomic part growing like e^{u/2};
     and a sweeping negative over an unbounded space of regularizations is not a skeptic
     result but an unsupported closure of an open formulation problem (roadmap milestone
     A0, classified `open-research`).

   **This plan's ruling:** the sweeping negative is UNPROVED and is not carried. A0 stays
   queued as `open-research` and the face stays in the §1 table. The one action both
   sides support is taken: `zeta_FQ_iff_RH`
   (`CharacterizationStatements.lean:154`) is a `def ... : Prop` over the opaque variables
   `(IsFourierQuasicrystal : Meas -> Prop) (ZetaComb : Meas) (RiemannHypothesis : Prop)`;
   it quantifies nothing and asserts nothing; it is **vocabulary, not a program
   conjecture awaiting proof**, and should be labelled as such wherever prose treats it
   as a target. That is a docstring edit, not a registry operation.

### 1.4 What the wall is *not*

It is not the B7 seam, not the corridor bound, not the rate frontier, and not the
hcomp exhaustion seam — the roadmap's B10 row already records the last of these as
de-walled by its skeptic ("known unconditional mathematics awaiting formalization").
Section 2 adds one more to that list and it is the most consequential correction in
this run: **closing the B7 seam is not wall work and is not RH progress.**

---

## 2. THE UNIFORMITY THESIS

**The run's seed hypothesis — "on every route the wall clause is a uniformity /
order-of-quantifiers statement, while every instrument produces instances" — is FALSE
as stated, and the way it fails is more useful than the way it would have been true.**

### 2.1 Clause by clause

| clause | logical form | is it an alternation? |
|---|---|---|
| B10 (Li face) | `∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re` | **No.** A bare unbounded universal with no inner existential. Nothing to swap. |
| A5-W / D11 (Weil face) | `∀ g, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re` | **No.** Π over `g`. The honest HAVE/NEED is `∃L0 ∀g` vs `∀L ∀g` — *deleting* an existential bound, not swapping two quantifiers. |
| C10 | `Λ ≤ 0`, i.e. a threshold on an `sInf` | **No.** A margin statement, not a quantifier order. |
| A5-FQ | (no statement exists) | Not applicable; see §1.3(4). |

The route-B facet reaches this independently and states it bluntly: "Anybody who
describes B10 as an order-of-quantifiers problem is inflating it." The route-A facet
reaches it too — "it is not swap two quantifiers; it is delete the existential bound on
L" — and then re-manufactures an alternation by lifting proof certificates into the
object language (`∀L ∃C_L : C_L ⊢ P(L)` vs `∃A ∀L : A ⊢ P(L)`). Its skeptic calls that
a smuggle, on the ground that `A` ranges over *arguments*, not mathematical objects, and
**this plan agrees with the skeptic**: the target `∀L, WeilPositiveOn L` is Π-over-L with
no existential to swap.

### 2.2 Where the alternations actually are — and they are all *below* the wall

The pattern is real. It is just not located where the brief placed it. Every genuine
order-of-quantifiers statement this run found sits at a **seam the program can work on**,
not at a wall clause:

* **The B7 seam** (route-B facet, and the sharpest statement of it anywhere in the
  corpus). With `L(n,T) := Re (BombieriLagarias.liZeroSum n T)` and
  `λₙ := lim_{T→∞} L(n,T)`:
  * HAVE (`RH_bl_finite_multiset`, proved, contrapositive per window):
    `¬RH → ∃T₀, ∀T ≥ T₀, ∃n > 0, L(n,T) < 0`
  * WANT (Li's hard direction): `¬RH → ∃n > 0, λₙ < 0`
  * The alternation is exactly `∀T ∃n ⟹ ∃n ∀T`: the Skolem function `n(T)` must be shown
    bounded in `T`.
* **The rate frontier** (`wall/rate-frontier` @ `e363d520b`, kernel-clean at the v4.34
  pin, read in this session). A region *shape* gives `∀δ ∃T`; Quasi-RH demands `∃δ ∀T`;
  `RateFrontierNoGo.shape_tendsto_zero_does_not_entail_quasi` proves, sorry-free, that
  every width function tending to 0 admits a point set satisfying the shape everywhere
  and violating every fixed margin. `dvpShape` and `vkShape` are both such shapes.

**Two corrections the integrator must carry, because both cut against work that looks
attractive:**

(a) **The effective truncation bound does not close the B7 seam.** The B7 memo queues
`|L(n,T) − λₙ| ≤ C n² log T / T` (§2.1). That controls the error at *fixed* n; the whole
difficulty is that n varies with T. Along the Skolem sequence the bound reads
`C n(T)² log T / T`, vacuous unless one already knows `n(T) = O(T^{1/2}/polylog)`. The
missing input is an upper bound on `n(T)`, a different object.
`AUDIT_TESTIMONY_B7_2026-09-18.md` seam 1 says the truncation bound "is precisely" what
is needed; **that is the one place the audit overstates and the integrator should not buy
it.**

(b) **Closing the B7 seam buys pin-independence, not RH progress.** `L(n,T)` is
non-decreasing in T at fixed n and converges to `λₙ`, so `λₙ < 0` for some n makes
`n(T)` bounded — and "`¬RH → ∃n, λₙ < 0`" is exactly the hard direction of Li's
criterion, which is *already on disk kernel-clean* as `LiCriterion.li_criterion_rh_iff`.
Staffing B7-i → B7-ii composition as frontier work is a category error. The roadmap's
B10 deps row should say so.

Likewise, the rate-frontier no-go must be read at its true scope: its theorems quantify
over abstract sets of (abscissa, ordinate) pairs and **never mention zeta**. What they
refute is "sharpening the region shape is a step toward Quasi-RH" *for arguments that
consume nothing but the shape*. That is real and worth registering; it is not a theorem
about ζ's zero set, and this plan will not let it be read as one.

### 2.3 Does this make the program's instrument class structurally insufficient?

**Not as a theorem. Insufficiency is not established, and the attempt to establish it was
refuted.** What *is* established, all kernel-clean, is a set of no-gos each of which
pairs ONE instrument class against ONE target:

1. Reflection-invariant per-zero functionals cannot orient a zero within its pair
   (`ReflectionForced.lean`, the WALL CAMPAIGN's FORCED half) — while the invariant pair
   weight `2cosh((β−1/2) log x)` *does* strictly detect off-line-ness
   (`ReflectionDetect.lean`). Products blind, sums detect.
2. A vanishing-width region shape does not entail a uniform margin
   (`RateFrontierNoGo.lean`).
3. A uniformly δ-robust sound heat-flow certificate scheme certifies no time `t < δ`, so
   its best bound is `Λ ≤ δ` and never `Λ ≤ 0`
   (`DBNFlowNoGo.uniform_robust_cannot_reach_wall`, `wall/route-c-debruijn` @ `2bc20cab1`,
   nine theorems, all three-axiom, no sorry).
4. Finite Euler sections have all zeros at `Im x = 1/2` uniformly in N, with `x = i/2` a
   zero of every nonempty section (route-A facet, elaborated and axiom-clean at the v4.32
   pin).

None of these is a barrier to RH, and combining them does not make one. The honest
summary is quantitative and route-specific, not structural.

### 2.4 The barrier result and its adversary — carried verbatim

The run commissioned a barrier attempt and an adversary. The attempt's status is
`sketched`; the adversary refutes it as a barrier claim. Both are reproduced here in
their own words, because the case where a barrier is refuted is exactly the case a plan
is tempted to quietly drop.

**BARRIER ATTEMPT (verbatim, `wall/barrier`, Lean at
`/Users/peterwmurphy/arda-wall-barrier/telperion/examples/wall_barrier/lean/`,
`WallBarrierAM.lean` + `FEUniformBarrierAM.lean`, status `sketched`):**

> "A real barrier theorem IS available to this program, but it is relativization-grade,
> not natural-proofs-grade, and the run's framing ("uniformity vs instances") is NOT the
> right axis. Three results, graded separately:
>
> (1) THE SYMMETRY BARRIER IS ABOUT ORIENTATION, NOT RH — PROVED, kernel-clean. The wall
> campaign's FORCED half generalizes to arbitrary reflection-invariant maps into arbitrary
> types (`no_invariant_orients`), but it is provably NOT an obstruction to RH:
> `invariant_detects` exhibits a reflection-invariant functional (rho |-> |Re rho - 1/2|)
> whose vanishing is exactly membership of the critical line, and RH is itself a
> reflection-invariant predicate (`onLine_reflect`). So "the RH wall is a symmetry theorem"
> is TRUE for orientation and FALSE for RH. Any barrier claim that upgrades FORCED into an
> obstruction to RH proves too much and is refuted in the kernel by `invariant_detects`.
>
> (2) THE FE-UNIFORMITY BARRIER (Davenport-Heilbronn substitution) — SKETCHED, with the
> transfer schema PROVED. Every RH-equivalence the program owns or targets is a theorem
> about a CLASS, not about zeta: Li positivity is proved on the li_positivity island by
> `biconditional_rh_li_of_hadamard_order_one` (XiOrderBridge.lean:68) from
> `Hadamard.hasFiniteOrder riemannXi` and `Hadamard.order riemannXi <= 1` and NOTHING else
> — the lemma name itself certifies the FE-uniformity of the whole Li ladder. The class
> contains Davenport-Heilbronn, which has off-line zeros (already Arb-certified in this
> repo). Hence no FE-uniform argument can prove ANY route's wall clause, and ONE witness
> refutes all four routes at once — the four routes are not independent attacks but four
> FE-uniform re-encodings of the same non-bundle residue, and the residue is the Euler
> product. I proved the transfer schema (`fe_uniform_criterion_is_false`,
> `no_fe_uniform_sufficient_condition`); the barrier over the bundle that actually covers
> the routes remains sketched.
>
> (3) THE DUAL CEILING (Beurling / Diamond-Montgomery-Vorhauer) — literature-anchored, NOT
> formalizable today. Drop the functional equation, keep the Euler product plus
> N(x) = rho x + O(x^theta): RH becomes independent of what is left, and the de la Vallee
> Poussin region is optimal. Consequence for this program: its own proved zero-free chain
> (gamma5 / polylog / dlvp / dlvp-effective) is proved from Beurling-uniform data, so the
> recorded "classical region ceiling" is a BARRIER, not a shortfall of effort.
>
> TAKEN TOGETHER: the Euler product alone caps at de la Vallee-Poussin; the functional
> equation alone decides nothing. Any proof must use both, jointly and inseparably. That is
> the sharpest true statement available about the wall today, and it is a sandwich, not a
> uniformity claim.
>
> WHAT I REFUTE IN THE RUN'S FRAMING: the "every wall clause is a uniformity statement
> while every instrument produces instances" pattern does NOT yield a barrier theorem. As a
> logical claim it is false (induction and compactness routinely prove universals from
> instance families), and a barrier of that shape would prove too much. The honest residue
> is quantitative and route-specific (the route-A facet's lambda_min(L) -> 0
> doubly-exponentially margin degeneration), not a barrier theorem. The right axis is WHICH
> AXIOMS an argument consumes, not how many quantifiers its conclusion has."

**BARRIER ADVERSARY (verbatim, `wall/adversary` @ `399eebc23`):**

> "REFUTED as a barrier claim. The proposed FE-uniformity barrier is SOUND AND EMPTY, its
> headline is unsupported by its own three items, and its central corpus evidence is
> factually false.
>
> (A) THE SCHEMA CANNOT REACH ANY WALL CLAUSE — kernel-proved. All three transfer theorems
> refute only the UNIVERSALLY QUANTIFIED form `forall E : FEData, Crit E`. Every route wall
> clause is a statement about ONE member: A5 "defect-0 membership of the regularized
> triple", B10 "all-n / all-support", C10 "Lambda <= 0", D11 "Weil positivity". I exhibited
> a second bundle member, s |-> (s - 1/2)^2 (entire, self-dual, order zero, only zero at
> 1/2), which SATISFIES the RH analogue. Consequently, in the kernel: `barrier_silent` (the
> bundle contains both an RH-satisfying and an RH-refuting member),
> `transfer_to_member_fails` (the inference "uniform form refuted, therefore this member's
> form refuted" is FALSE), and `uniform_refutation_decides_nothing` (for EVERY Crit
> equivalent to RHfor on the bundle — exactly the class the barrier claims to kill — Crit
> is true at one member and false at another). The barrier's conclusion is compatible with
> both truth values of every route's wall clause.
>
> (B) THE CENTRAL CORPUS EVIDENCE IS FALSE. "Route B's equivalence consumes ONLY entire +
> order <= 1 and NOTHING else — the lemma name itself certifies the FE-uniformity of the
> whole Li ladder." Read the proof term, not the name.
> `biconditional_rh_li_of_hadamard_order_one` (RHBridge.lean:105) is a theorem ABOUT
> `riemannXi` with two named hypotheses, not a theorem about a class; it routes through
> `rh_equiv_mathlib` (RHBridge.lean:29), which consumes `riemannZeta_ne_zero_of_one_le_re`
> at lines 48 and 79, imported at line 7 from `Mathlib.NumberTheory.LSeries.Nonvanishing`,
> whose proof uses `LSeries_eulerProduct_exp_log` (Nonvanishing.lean:295-296). Route B's
> corpus proof already consumes Euler-product non-vanishing and is therefore NOT in the
> barrier's class. By the researcher's own (correct) axis — "WHICH AXIOMS an argument
> consumes" — his barrier fails.
>
> (C) THE CLASS COVERS NOTHING THE PROGRAM BUILDS. 3/3 real artifacts checked are outside
> it; the one artifact inside it is already quarantined from the wall by the corpus's own
> design.
>
> (D) ZERO NOVELTY. QC_PROGRAM.md Pillar 1 (2026-09-13/14, four days earlier): "the
> discriminating clause against Davenport-Heilbronn is **weight positivity** (Euler
> product), confirmed mechanically by the zoo." That is verbatim the barrier's headline
> conclusion, already mechanically confirmed and already used to design route A's axioms.
>
> (E) THE ENRICHMENT GOES THE WRONG WAY. The program's actual target class is roadmap A1d:
> "unimodular completely-multiplicative + FE ==> degree-1 Selberg element". DH FAILS the
> multiplicativity clause, so the witness does not exist there. `enriched_bundle_flips`
> proves that over a class with no off-line witness the identical schema runs FORWARD as a
> theorem schema. The barrier's force is a property of the class chosen, not of RH.
>
> (F) THE SYMMETRY ITEM IS A DUPLICATE OF AN EXISTING CORPUS ARTIFACT, and its
> generalization has a defect. [...] `no_invariant_orients` [...] takes its contradiction
> from the pair (0, 1), which are not zeros of anything. On the zero set — where every
> instrument in this program is evaluated — I proved FORCED is VACUOUS under the RH
> analogue (`forced_on_zeros_vacuous`) and asserting it there IMPLIES an off-line zero
> (`forced_on_zeros_iff_not_rh`). A statement equivalent to NOT-RH cannot obstruct a proof
> of RH; it presupposes its negation.
>
> (G) THE DMV CEILING IS NOT BINDING ON THIS PROGRAM. The zero-free artifacts record their
> own ceiling and it is not DMV [...] Those nodes sit strictly BELOW de la Vallee-Poussin
> for a documented FORMALIZATION reason, and RH_dlvp_region_effective is ALREADY PROVED, so
> the program has reached dVP. DMV caps widening PAST dVP from Euler-product-only data,
> which no route proposes.
>
> WHAT SURVIVES, and I say so plainly: the Lean is real (I re-elaborated it myself:
> sorry-free, 3-axiom); the DH Arb certificate is quoted accurately;
> `poly_refutes_poor_bundle` is an honest self-refutation most authors would have
> suppressed; and the refutation of this run's "uniformity vs instances" framing is correct
> and I reach it independently."

**INTEGRATOR'S RULING, with one independent verification.**

The adversary's point (B) is decisive and I re-verified it on disk in this session rather
than taking either side's word. At
`.../.lake/packages/LiCriterion/Lc/LiCriterion/RHBridge.lean`: line 7 imports
`Mathlib.NumberTheory.LSeries.Nonvanishing`; `rh_equiv_mathlib` is at line 27;
`riemannZeta_ne_zero_of_one_le_re` is applied at lines 48 and 79;
`biconditional_rh_li_of_hadamard_order_one` is at line 105 and rewrites by
`rh_equiv_mathlib` at lines 89 and 98. **Route B's corpus equivalence does consume
Euler-product non-vanishing.** The barrier's "and NOTHING else" is false against the
house's own dependency graph.

Verdict: **the FE-uniformity barrier is REFUTED as a barrier.** Point (A) alone settles
it — a refutation of `∀E : FEData, Crit E` cannot decide `Crit` at the single member that
every wall clause is about. What survives the adversary, and is worth keeping in the
corpus, is a scope lemma, not a barrier: *an argument that consumes only entirety,
self-duality and order ≤ 1 cannot prove any route's wall clause, because Davenport–Heilbronn
is in that class and is Arb-certified off-line here.* That is useful as a **design rule for
future statements** (if a proposed lemma's hypotheses are FE-uniform, it cannot be the
wall's last step) and useless as an obstruction, since no artifact the program has built
is in that class.

Verdict on item (1): the symmetry barrier is about orientation, confirmed by its own
author and by `invariant_detects`. It is **not** an obstruction to RH and must never be
cited as one.

Verdict on item (3): the DMV/Beurling ceiling is literature-anchored and not formalizable
at any pin the campaign uses; the adversary's (G) additionally shows it is not the binding
constraint on the corpus's zero-free chain, which is capped by a documented *formalization*
gap and has in any case already reached dVP. **Do not write the barrier's proposed ledger
text onto `RH_zero_free_gamma5` or `RH_zero_free_polylog`.**

### 2.5 The thesis, in one paragraph

Wall clauses are bare universals or thresholds, not alternations; alternations live at the
seams *below* the wall, where they are real, nameable, and — in the two cases this run
made precise — either already-owned mathematics in disguise (B7) or provably not closable
from the instrument's own inputs (rate frontier, heat-flow robustness). The instrument
class is therefore **demonstrably insufficient for the seams it has been tested against,
and of unknown sufficiency for the wall**, and no argument in this run changes the second
half of that sentence. The right axis for future no-gos is the barrier author's own, which
his adversary endorses: *which axioms does the argument consume*.

---

## 3. THE FACETED ASSAULT

Six pre-wall facets, ordered by value per unit of work. Each item gives the exact
`mission` subcommand, the cost, and what it buys. The shim, run from `telperion/`:

```sh
PYTHONPATH=src python3 -c "import sys,tomli; sys.modules['tomllib']=tomli; \
from telperion.cli import main; sys.argv=['telperion','mission',SUBCMD,...]; sys.exit(main())"
```

Verified CLI signatures (read from `src/telperion/cli.py:1619-1676` in this worktree):

* `add CAMPAIGN NAME --title T --kind {goal,milestone,lemma,definition} [--deps a,b] (--statement T | --statement-file F)` — **new nodes are created with `status = "draft"`**
* `audit SLUG [--campaign C] --text T --auditor A` — promotes draft → open
* `link SLUG [--campaign C] --artifact P --kind {lean_module,frozen_cert} --via {direct,reduction}`
* `attempt SLUG [--campaign C] --session S --route R --verdict {Proved,Refuted,NoGo,Stalled} --detail D`
* `grant SLUG [--campaign C]` · `verify [CAMPAIGN] [--deep-lean]` · `open-leaves [CAMPAIGN]` · `graph [CAMPAIGN]`

`depends_on` targets **must be in the same campaign** (`missions/registry.py:78-83` raises
`SchemaError` otherwise). Every cross-campaign relationship below is therefore recorded in
a title or a ledger entry, never as an edge.

---

### F1 — REGISTRY INTEGRITY (do this first; it protects every other claim)

The backlog map's headline is that the grant gate can mark a node `proved` on a false
premise. **I re-verified all three mechanisms on disk in this worktree, independently of
the probe campaign:**

* **G1 — the gate never checks for `sorry`.** `missions/verify.py:261` `grant_status`
  checks exactly five preconditions (status open; proof link present; artifact file
  exists; normalized statement non-empty; normalized statement is a substring of the
  normalized artifact). It never inspects the artifact for `sorry`, `sorryAx`, or axioms.
  Worse, `normalize_lean` (`verify.py:107-117`) strips a trailing `:= by sorry` / `:= sorry`
  with a `$`-anchored regex, and `statements._build_body` appends `:= by sorry` to every
  generated statement file — so a sorry-carrying artifact matches **by design of the
  normalizer**. The correct checker already exists and is already tested:
  `audit_lean_file` at `src/telperion/audit.py:87`, wired only into the standalone
  `telperion audit` command at `cli.py:636`. **The gate simply never calls it.**
* **G2 — the gate never inspects `depends_on`.** Dependency-status awareness lives only in
  `open_leaves`, a scheduling query, not a gate.
* **G3 — `closure_clean` is a label, not a gate.** `grant_status:322` sets
  `closure_clean = (new_status == "proved")` unconditionally, and `_compute_closures`
  (`verify.py:184-191`) applies the dependency fixpoint **only to `via = "reduction"`
  nodes** — "a direct-proved node's closure is always clean (True)". I counted the live
  links: **44 `via = "direct"`, 0 `via = "reduction"`** across all four campaigns. The
  closure fixpoint has never executed against a single real node.

What holds the line today is per-island CI (`proof-lean.yml` / `telperion-lean-e2e.yml`
sorryAx guards) keyed to named anchor theorems — and nothing joins a node's
`proof.artifact` field to any CI guard. Coupling is convention plus reviewer attention.

**F1 ops (code, not registry; ~1 day total, no Lean build, no disk cost):**

| op | change | cost | buys |
|---|---|---|---|
| F1-1 | In `grant_status`, before the containment check, call `audit_lean_file(artifact_path)` and raise `GateError` on any `sorry`/`sorryAx`/stub finding. Three lines into already-tested code. | 2 h | The gate stops being able to certify a `sorry`. This is the single highest-value change in the entire plan. |
| F1-2 | In `grant_status`, refuse the flip if any `depends_on` target is not `proved`. | 1 h | A node can no longer be proved over a draft dependency. |
| F1-3 | Extend `_compute_closures`' fixpoint to `via = "direct"`, with an explicit `closure_override_reason` field to preserve `RH_dlvp_zero_free_region`'s deliberate `false`. | 3 h | The 44 live links get a real closure computation for the first time. |
| F1-4 | Make `verify_campaign` **error** (not warn) on `status = "proved"` with `closure_clean = false` and no `closure_override_reason`. | 1 h | `mission verify` becomes capable of failing on the condition it exists to detect. |

**Do F1 before any grant in F2–F6.** Every grant executed before F1-1 lands is a grant
the house cannot distinguish from a sorry.

---

### F2 — THE NO-GO HARVEST (this run's actual new output)

Four kernel-clean negative results exist in sibling worktrees and are not in the registry.
They are the run's real product and they are cheap to land. **Each is a theorem about an
instrument, not about zeta, and each node title must say so.**

**F2-1. Register the rate-frontier no-go.** Artifact:
`/Users/peterwmurphy/arda-wall-rate-frontier/telperion/examples/li_positivity/lean/RateFrontierNoGo.lean`
(`wall/rate-frontier` @ `e363d520b`, elaborated with `lake env lean` at the v4.34 pin, no
island build). Statement to register, verbatim from the artifact:

```lean
theorem shape_tendsto_zero_does_not_entail_quasi
    (w : ℝ → ℝ) (hw : Filter.Tendsto w Filter.atTop (nhds 0)) :
    ∃ S : Set (ℝ × ℝ),
      (∀ p ∈ S, 3 ≤ p.2 ∧ p.1 ≤ 1 - w p.2) ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S, p.1 ≤ 1 - δ
```

```sh
mission add rh RH.rate_shape_no_quasi \
  --kind lemma --deps "" \
  --title "The RATE-FRONTIER NO-GO (a theorem about region SHAPES, not about zeta): for every width function w tending to 0 there is a set of (abscissa, ordinate) pairs satisfying the shape at every point and admitting no fixed positive margin, so dvpShape and vkShape both sit strictly on the near side of the forall-delta-exists-T / exists-delta-forall-T alternation. Scope: the statement quantifies over abstract point sets and NEVER mentions riemannZeta; it refutes 'sharpening the rate is a step toward Quasi-RH' only for arguments consuming nothing but the shape. NOT a step toward RH; conjecture1_proved = False" \
  --statement-file /path/to/rate_shape_no_quasi.lean
mission audit RH_rate_shape_no_quasi --auditor "<blind auditor, independent read-back>" --text "<testimony>"
mission link  RH_rate_shape_no_quasi --artifact examples/li_positivity/lean/RateFrontierNoGo.lean --kind lean_module --via direct
mission grant RH_rate_shape_no_quasi
```
**Cost:** 0.5 day (statement authoring + blind read-back), no build beyond one
`lake env lean`. **Buys:** the corpus stops being able to describe a Vinogradov–Korobov
rate improvement as progress toward RH, with a kernel theorem rather than prose.

**F2-2. Register the heat-flow robustness no-go.** Artifact:
`/Users/peterwmurphy/arda-wall-route-c-debruijn/telperion/examples/dbn/lean/DBNFlowNoGo.lean`
(`wall/route-c-debruijn` @ `2bc20cab1`; nine theorems, all `[propext, Classical.choice,
Quot.sound]`, no sorry; guard module `AxiomGuardDBNFlowNoGo.lean` included). Register
`uniform_robust_cannot_reach_wall` — a uniformly δ-robust sound scheme certifies no
`t < δ`, so its best bound is `Λ ≤ δ`, never `Λ ≤ 0`.
```sh
mission add rh RH.dbn_flow_robustness_nogo --kind lemma --deps "" --title "..." --statement-file ...
mission audit RH_dbn_flow_robustness_nogo --auditor "..." --text "..."
mission link  RH_dbn_flow_robustness_nogo --artifact examples/dbn/lean/DBNFlowNoGo.lean --kind lean_module --via direct
mission grant RH_dbn_flow_robustness_nogo
```
**Cost:** 0.5 day. **Buys:** the `RH_MARGINALITY_LEHMER` method-class no-go, which the
roadmap's C10 row carries as prose, becomes a quantitative kernel theorem; route C's
honest ceiling gets a machine-checkable statement. Also lands `xiArg_re_eq_half_iff` and
friends, the complete C4 change of variables, as a by-product that F6 consumes.

**F2-3. Register the uniform-in-N Euler-section refutation — the theorem, NOT the
interpretation.** The route-A facet proved, axiom-clean at the v4.32 quasicrystal pin,
that for *every* finite prime set P every zero of the |P|-factor Euler section has
`Im x = 1/2` exactly, and `x = i/2` is a zero of every nonempty section. Register with the
product **inlined**, so no `MMDefs` edit is needed (`MMDefs.lean:33` already carries
`twoFreq` verbatim; three branches edited `MMDefs` in one day and the conflict window is
still open):

```lean
theorem euler_section_uniform_offline (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) (x : ℂ)
    (hz : (∏ p ∈ P, twoFreq 1 ((-(1 / Real.sqrt (p : ℝ)) : ℝ) : ℂ) 0
              (-(Real.log (p : ℝ))) x) = 0) :
    x.im = 1 / 2
```
```sh
mission add mirrormere MM.euler_section_uniform_offline --kind lemma \
  --deps MM_twofreq_realrooted_iff --title "..." --statement-file ...
```
**Cost:** 1 day including the blind read-back. **Buys:** the negative control for the
torus-section ladder goes from three instances (p = 2, 3, 5) to *every* rung, with a
single witness independent of N. The naive ladder does not drift toward the line; it fails
identically everywhere.

**DO NOT** register `eulerSection_not_conj_closed` as its own node, and do not attach the
"T3 has no object" reading to anything. The theorem is true (independently re-elaborated,
axiom-clean) but the interpretation is false against the house's own Lean:
`DefectDictionary.lean:111` is `def defect {A : Matrix n n k} (hA : A.IsHermitian) : Nat :=
posIndex hA.neg` — defined for *any* Hermitian matrix, with no involution hypothesis;
`offline_pairs_le_defect` likewise takes an arbitrary Hermitian `A`; the same pair is
duplicated at `MMDefs.lean:97,111`. Nothing is undefined. What actually fails for a section
is the pair-block *counting* row, because a section has no functional equation and hence no
natural arch-minus-prime Hermitian form. Keep the result as a four-line corollary inside the
F2-3 artifact. **Registering a node whose title retires a live research track on a premise
contradicted by the house's own Lean is precisely the failure the audit cycle exists to
catch, and it is this run's worst near-miss.**

**F2-4. Ledger the B7 seam correction.** No new node; the correction belongs on the
existing open node.
```sh
mission attempt RH_bl_explicit_formula --session "<session>" \
  --route "seam analysis: forall-T-exists-n to exists-n-forall-T" --verdict Stalled \
  --detail "The B7 seam is a genuine Sigma-to-Pi alternation over (T, n): RH_bl_finite_multiset gives not-RH -> exists T0, forall T >= T0, exists n > 0, L(n,T) < 0, while Li's hard direction needs exists n, forall T. The queued effective truncation bound |L(n,T) - lambda_n| <= C n^2 log T / T (B7 memo 2.1) does NOT close it: evaluated along the Skolem sequence it reads C n(T)^2 log T / T, vacuous unless n(T) = O(T^(1/2)/polylog) is already known. The missing input is an upper bound on n(T), a different object. AUDIT_TESTIMONY_B7_2026-09-18 seam 1 overstates this and should not be relied on. Separately: L(n,T) is nondecreasing in T at fixed n and converges to lambda_n, so lambda_n < 0 bounds n(T) -- i.e. the swap IS Li's hard direction, already on disk kernel-clean as LiCriterion.li_criterion_rh_iff. Closing this seam buys INDEPENDENCE FROM THE UPSTREAM PIN, not RH progress. conjecture1_proved = False"
```
**Cost:** 15 minutes. **Buys:** stops a 4-12 month staffing decision from being made on the
belief that it is frontier work.

---

### F3 — PRE-WALL DISCHARGE (the five open mirrormere leaves and the rh open pair)

All verified workable via `mission open-leaves` in this worktree.

| op | node | route | cost | buys |
|---|---|---|---|---|
| F3-1 | `MM_euler_factor_section_offline` | Five-line bridge on the v4.32 island: instantiate `twoFreq_realRooted_iff` with `c₁=1, c₂=−1/√2, lam₁=0, lam₂=−log 2`; the iff reduces to `¬(‖(1:ℂ)‖ = ‖((−1/√2:ℝ):ℂ)‖)`, i.e. `1 ≠ 1/√2` by `norm_num` + `Real.sqrt_two` (`CONSUMER_SWEEP` §1 row 5). Proof exists on `mm/mm-euler-factor-offline`. | 0.5 d | Closes the T2 negative control. Subsumed by F2-3 as the N=1 case — **do F2-3 and F3-1 in one artifact, one module name**, per the one-module-per-agent island rule. |
| F3-2 | `MM_recurrence_deficit_eq_excess` | `Real.exp` ring algebra + strict monotonicity; proof on `mm/recurrence-deficit`. | 0.5 d | The E4a Face-4 ↔ Face-1 witness bridge. |
| F3-3 | `MM_offline_disjoint_discs` | Pure metric topology; proof on `mm/offline-disjoint-discs`. | 0.5 d | The E4b isolation lemma, substrate for disjoint-disc off-line counting. |
| F3-4 | `MM_torus_section_dictionary` (**draft, and it is the blocker**) | Needs a *re-audit*, not a proof: its original statement was caught as definitionally `rfl` by the 2026-09-14 blind read-back and replaced, and the replacement has never been read back. `mission audit MM_torus_section_dictionary --auditor "<independent>" --text "<testimony>"` | 0.5 d | Unblocks `MM_torus_section_n2_rigidity`, which is `open` but absent from `open-leaves` **solely because its dep is draft**. Highest leverage per hour in F3. |
| F3-5 | `MM_torus_section_n2_rigidity` | Short bridge from `twoFreq_realRooted_iff`; gated on F3-4. Branch `mm/torus-ladder-t1`. | 1 d | The T1 N=2 rung in ladder vocabulary. |
| F3-6 | `MM_speiser_box_probe` | Winding-box certificate via the *derivative* variant of the A2 EM evaluator. The E9 hidden cost is real: second-derivative machinery for the winding integrand does not exist. | 2–4 w | One `ζ′`-zero-free box left of the line. **Not the Speiser wall.** Defer past week 4. |
| F3-7 | `RH_li_rung0_kernel` | `CONSUMER_SWEEP` route: Mathlib `riemannZeta_one` + an Euler–Mascheroni lower bound gives `taylorCoeff riemannXi 0 = 1 + γ/2 − log(4π)/2`, then `2 + γ > log 4π`. Still needs a certified difference-quotient or series bracket for `logDeriv (φ riemannXi)` at 0. | 2–6 w | The first Li rung with **no Arb hypothesis** — the only rung in the ladder that is not hypothesis-carrying. Genuine, and honestly `hard-known-shape`. |

For each of F3-1 … F3-3 and F3-5, after the artifact is on `main`:
```sh
mission link  <SLUG> --artifact <path-from-campaign-root> --kind lean_module --via direct
mission grant <SLUG>
mission attempt <SLUG> --session "<s>" --route "<route>" --verdict Proved --detail "<what landed, axioms, island>"
```
**Conflict warning, from `MIRRORMERE_TEAM_REPORT_2026-09-18.md` §3:** C4 — two branches link
`MM_euler_factor_section_offline` to *different* modules; C5/C6 — divergent emitter copies.
Resolve the module choice before any `link`, or the grant records a path that CI does not
build.

---

### F4 — EFFECTIVE CONSTANTS (the standing queue, now unblocked)

The three new critical-path bricks carry **existential** constants. `CONSUMER_SWEEP` §3
shows the inputs for making one of them effective now exist: zeta-23-lean's
`WeilEF/Effective.lean` has `zeta_local_zero_count_explicit : N(t,t+1] ≤ 540000000·log(|t|+3)`
and `zeta_logDeriv_partial_fraction_explicit` with `135000000·log(|t|+3)`.

| op | item | cost | buys |
|---|---|---|---|
| F4-1 | Effective corridor constant: re-run `RvMBridge3.corridor_bound`'s `good_height_real` with the explicit inputs. Remaining seam, named: the compactness step `corridor_small` still needs a numeric bound on `[2,8]`. | 2–4 w | Turns `∃C` into a number on the unique four-consumer blocker (E7 = A3 = B5 = D6). Every downstream effective statement inherits it. |
| F4-2 | Author the node **only after** the constant is in hand. Queue item, not a node today — the roadmap's own "the statement is the work" discipline (§9). | — | Avoids a fourth un-audited draft. |

---

### F5 — THE INSTANCE FACTORY (instrumentation; label it as such, always)

| op | item | cost (measured, not optimistic) | buys |
|---|---|---|---|
| F5-1 | `AND_ladder_h280000` → hypothesis-free form + branch reconcile, then grant. | Blocked on the `rh/million-turing` reconcile, not on compute. | Closes the one anduril open leaf that is actually workable. |
| F5-2 | Ladder CI to 200000 via the prior-block-cache/matrix shape; retire the monolith. | **Measured**: h25000 = 30 min, h50000 = 62 min on the first runners; `H_CI = 50000` today. Linear-ish in block count ⇒ 200000 is ~4–5 h of runner time per full rebuild. | The paper can cite what CI builds rather than what a laptop built. |
| F5-3 | `AND_ladder_1e6` (~1.8M zeros). Roadmap: "nothing structural remains on current T5 machinery, wall-clock only." | Weeks of wall-clock; **disk is the binding constraint, not CPU**. | A number. Not evidence for RH — certified prefixes are morally forced by on-line verification. |
| F5-4 | `AND_ladder_1e9` / `AND_ladder_1e13`. Gated on an unauthored A3 Riemann–Siegel era (theta branch + RS main sum + Gabcke C0 remainder). | Quarters. | **Do not staff.** The gate is three unauthored bricks; the goal node currently makes the campaign look 75 % closed when the real frontier is unregistered. |
| F5-5 | Li prefix throughput to n ≈ 10³. | Days of compute; but N = 1000 means ~1000 simultaneous Arb hypotheses and **the packaging discipline for that does not exist**. | Nothing, until the packaging discipline exists. Build the discipline first or skip. |

**Standing label for everything in F5:** *instrumentation, not evidence.* Roadmap §3
B1 already says so; the plan restates it because F5 is the facet most likely to be
mis-sold in a status update.

---

### F6 — ROUTE C FOUNDATIONS (the only route with a first-anywhere formalization available)

Route C is the outlier of §1.3 and therefore the only route where pre-wall work is not a
re-coordinate of B10. Its three drafts are `STATED NOT PROVED` and have never been read
back.

| op | node | action | cost | buys |
|---|---|---|---|---|
| F6-1 | `RH_dbn_rh_iff_H0_real_zeros` (C4) | `mission audit RH_dbn_rh_iff_H0_real_zeros --auditor "<independent>" --text "<testimony>"`, then prove: F2-2 already lands the complete change of variables (`xiArg_re`, `xiArg_re_eq_half_iff`, `xiArg_surj`, `xiArgInv_im`). | 1–2 w after F2-2 | RH ⟺ all zeros of H₀ real, in AND-ladder grammar. Cheapest real theorem on route C, and F2-2 pays for most of it. |
| F6-2 | `RH_dbn_H0_eq_xi` (C2) | A genuine representation theorem (Mellin ↔ Fourier via Jacobi theta, two IBPs with dominated convergence). Audit first. | months | H₀ = Ξ/8. Gate for C3. |
| F6-3 | `RH_dbn_debruijn_real_zeros` (C3) | de Bruijn 1950: `t ≥ 1/2 ⇒ real zeros`. **First formalization anywhere.** | 1–3 mo after C2 | Λ exists, Λ ≤ 1/2. A publishable first with **no wall risk**. |
| F6-4 | Λ's definition | **Do NOT define Λ before C3** (roadmap C2 row: the `sInf` ill-posedness trap). F2-2's `mem_of_sInf_lt` / `sInf_le_zero_iff` make the trap explicit with monotonicity and well-posedness as *named hypotheses* — use them, do not bypass them. | — | Avoids authoring an ill-posed definition. |
| F6-5 | C7 (P15 effective estimates + barrier) | The one big staffing decision. **Do not commit without a design memo pricing the Ki–Kim–Lee dependency and the mollifier-era constants risk**; the A+B−C validity floor was demonstrated near X ≈ 6·10¹⁰ and G4-scale reuse needs re-derivation, not citation. | 6–18 mo | A certified Λ bound. Must beat Λ < 1/2 (Ki–Kim–Lee) to be non-trivial and 0.2 to beat the published record. |

---

## ═══ HARD LINE ═══

**Everything above this line is pre-wall. None of it is progress toward RH. Everything
below this line is the wall, and none of it is staffed.**

The test for which side an item is on is not difficulty and not novelty. It is: *does the
item's statement, if proved, still leave `RiemannHypothesis` exactly as open as it was?*
For every F1–F6 item the answer is yes. That is why they are staffable.

### WALL INVENTORY — registered, permanently draft, never attempted, decomposition refused

| clause | registry object | status | why unstaffed |
|---|---|---|---|
| A5 / B10 / D11 (one clause) | `MM_zeta_comb_membership` (kind `goal`, draft) and `RH_conjecture` (kind `goal`, draft) | draft **by charter** | RH-equivalent (Weil 1952; Bombieri 2000 on exactly `C_c^∞`). Nothing on `main`, nothing on any `mm/*` branch, and nothing in any facet of this run reduces, weakens or approaches it. |
| C10 | not registered, and correctly so | — | `Λ ≤ 0`. F2-2 now proves *why* the route's own instrument class cannot reach it. |
| `L* = ∞` (the support-graded form) | **not registered — proposed and DROPPED** | — | The same wall in its measurable coordinate, not a second wall. See below. |

**Three proposals from this run are refused, with reasons, so they do not return next week:**

1. **`MM_weil_positive_support_graded` / `WeilPositiveOn` / the `L*` coordinate — DROPPED.**
   Five independent reasons, any one sufficient: the package arrived truncated so the
   statement/deps/route were never delivered; `(∀L, WeilPositiveOn L)` is definitionally
   the campaign goal already carried by `MM_zeta_comb_membership`, which
   `mm/w3c-goal-weil-membership` has already re-authored to exactly that text; the
   `WeilExplicit` vocabulary is **not on main** (`grep` of
   `missions/mirrormere/lean/Statements/MMDefs.lean` returns nothing), so it would be a
   fourth AUTHORED `MMDefs` edit inside an open conflict window on top of unmerged #562,
   #565, #566, #567, #568; `Antitone WeilPositiveOn` is unfolding and the `iff` is
   `HasCompactSupport → ∃L, supp ⊆ [−L,L]` plus specialization; and the motivating number
   is stale — the "record to beat" of L = 0.8 was superseded four days before this run by a
   certified half-width of 1.0625, while the "published floor" `L* ≥ (log 2)/2` is the
   **empty-prime-sum range** (`autocorr g` is supported in `[−2L,2L]`, so `2L < log 2`
   kills every `Λ(n)` term with `n ≥ 2` and leaves only the archimedean term). Clearing
   that floor is vacuous and must not be presented as a bar.
2. **`WeilPositiveOn L` for L beyond the certified window — NOT the wall, but not staffed.**
   A finite, well-posed, genuinely open computational-analytic problem, blocked by the
   Landau–Widom decay law: certification cost is doubly exponential in L, the published
   enclosure at L = 0.8 is already 8.9e-18 … 2.27e-17 and falls to ~3.2e-283 at L = 2. It
   buys about one decimal of L per major effort and never reaches the wall.
3. **A1e (arithmetic FQ ⟺ Selberg element) — a DIFFERENT open problem, not the wall.**
   Bounded below by the Selberg degree conjecture, which has moved exactly one unit
   interval in thirty years (Kaczorowski–Perelli, *Acta* 182 (1999); *Annals* 173 (2011)).
   Roadmap's own estimate: < 5 %, generational. It would not advance A5-W even if it
   closed, because A5-W does not mention the Selberg class.

**One claimed no-go is refused in the other direction:** the route-A facet's "quantitative
kill" — that `λ_min(L) → 0` doubly-exponentially makes the instrument class *provably* the
wrong shape — is not carried. A uniform argument need not exhibit a uniform margin: under
RH the explicit formula proves `∀L, ∀g, W(g⋆g̃) ≥ 0` as a sum of `|ĝ|²` terms, uniform in L
with margin identically zero. Positivity of a quadratic form is a closed condition always,
with or without Landau–Widom. The underlying observation is Zhu's own last abstract
sentence, carefully scoped to *one-stroke certificates*; escalating it to "no
limiting/compactness/interpolation argument can manufacture `∃A ∀L`" is not supported, and
it is anchored on a preprint the facet itself says not to anchor on. **Keep the negative
half** — there is no B7-style truncation seam on the Weil route, because for `supp g ⊆
[−L,L]` the prime side is a finite sum over `n ≤ e^{2L}` and the archimedean side is one
convergent integral — **and drop the kill.**

---

## 4. SEQUENCING

Costs below are the measured ones. Disk is a first-class constraint: the previous team run
filled the 926 GB root volume to zero bytes, which blocks every agent at the tool layer.
`df -h /` at the time of writing: **94 Gi available.** Every block below states its disk
posture.

### Week 1 — integrity, then the harvest

| day | work | disk posture |
|---|---|---|
| 1 | **F1-1 through F1-4.** Gate calls `audit_lean_file`; gate refuses non-proved deps; closure fixpoint extended to `direct` with `closure_override_reason`; `verify` errors on `proved` + `closure_clean=false`. Re-run `mission verify` on all four campaigns and **expect new failures** — that is the point. | No build. Zero. |
| 2 | **F2-4** (B7 ledger, 15 min). **F2-1** + **F2-2** statement authoring and blind read-backs. | `lake env lean` only, on existing island caches. Never `lake exe cache get` in a symlinked island. |
| 3–4 | **F3-4** (`MM_torus_section_dictionary` re-audit) — highest leverage per hour in the plan. Then **F2-3 + F3-1 in ONE module** on the v4.32 quasicrystal island. | One module name per agent on a shared island. After any build: `rm -rf <island>/.lake/build/ir`. |
| 5 | **F3-2**, **F3-3** link+grant from the existing `mm/*` branches. Resolve the C4 module-choice conflict before any `link`. | No new builds. |

**Week-1 decision point (end of day 1):** if F1-1 cannot be landed in a day, **stop all
grants** until it can. A registry that can certify a `sorry` is worse than no registry,
because it launders a false claim into a status table.

**Week-1 tripwire:** if `mission verify` still reports OK on all four campaigns *after*
F1-3 and F1-4 land, the fixpoint is not running — investigate before trusting any closure
flag.

### Weeks 2–4 — discharge and the first effective constant

* **F3-5** (`MM_torus_section_n2_rigidity`) once F3-4 clears. 1 day.
* **F4-1** (effective corridor constant). 2–4 weeks; the single named seam is the numeric
  bound on `[2,8]` for `corridor_small`. **Staff one agent, not a team.**
* **F6-1** (C4 audit + proof) riding F2-2's change-of-variables. 1–2 weeks.
* **F5-1** (`AND_ladder_h280000` reconcile + grant) when `rh/million-turing` lands.
* **F5-2** (ladder CI to 200000) only if runner budget allows: at the measured 30 min /
  25 k block this is ~4–5 h per full rebuild, so it displaces roughly one day of other CI
  per week. **If CI queue time exceeds 6 h/day, defer F5-2 and keep `H_CI = 50000`.**

**Week-4 decision points:**
1. **Effective corridor constant in hand?** If yes, author its node (F4-2) and re-price
   every downstream effective statement. If no, and `corridor_small` has not moved in two
   weeks, record a `Stalled` attempt naming the `[2,8]` bound and re-scope.
2. **C7 go/no-go.** Commit only with a written design memo pricing the Ki–Kim–Lee
   dependency and the mollifier-era constants. **Default is no.**
3. **F5 review.** If any F5 item has been described in a status update as evidence rather
   than instrumentation, stop that item and fix the description first.

### Weeks 5–12 — the two long bets

* **F6-2 → F6-3** (C2 then C3): the de Bruijn 1950 formalization is a first anywhere, on
  the only route whose wall is genuinely distinct, with no wall risk at the rungs. This is
  the plan's primary 12-week bet.
* **F3-7** (`RH_li_rung0_kernel`): the one Li rung with no Arb hypothesis. Secondary bet.
* **F3-6** (`MM_speiser_box_probe`): only if the second-derivative EM machinery is built
  for another reason. Otherwise leave open.
* **Not staffed in 12 weeks:** C7, F5-4, A1e, B9/L-growth, D7, D9, and every item below
  the hard line.

**Falsification tripwires, armed, checked weekly:**

| tripwire | fires when | consequence |
|---|---|---|
| T1 | A certified `λₙ < 0` on any rung | **RH is refuted.** `li_neg_refutes_rh` is wired. Drop everything and verify. |
| T2 | A genuine-data negative defect window, or a band `N(T)` deficit confirmed by an off-line winding-1 box | Same class: a validated refutation payload. |
| T3 | The Weil-form emitter reports a non-positive or indeterminate sign anywhere inside `[−(log 2)/2, (log 2)/2]`, where positivity is a theorem (Yoshida; re-proved Bombieri 2000) | **The emitter is not computing Weil's form** and every enclosure it has ever produced is uninterpretable. Halt all D2/D3 work. |
| T4 | `mission verify` passes on a node whose artifact contains `sorry` after F1-1 lands | The fix did not fix it. Treat every grant since as suspect. |
| T5 | MIRRORMERE registers and grants an **affirmative** uniform-in-N node (as opposed to a refutation-shaped one) within 90 days | §2's reading — that the ladder's only available uniformity is on the refutation side — is wrong; re-open the T3 programme. |
| T6 | Lehmer-pair quality trending to 0 on certified consecutive pairs | Λ pressure; re-prioritize route C. |

---

## 5. WHAT WOULD CHANGE THE PLAN

Ordered by how much they would change it.

1. **A rigorous CCM convergence proof for any infinite subsequence** (Connes–Consani–Moscovici,
   2310.18423 / 2511.22755 deliver provably self-adjoint finite operators whose spectra match
   zeros *numerically*, with the convergence openly identified as the RH content). The roadmap
   calls this "the largest RH event since 1974." **Drop everything and verify.**
2. **A certified `λₙ < 0`, or any T1/T2 tripwire firing.** The program's unique
   decade-scale non-negligible payoff is a certified *refutation* if RH is false. Every
   other line of work is subordinate.
3. **An external formalization of `H_t` / Riemann–Siegel appearing.** C7 and A3 costs
   collapse; F6 goes from primary bet to fast follow, and the 12-week shape is rewritten
   around it.
4. **Mathlib lands Hadamard factorization of ξ at a pin the campaign uses.** The zero-free
   chain's documented ceiling is a *formalization* gap (`ZeroFreePolylog.lean`'s header names
   the missing one-sided `Re ≥ 1` log-derivative bound; `ZeroFreeElementary.lean` names the
   missing Hadamard factorization), not a mathematical one. Landing it would make several
   F4 items cheap. Note that this does **not** move the wall.
5. **Mathlib lands automorphic L-functions.** Route A's A1 horizon shortens; still not the
   wall, and A1e stays generational.
6. **Mathlib lands a Fourier transform of measures / diffraction predicates.** The
   `ARITHMETIC_FQ_MEMBERSHIP_SPEC` substrate becomes buildable. Given §1.3(4), build it only
   if A0 produces a non-vacuous membership statement first — otherwise it is a faithful `def`
   of a class with nothing to carry.
7. **T3 fires** (an affirmative uniform-in-N node): §2's central reading is wrong, and the
   torus-section programme returns to the board.
8. **A real barrier result appears** — from anyone, including this house. The bar, set by
   §2.4: it must refute a clause about a *single member*, not a universal over a class; it
   must not be refuted by exhibiting a class member that satisfies the analogue; and it must
   survive being checked against which axioms the house's own artifacts actually consume.
   The FE-uniformity attempt failed all three. If one ever passes, the wall inventory above
   becomes a closure argument and the whole program is re-scoped as instrumentation plus a
   published negative result.
9. **E5 fails on a witness class** (finite-grade interderivability between faces): the
   one-clause thesis is refuted at finite grade and the program reorganizes as a route
   portfolio rather than four views of one wall.
10. **Disk: the 926 GB volume passing 90 % used.** Not a mathematical event, but it halted
    the previous run at the tool layer. `df -h /` before every build; under 20 Gi free,
    stop and report.

---

## 6. THE HONEST LEDGER

### What this program can now prove

Kernel-checked, axiom-guarded, on `origin/main` or a named island:

* **The classical zero-free chain**, up to and including an **effective** de la Vallée-Poussin
  region with a concrete constant (`RH_dlvp_region_effective`, `RH_dlvp_zero_free_region`),
  plus the elementary `γ⁻⁵` and polylog regions and the sharp near-line growth bound.
* **Backlund `S(T) = O(log T)`** carrying only zeta-nonvanishing on the segment.
* **The roadmap's entire critical path**, kernel-checked on the `rvm_bridge` island
  (Lean v4.33.0-rc2, importing zeta-23-lean as a Lake dep), all
  `[propext, Classical.choice, Quot.sound]`: cumulative Riemann–von Mangoldt
  (`RvMBridge2.rvm_unconditional`), the corridor bound (`RvMBridge3.corridor_bound`), and
  the limit explicit formula in `HasSum` form (`RvMBridge4.limit_explicit_formula`).
  **Their constants are existential, not effective.**
* **A finite zero-localization ladder** to height 640000 (1,072,715 zeros on the critical
  line), with Arb enclosures entering as explicit HYPOTHESES — the documented trust boundary.
* **The finite Bombieri–Lagarias positivity core** (`RH_bl_finite_multiset`), which carries
  zero zeta-specific content by design.
* **The Bragg/diffraction bridges**: the finite explicit formula in diffraction form as a
  kernel identity with the primes, its trace reading, the defect instrument and its
  off-line-pair counting theorem, the certified defect witness pair.
* **A growing library of negative controls and no-gos**: reflection-invariant functionals
  cannot orient a zero; bare finite operator existence is vacuous; finite Euler sections are
  off-line at every rung; region shape does not entail a uniform margin; uniformly robust
  heat-flow schemes cannot reach `Λ = 0`.

### What it cannot prove, and has no method for

* **The wall clause, in any of its coordinates.** `∀n, 0 ≤ Re λₙ`; Weil positivity on all
  of `C_c^∞`; defect-0 membership of the regularized triple; `Λ ≤ 0`; `ζ′ ≠ 0` on
  `0 < Re s < 1/2`. Not approached, not weakened, not reduced by anything in this run.
* **Any uniform-in-parameter statement** at the seams: a bounded `n(T)` for B7; a fixed
  margin `δ` for the rate frontier; a support radius beyond the certified window.
* **An effective form of the three new bricks.** Queued; F4-1 is the first attempt.
* **`RvMUnboundedMeanDensity` from finite data** — surveyed 2026-09-15, no unconditional
  kernel proof exists in corpus or Mathlib; linear zero-count bounds provably do not suffice.
* **A barrier theorem.** The one attempted in this run was refuted (§2.4), and the "uniformity
  vs instances" framing that motivated the run does not yield one.

### What this run actually produced

Four kernel-clean no-gos, one exact statement of the B7 alternation together with the
demonstration that closing it is not RH progress, one verified refutation of a proposed
barrier, one verified identification of three of the four wall clauses as a single clause,
and one verified hole in the grant gate that could have certified a `sorry` as `proved`.
None of that is progress toward RH. All of it is progress toward *not being wrong about*
RH, which is the only kind of progress this program has ever been able to make honestly.

### The sentence that stays at the top of every artifact

**`conjecture1_proved = False`.**

---

*Provenance: `origin/main` @ `2b419fd04`; sibling worktrees `wall/barrier`,
`wall/adversary` @ `399eebc23`, `wall/backlogmap` @ `8b46eb07`, `wall/rate-frontier` @
`e363d520b`, `wall/route-c-debruijn` @ `2bc20cab1`. Corpus claims carrying file:line were
re-read in this worktree. The route-B facet package arrived truncated and its unseen
operations were not executed or recommended. No Lean was built for this document; disk at
write time: 94 Gi free on a 926 Gi volume. No emoji in any Lean or Python this plan
proposes. `conjecture1_proved = False`.*
