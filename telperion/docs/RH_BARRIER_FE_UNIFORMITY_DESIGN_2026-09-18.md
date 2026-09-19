# The FE-uniformity barrier -- design memo for four registry nodes

*Branch `wall/barrier`, 2026-09-18. Barrier-researcher seat of the faceted-assault run.*
*`conjecture1_proved = False`. No RH progress is claimed here; this memo bounds what a
class of arguments can do, it does not advance any of them.*

## 0. One-paragraph statement

Every RH-equivalence this program owns or targets -- Li positivity (route B), Weil
positivity (routes A and D), de Bruijn-Newman `Lambda <= 0` (route C), Fourier-quasicrystal
membership (route A) -- is a theorem about a CLASS of functions, not about zeta: the class
of entire, self-dual, order-one completed L-functions. Call an argument **FE-uniform** when
every hypothesis it consumes is a member of that bundle. The bundle contains the
Davenport-Heilbronn function, which has zeros off the critical line. Therefore **no
FE-uniform argument can prove any route's wall clause, and one witness refutes all four
routes at once.** The dual half is already in the literature: for the bundle that keeps the
Euler product and drops the functional equation (Beurling systems), Diamond-Montgomery-
Vorhauer showed the classical de la Vallee-Poussin zero-free region is optimal. Both
ingredients are therefore necessary, and neither is sufficient alone.

## 1. What is new, and what is not

NOT new: Davenport-Heilbronn as a negative control (this repo already carries a rigorous Arb
driver for it, `telperion/src/telperion/arb_dh.py`, and a certified off-line zero,
`telperion/docs/QC_DH_SCOUT.md` section 4); the observation that the primes break the
reflection (`RH_WALL_SYMMETRY_THEOREM_2026-09-16.md` says so, and calls the general form a
HEURISTIC bounded below by the Selberg degree conjecture).

New here:

1. **The heuristic becomes a theorem on a named bundle.** No Selberg-class degree conjecture
   is needed. The bundle is explicit, the witness is explicit, the transfer is kernel-checked.
2. **One witness, all four routes.** `FEBarrier.fe_uniform_criterion_is_false` shows that any
   criterion that is EQUIVALENT to the RH analogue throughout the bundle inherits the
   refutation. The roadmap's thesis ("every route relocates RH into one named clause") is
   upgraded: it is the SAME clause in all four, namely the non-bundle residue.
3. **The corpus supplies its own confirmation.** Route B's equivalence is proved on the
   li_positivity island by `biconditional_rh_li_of_hadamard_order_one`
   (`Lc/LiCriterion/XiOrderBridge.lean:68`) -- from `Hadamard.hasFiniteOrder riemannXi` and
   `Hadamard.order riemannXi <= 1`, and nothing else. The name itself certifies the
   FE-uniformity of the whole Li ladder.
4. **The symmetry barrier is scoped, in the kernel.** The wall campaign's FORCED half is
   generalized to arbitrary reflection-invariant maps, and then LIMITED: a
   reflection-invariant functional that decides on-line-ness exactly does exist, so
   reflection invariance is provably NOT an obstruction to RH. See section 4.
5. **The dual ceiling is quoted from the literature** and attached to the program's own
   proved zero-free chain (section 3).

## 2. Barrier I -- FE-uniformity (Davenport-Heilbronn)

Artifact: `telperion/examples/wall_barrier/lean/FEUniformBarrierAM.lean`, namespace
`FEBarrier`, Lean v4.34.0-rc1, elaborated with `lake env lean` against the v4.34 rh
statements island. Sorry-free; `#print axioms` on every theorem returns
`[propext, Classical.choice, Quot.sound]`.

```lean
structure FEData where
  Ξ : ℂ → ℂ
  entire : Differentiable ℂ Ξ
  fe : ∀ s : ℂ, Ξ (1 - s) = Ξ s
  orderOne : ∃ C c : ℝ, ∀ s : ℂ, ‖Ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))

def RHfor (D : FEData) : Prop := ∀ s : ℂ, D.Ξ s = 0 → OnLine s
```

The three transfer theorems, all proved:

* `fe_uniform_rh_is_false` -- one bundle member with an off-line zero refutes `∀ E, RHfor E`.
* `fe_uniform_criterion_is_false` -- and refutes `∀ E, Crit E` for every `Crit` equivalent to
  `RHfor` on the bundle. This is the "one witness kills every route" clause.
* `no_fe_uniform_sufficient_condition` -- the integrator-facing contrapositive: if a lemma
  `L` is FE-uniform and SUFFICIENT for the RH analogue, `L` is false somewhere in the bundle.
  Substituting Davenport-Heilbronn for zeta is a sound refutation test for any candidate wall
  proof whose hypotheses are bundle data.

`zetaFEData` exhibits the completed zeta as a bundle member (entirety
`differentiable_completedZeta₀` and the functional equation `completedRiemannZeta₀_one_sub`
straight from Mathlib; the order bound carried as a NAMED hypothesis because
`XiGrowth.riemannXi_order_le_one` lives in the pinned LiCriterion dependency, not in
Mathlib). So the bundle is non-vacuous on the object the program cares about: an FE-uniform
argument really would apply to zeta.

`mobius_disc_iff : ρ ≠ 0 → (‖1 - 1 / ρ‖ < 1 ↔ 1 / 2 < ρ.re)` is proved as the concrete
instance: it is the entire geometric content of Li's criterion, and it mentions no
arithmetic. The Li ladder transmits the POSITIONS of the zeros and adds nothing to them.

**Trust boundary.** The Davenport-Heilbronn off-line zero enters as an explicit hypothesis
(`hz`, `hoff`) of every theorem, exactly as the Arb enclosures enter the zero-localization
ladder. Its discharge is `QC_DH_SCOUT` section 4: a rigorous argument-principle winding
count, winding number 1 on the rational box `Re ∈ [79/100, 83/100]`,
`Im ∈ [8568/100, 8572/100]`, re-checked at doubled precision and doubled boundary density,
with two negative controls. That is Arb-interval trust, not Lean-kernel trust, and it is
labelled as such.

## 3. Barrier II -- the dual ceiling (Beurling; Diamond-Montgomery-Vorhauer)

Drop the functional equation, keep the Euler product and the integer-counting regularity,
and RH becomes independent of what is left. Broucke-Debruyne-Vindas, *Beurling integers with
RH and large oscillation*, arXiv:2004.11501v2, introduction, VERBATIM (PDF read this
session, pages 1-2):

> "Their Beurling number system has the additional feature that its associated zeta
> function [...] also realizes the classical de la Vallee Poussin zero-free region; in
> particular, the Riemann hypothesis (RH) fails for it."

> "The number system constructed by Diamond, Montgomery, and Vorhauer also provides the
> valuable information that a zeta function might not have a wider zero-free region than
> that of de la Vallee Poussin if we only require that Beurling's property that the integers
> have multiplicative structure and (1.1) hold."

> "Zhang complemented these results by showing that there are also Beurling number systems
> for which, in contrast, the RH and the asymptotic estimate (1.1) both hold."

((1.1) is `N(x) = ρx + O(x^θ)`, `1/2 < θ < 1`. Primary source for the construction itself is
Diamond-Montgomery-Vorhauer, *Beurling primes with large oscillation*, Math. Ann. 334 (2006);
that paper was NOT read this session -- the quotes above are a published restatement.)

Consequence for THIS program: the proved zero-free chain (`RH_zero_free_gamma5`,
`RH_zero_free_polylog`, `RH_dlvp_zero_free_region`, `RH_dlvp_region_effective`) is proved
from the Euler product plus growth -- Beurling-uniform data. DMV says the de la Vallee-Poussin
shape is the CEILING for that data. The recorded ceiling in the program's own history
("only crude -> CLASSICAL region") is therefore a barrier, not a shortfall of effort, and
widening it requires the functional equation, which Beurling systems do not have.

Taken together with section 2: **the Euler product alone caps at de la Vallee-Poussin, and
the functional equation alone decides nothing. Any proof must use both, jointly and
inseparably.** That is the sharpest true statement available about the wall today.

## 4. The symmetry barrier, scoped in the kernel

Artifact: `telperion/examples/wall_barrier/lean/WallBarrierAM.lean`, sorry-free, 3-axiom.

* `no_invariant_orients` -- FORCED, generalized: for ANY map `F : ℂ → α` into ANY type with
  `F (1 - conj ρ) = F ρ`, and ANY decision rule `dec`, it is false that
  `dec (F ρ) ↔ 1/2 < ρ.re` at every off-line `ρ`. The wall campaign's hypothesis "built out
  of `Ξ` and conjugation" is replaced by the only property its proof used. Witness pair
  `(0, 1)`.
* `invariant_detects` -- and the SCOPE LIMIT: `ρ ↦ |Re ρ - 1/2|` is reflection-invariant and
  vanishes exactly on the critical line. RH is a reflection-INVARIANT predicate
  (`onLine_reflect`), so reflection invariance is provably NOT an obstruction to RH.

Read together: "the RH wall is a symmetry theorem" is TRUE for ORIENTATION and FALSE for RH.
Any barrier claim that upgrades FORCED into an obstruction to RH proves too much and is
refuted by `invariant_detects`. This is a correction to the reading of
`RH_WALL_SYMMETRY_THEOREM_2026-09-16.md`, not to its theorem.

## 5. Registry operations (exact; run inside `telperion/` with the py3.9 shim)

Shim prefix, used for every command below:

    PYTHONPATH=src python3 -c "import sys,tomli; sys.modules['tomllib']=tomli; from telperion.cli import main; sys.argv=[...]; sys.exit(main())"

**OP 1 -- vocabulary.** Add an AUTHORED block to `missions/rh/build_rhdefs.py`: a literal
`FE_BARRIER_BLOCK` containing `namespace FEBarrier` with `OnLine`, `FEData` and `RHfor`
exactly as in section 2, appended to `parts` after `BOMBIERI_LAGARIAS_BLOCK`, then regenerate
with `python3 missions/rh/build_rhdefs.py`. Do NOT hand-append to `RHDefs.lean`.

**OP 2 -- node `RH_barrier_orientation_only`** (kind `lemma`, no deps; statement is the
`WallBarrierAM.RH_barrier_orientation_only` registry form, which needs no new vocabulary):

    sys.argv=['telperion','mission','add','rh','RH_barrier_orientation_only',
      '--kind','lemma',
      '--title','Reflection invariance obstructs ORIENTATION only -- not RH (symmetry-barrier scope limit)',
      '--statement-file','<path to the registry-form theorem text>']

then `mission audit` (blind read-back, draft -> open) and `mission grant` against
`telperion/examples/wall_barrier/lean/WallBarrierAM.lean`.

**OP 3 -- node `RH_barrier_fe_uniform`** (kind `lemma`, deps
`RH_li_ladder_reduction,RH_bl_explicit_formula`; requires OP 1):

    sys.argv=['telperion','mission','add','rh','RH_barrier_fe_uniform',
      '--kind','lemma','--deps','RH_li_ladder_reduction,RH_bl_explicit_formula',
      '--title','No FE-uniform argument proves any route wall clause (Davenport-Heilbronn substitution)',
      '--statement-file','<path to fe_uniform_criterion_is_false + no_fe_uniform_sufficient_condition>']

then `audit`, then `grant` against
`telperion/examples/wall_barrier/lean/FEUniformBarrierAM.lean`.

**OP 4 -- ledger, not nodes.** Barrier II is not formalizable today (no Beurling systems in
Mathlib) and must NOT be registered as a node. Record it as attempts against the four
zero-free nodes:

    sys.argv=['telperion','mission','attempt','rh','RH_dlvp_region_effective',
      '--note','BARRIER (DMV 2006 via arXiv:2004.11501): the de la Vallee-Poussin shape is optimal for Euler-product-plus-N(x)=rho x+O(x^theta) data; widening it needs the functional equation. Not a defect of this node -- a ceiling on its method.']

(and the same for `RH_dlvp_zero_free_region`, `RH_zero_free_polylog`,
`RH_zero_free_gamma5`; check the `attempt` flag names against `mission attempt --help`
before running -- the flags were not exercised this session).

**OP 5 -- do NOT register** a node asserting the Davenport-Heilbronn off-line zero. It is an
Arb-interval certificate, not a kernel theorem, and the program's convention is that such
facts enter as HYPOTHESES of the consuming theorem. The hypothesis form is already in place
in section 2's theorems.

## 6. Scope limits, stated as sharply as the claims

1. **This is not an unprovability result.** It is relativization-grade: it rules out
   arguments uniform in a named bundle and says nothing about arguments that use the Euler
   product, `Lambda >= 0`, or the certified zero inventory. RH is presumably decidable by
   some proof; nothing here bears on that.
2. **It does not devalue the instruments.** The Li ladder, the Gram/defect inertia
   instrument, the diffraction reading and the explicit formula are correct transporters.
   The claim is only that they carry no arithmetic of their own: whatever decides RH must
   enter as INPUT (the `Lambda` coefficients on the prime side, the theta kernel's
   positivity, the certified inventory), never as machinery.
3. **No conflict with the 17 proved RH nodes.** None of them asserts RH, Weil positivity or
   Li positivity; the zero-free chain is proved from the Euler product, outside the bundle.
   A barrier that contradicted a proved node would be wrong, and this one does not.
4. **Route C's membership in the bundle is NOT verified.** The de Bruijn-Newman flow needs a
   kernel `Phi` with decay and positivity properties; the Davenport-Heilbronn analogue is a
   SIGNED theta combination and may fall outside the class on which `Lambda <= 0 iff RH` is a
   theorem. Route C's inclusion in section 2's "all four" is therefore CONJECTURAL and is
   flagged as such. Routes A, B and D are verified: Li's criterion is an order-one Hadamard
   statement, and Weil's criterion is an explicit-formula statement, both bundle-uniform.
5. **Barrier II's primary source was not read.** Two verbatim quotes from a published
   restatement (arXiv:2004.11501v2) carry it. Anyone relying on the DMV constants should read
   Math. Ann. 334 (2006) directly.
6. **The bundle could be too weak.** If a future argument uses a bundle clause this memo did
   not list (say, a Ramanujan-type coefficient bound that Davenport-Heilbronn fails), the
   barrier does not apply to it. That is the honest way past this barrier, and naming such a
   clause is the most valuable thing a route can now do.

## 7. Next step

The one move that converts this memo into a hard in-corpus theorem: **generalize the
LiCriterion chain from `riemannXi` to an abstract `f` satisfying `FEData`.** The upstream
package proves everything for `riemannXi` specifically, but its own proof structure
(`biconditional_rh_li_of_hadamard_order_one`) already shows the chain never uses zeta. With
the abstract version in hand, `fe_uniform_criterion_is_false` instantiates at Li positivity
with no hypothesis left over, and the Davenport-Heilbronn Arb certificate delivers a
kernel-checked "Li positivity is false for D" -- a formal barrier instance, not a
transfer schema. Estimated cost: the Hadamard-factorization half is already abstract in the
package (`Hadamard.hadamard_factorization_general`); the work is re-routing
`xi_weighted_genus_one_of_hadamard_order_one` and
`xi_factorization_prod_with_multiplicity_of_hadamard_order_one` through a variable `f`.
