# Reformulation: `Aobj` is a monomer-dimer partition function — the global-argument foundation

## The identity (verified exhaustively, 0/986 mismatches, trees n<=12)

For a tree `T` the matching-sum identity `per(L(T)) = Σ_{matchings M} ∏_{v unmatched} deg(v)` divides
through by `∏_v deg(v)` to give:

    Aobj(T) = per(L(T)) / ∏_v deg(v)
            = Σ_{matchings M of T}  ∏_{(u,v) ∈ M}  1/(deg(u)·deg(v))
            = Σ_{matchings M}  ∏_{v matched by M}  1/deg(v).

So **`Aobj` is exactly the monomer-dimer (matching) partition function of `T` with edge activities
`w_{uv} = 1/(deg(u)·deg(v))`.** (Checks: `P3` = `1 + 1/2 + 1/2 = 2`; star `K_{1,3}` = `1 + 3·(1/3) = 2`.)

This is the same object the cavity engine (`Ztot`/`Zopen`) computes — it is the standard monomer-dimer
transfer recursion — so the whole `R47Tree`/`R47RootRate` machinery is a monomer-dimer solver.

## Why this matters: it moves the open lemma into a studied theory

The `Hnorm` residual (the sole remaining obligation for Conjecture 1, `Hdom` being fully closed) is:

> For every tree `t` with `strDefect t > 0`, there EXISTS an SPR move `t -> t'` with `strDefect t' <
> strDefect t` and `Aobj t <= Aobj t'`.

In the partition-function language this is a **monomer-dimer extremality** statement: a non-backbone tree
always admits a defect-reducing local rewiring that does not decrease the degree-weighted matching
partition function. Two properties of this object are the natural levers for the GLOBAL argument that the
local cavity certificates provably cannot supply (the residual moves fail the `G1` lift-gain — see
`REALOBLB_TYPEW_B0_FINDINGS.md`):

- **Heilmann-Lieb real-rootedness.** The matching polynomial of any graph is real-rooted; monomer-dimer
  activities inherit log-concavity / interlacing structure. Candidate: express the SPR increment as a
  ratio of matching polynomials and use interlacing to sign it.
- **Edge-deletion recursion + correlation.** `Z(T) = Z(T∖e) + w_e · Z(T∖{u,v})` (for the FIXED-weight
  polynomial) and negative edge-correlation (Heilmann-Lieb) constrain how relocating a branch changes `Z`.
  The complication is that an SPR move also RE-WEIGHTS every edge at the two endpoints (degrees shift), so
  the clean fixed-weight recursion must be combined with a degree-reweighting accounting.

## The exact obstruction, in this language

The per-move increment (acted node a child of a degree-`k` parent, other children `qSum = QO`) is
`∝ (1+QO/k)·G1 + (1/k)·G2`, safe iff `G2 >= (k+QO)·(−G1)`. The residual moves have `G1 < 0` (they lower the
acted node's `Ztot`, i.e. its local matching partition weight), so safety couples to the global degrees
`(k,QO)`. A global monomer-dimer inequality (not a local cavity cert) is exactly what would bound this.

## Heilmann-Lieb attempt — findings toward the global argument

Three probes toward signing the SPR increment (all exact, exhaustive where noted):

1. **Degree sequence does NOT determine `Aobj`** (35/67 sequences on n<=10 carry >1 distinct value). So the
   argument cannot be pure degree-majorization — it must use the matching STRUCTURE. (Rules out a whole
   family of would-be-simple proofs.)
2. **The fixed-weight deletion recursion `Z(T) = Z(T∖e) + w_e·Z(T∖{u,v})` holds** (the HL lever is
   available); the only wrinkle is that an SPR move re-weights edges at the two endpoints (degrees shift).
3. **A CLEAN SUFFICIENT CONDITION for the leaf move.** Over all 612 defect-reducing leaf-onto-leaf moves
   (n<=12): every Aobj-DECREASING one has `deg(par_source) <= deg(par_target)`. Equivalently

       (defect-reducing leaf move)  AND  deg(par_source) > deg(par_target)   ==>   Aobj nondecreasing

   with **0 violations**. This is the degree-equalizing gate, and it is SUFFICIENT (not necessary — most
   safe moves violate it, which is why the gate alone under-covers).

## The precise remaining crux

The gate `deg(par_source) > deg(par_target)` signs the leaf-move increment ONLY in combination with
defect-reduction: the raw closed form `N` (see `REALOBLA_FLP_B0_FINDINGS.md`) is sign-indefinite at
`nO=1, QO<1/9`, but those bad configs are exactly the NON-defect-reducing ones. So the open crux is:

> **(crux)** show that a defect-reducing leaf move with `deg(par_source) > deg(par_target)` cannot land in
> the `N<0` region (`nO=1` with a high-degree source-sibling) — i.e. link the STRUCTURAL defect-reduction
> hypothesis to the ANALYTIC safe region of `N`.

Plus the whole-hub (Case-B) family — needed for the last ~8% — whose increment is not even degree-gate-safe
(1529 defect-reducing negatives survive the gate; `G1` lift-gain fails), so it needs a genuinely global
monomer-dimer inequality, not a gate.

## Status

This is a **reformulation + partial result**, not a proof: the monomer-dimer identity is exhaustively
verified; the degree-equalizing gate is a clean SUFFICIENT condition for defect-reducing leaf moves; and the
open crux is now pinned to two precise sub-problems (link defect-reduction to `N`'s safe region; a global
inequality for the whole-hub family). It does NOT close `Hnorm`. `conjecture1_proved = False`.
