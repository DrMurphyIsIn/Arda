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

## Status

This is a **reformulation**, not a proof: the identity is verified exhaustively and recasts the open lemma
as monomer-dimer extremality, giving a concrete foundation (Heilmann-Lieb) for the global argument. It does
NOT close `Hnorm`. `conjecture1_proved = False`.
