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

## RESOLVED: crux (a) for the ADJACENT leaf move — no gate needed, defect-reduction alone certifies

The structural-implies-analytic link is now a complete, formalizable proof for the adjacent case (`par_v`
a child of `par_w`; root at `par_w` by `Aobj` root-invariance):

1. **`nB = 0 ⟹ non-defect-reducing.**  If `par_v` has no children besides the target leaf `v`, then
   `par_v = node[v]` is a CHERRY (piece) before and `par_v' = node[stem]` an ARM (piece) after; no
   piece-status changes anywhere, so `strDefect` is unchanged. (Pure `isPiece` computation — Lean-ready.)
2. **Hence `strDefect`-reducing ⟹ `nB ≥ 1`** (contrapositive).
3. **`N` has nonnegative `QB,QO` coefficients**, so `N ≥ N0 := N|_{QB=QO=0} = nO·(nB·nO + nB + nO − 2)`.
4. **`nB ≥ 1 ⟹ nB·nO + nB + nO ≥ 2 ⟹ N0 ≥ 0`** (arithmetic), hence `N ≥ 0`, hence
   `increment = PB·PO·N / [2(nB+2)(nO+1)(nO+2)] ≥ 0`.

Verified exhaustively (3025 adjacent configs, 90 defect-reducing): **0 with `nB=0`, 0 with Aobj decrease**;
and `N ≥ 0` for every realizable `nB≥1` (0/300000). So **every defect-reducing ADJACENT leaf-onto-leaf move
is Aobj-nondecreasing — unconditionally, no degree gate.** This closes the analytic half of crux (a): the
degree gate was only a sufficient proxy; the true certificate is the structural fact `defect-reducing ⟹
nB≥1`, which lands the closed form in its provably-nonneg region.

## (a') deeper `par_v` is NOT a clean analogue; and the adjacent move's coverage

- **(a') deeper `par_v` needs the gate.** For `par_v` deeper than a child of `par_w`, "defect-reducing
  alone" does NOT certify: the random deeper sweep found **35 Aobj-DECREASING defect-reducing moves** (all
  with the gate violated, `deg(par_source) <= deg(par_target)`); the degree gate rescues them (322/322 safe).
  So the clean, gate-free `defect-reducing ⟹ nB≥1 ⟹ N≥0` result is **adjacent-specific**; the deeper case is
  a `defect-reducing + gate` statement over a different (path-denominator) closed form — genuine further work.
- **Coverage of the adjacent move.** On the genuine core (n<=14): sibling `FlpStepAt` 78.2% (394);
  **adjacent defect-reducing leaf move 29.2% (147); union 82.1% (414) — +20 trees over sibling.** So the
  adjacent move is a real, cleanly-certifiable coverage extension beyond `FlpStepAt` (worth formalizing).

## Lean formalization plan (adjacent leaf StraightStep — the first extension beyond FlpStepAt)

The move at `par_w = node[leaf_w, par_v, *Other]`, `par_v = node[leaf_v, *Bv]` (nB=|Bv|>=1) →
`node[par_v', *Other]`, `par_v' = node[stem, *Bv]`, `stem = node[leaf]`.

- **usize**: `usize` congruence + `usize(par_v)=usize(par_v')` (leaf->stem is size-preserving at v; leaf_w
  moves into stem). Mechanical.
- **Aobj (`<=`)**: root-invariance (`Aobj_node_perm`) roots the whole tree at `par_w`; then the closed-form
  increment `= PB·PO·N / [2(nB+2)(nO+1)(nO+2)]` with `N = N(QB,QO,nB,nO)` and `N >= N0 = nO(nB·nO+nB+nO-2)`.
  Direct cavity computation (like `twoHub_le_tie` / the PC6 bridge) + `nlinarith`. This is the substantial
  half (needs the closed forms of `node[leaf_w,par_v,Other]` and `node[par_v',Other]`).
- **strDefect (`<`)**: the novel structural core — `nB=0 ⟹ par_v=cherry (piece), par_v'=arm (piece)`, a
  piece->piece change, and `leaf_w` a piece, so the move preserves `strDefect`; hence a `strDefect`-reducing
  instance forces `nB>=1`. Pure `isPiece` computation. Then package the `nB>=1` defect drop.

## Status

**Progress, not full closure.** Monomer-dimer identity verified; crux (a) RESOLVED for the adjacent leaf
move (Lean-ready proof `defect-reducing ⟹ nB≥1 ⟹ N≥0`, no gate); adjacent move adds +20 trees coverage
(-> 82.1%). Open: (a') deeper `par_v` (gate + path-denominator closed form); (b) whole-hub Case-B (global
monomer-dimer inequality; `G1` fails). Does NOT close `Hnorm`. `conjecture1_proved = False`.
