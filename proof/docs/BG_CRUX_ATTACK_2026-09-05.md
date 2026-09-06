# BG open crux — attack analysis (2026-09-05)

Direct attempt on the sole open crux (the tie-adjacent hard core) + the assembly, from all three handles.
Honest outcome: each vector confronts a specific, characterized obstruction. `conjecture1_proved = False`.

## Vector 1 — the residual 5 `cb`-heavy Kelmans cells `{(0,5),(1,4),(1,5),(2,5),(3,5)}` (merge handle)

- The dichotomy (`R47R7KelmansDichotomyCert`) proves the step INCREASES iff the donor is loaded; these cells
  have a HEAVILY-loaded donor (`cb∈{4,5}`), so the step is genuinely increasing (`three_hub_residual_probe`:
  0 real decreases). The cells are TRUE — the issue is purely the CERTIFICATE, not the math.
- Box-positivity (`emit_nonneg_orthant`, corners of the `(σ_Q, σ_S)` box) is too crude for large `cb`: the
  `σ_S = 0` corner fails, and the parallel lane confirmed even the refined `(db-2)·z1` sub-box + explicit
  C-mover term fails at its corner. So a box/lower-bound refinement (incl. constrained-SOS with a `σ_S ≥ σ_min`
  bound) does NOT close them — that refinement was already tried.
- The genuine next attack: a STRONGER-than-box certificate on the EXACT cell polynomials — Handelman (products
  of the constraint polys) or Putinar with the exact recursion EQUALITY (`z_C·ρ_C` as an equality constraint,
  not a box bound), via `emit_handelman`/`find_putinar_certificate(equalities=…)`. **OBSTRUCTION:** the exact
  cell polynomials + the recursion equality live in the parallel lane's `kelmans_mixed_load.py` /
  `three_hub_residual_probe`, which is NOT synced into this repo. Attacking them here requires either syncing
  that Python or re-deriving the 3-hub Kelmans cavity step from scratch. This is the concrete, non-box attack —
  it is not ruled out, it is un-attempted here for lack of the synced polynomials.

## Vector 2 — Gap-1 quantitative strict amplitude (rate handle, my territory)

- `Aobj = (d+1)/d·Ztot(dtSub) − Zopen/d`; the sharp `(26/23)/rhoB` bound needs the QUANTITATIVE strict off-tie
  amplitude `rhoB^n − Ztot(dtSub)` (verified irreducible: `Zopen`-only reframing overshoots at every tie K).
- This amplitude = the SUBACTION's off-tie slack: `bell b ≤ −ρwit(root)`, `ρwit` margin-0 only at the tie, so
  off-tie the SUB inequalities carry POSITIVE slack — the quantitative margin. `master_ineq_strict` proves the
  QUALITATIVE `bell < 0` off deg-6; the quantitative `bell ≤ −δ(b)` (with a computable `δ`) is the open step.
- **OBSTRUCTION:** concrete pieces (per-arm strict deficit `armRate11(j) < 1` for `j≠5`, computable rationals)
  do NOT compose to the full-backbone amplitude without the spine/rooting/cherry contribution — the quantitative
  slack is a whole-backbone quantity, and the subaction telescoping's exact off-tie margin is the open work.

## Vector 3 — the assembly (tree→hub / Obligation-A)

- The Kelmans certs are ABSTRACT polynomial nonneg facts (`0 < poly(x,y)`); Hdom needs `Aobj(backboneU s) ≤
  Aobj(tie)`. Wiring requires proving `Aobj(merge) − Aobj(s) = poly/denom` in the cavity model (the emitter's
  untrusted derivation, formalized). **OBSTRUCTION:** the smallest Balanced+Capped two-hub base case (two hubs,
  each ≥5 load-5 arms) is a ~112-vertex tree — NOT a small concrete unfolding; the connection is parametric
  cavity algebra (`Ztot_hubNode_dressed`), the parallel lane's tree→hub model.

## Honest verdict

The crux is genuinely the open research boundary; my direct attempt confirms and SHARPENS why: the residual
cells are TRUE and need a stronger-than-box certificate on polynomials not synced here (concrete, un-attempted);
Gap-1 needs the quantitative subaction slack (whole-backbone, open); the assembly base case is parametric-huge.
No vector yields a session-scale closure; the one concrete un-attempted attack (Handelman/exact-equality on the
synced residual polynomials) is the sharp next move IF that Python is synced. `conjecture1_proved = False`.
