# Integrating the RH cross-pollination probe into the BG discharge plan (2026-09-01)

The parallel RH session ran its box-positivity toolkit against the BG discharge core and produced a
handoff (findings F1–F4). This note reconciles it with the BG session's own Phase 0/1/2 results — they
**converge**, and together they refine the plan from "find a universal `τ`" to a **bulk/tie split**.
`conjecture1_proved = False`.

## What the RH probe found (their F1–F4)

- **F1 — backend transfers.** The box-Positivstellensatz finder (`find_handelman_certificate`) and the
  Putinar SDP finder (`emit_constrained_sos`, finder mode) run locally (cvxpy + CLARABEL/SCS) and are
  RH-dogfood-validated. The certify→reconstruct→emit loop is real.
- **F2 — polynomialization.** `τ` sits in an *exponent*: `exp(11φ_v) = Aarg_v^11 · ∏_u Bof_{v,u}^{−11τ} ≤
  621/64`. A polynomial certificate therefore needs `11τ ∈ ℤ`: set `k_{v,u} := 11τ_{v,u} ∈ {0..11}` with
  `k_v + k_u = 11` per edge. The discharge becomes an INTEGER edge-labeling.
- **F3 — the tie is off-grid (exact, on S(40,5)).** The per-tree LP saturates `F*` exactly
  (`φ = 0.20659` at leaf/armmid/center, slack 0), but the tight shares are OFF the `k/11` grid
  (`τ_leaf ≈ 0.462 ∈ (5/11, 6/11)`, `τ_armmid ≈ 0.826`) and solve `A_v − Στ B = F*` with **transcendental**
  coefficients (ratios of logs of rationals). At `k=5` the leaf violates; at `k=6` the armmid violates —
  so **no integer-`k` (polynomial) discharge is tight at the tie**. SOS provably cannot certify the tie
  config directly.
- **F4 — realizability is load-bearing.** The naive box `h ∈ [0,1]^k` is UNSOUND: a leaf *sends* message
  `1`, so its back-field is pinned (`hp = 1`), and the loose box contains unrealizable points where
  `φ_v > F*` for every `τ`. The certificate must run over the **BP-consistency variety** (the cavity
  recursion), not the free box.

## How this matches the BG session's independent results

- **F3 ⇔ BG Phase 0 + Phase 2.** BG Phase 0 (`bg_phase0_pertree_feasibility`) independently found *every*
  tree feasible with `F*` **sharp** (worst gap `+5.6e-17`), and BG Phase 2 (`bg_phase2_tau_locality`)
  found the universal-`τ` out-of-sample gap **shrinks but never reaches 0** (`0.046 → 0.02 → 0.006`).
  F3 explains *why*: the exactly-tight `τ` is transcendental, so no closed-form/grid `τ` — and no
  finite regression — can hit it. **Corollary: stop trying to fit a single universal `τ`.**
- **F4 ⇔ BG Phase 1 (this session).** BG Phase 1 just extended the SOS/SDP engine with **free equality
  multipliers** `p = σ_0 + Σσ_i g_i + Σλ_j h_j` (commit `250d428`). The equalities `h_j = 0` are exactly
  the cavity-recursion / BP-consistency constraints F4 says are mandatory — the engine now certifies over
  the **reachable variety**, not the free box. F4 is the motivation; Phase 1 is the tool.
- **New tie configs (BG extends F3).** The RH probe examined only `S(40,5)`. BG Phase 0 found the tie is
  hit by a *variety* of shapes: `S(k,5)` **and** caterpillars `cat[8,4,6,5]`, `cat[5,9,3]` (all exactly
  `F* = 0.206586`). So the saturating set is richer than the broom family — relevant to cover-completeness.

## The refined plan: BULK / TIE split (supersedes "derive one universal τ")

1. **Model the realizable field box** (BP-consistency = cavity recursion) as equality constraints
   `h_j = 0` — use the Phase 1 engine. (Optionally add reachable-range box inequalities from Phase 0.)
2. **Certify the slack BULK** per integer-degree case with a **fixed rational (or `k/11`-grid) `τ` that
   leaves margin**, via the equality-constrained Putinar finder over the realizable variety. The bulk has
   *strict* slack (non-tie configs), so a non-tight rational `τ` suffices — no transcendental `τ` needed.
3. **Discharge the TIE points by exact `27·23` arithmetic** (`emit_padic` / `FiniteDecide`), NOT SOS —
   F3 proves no polynomial discharge is tight there. Then **prove cover-completeness**: the tie configs
   (`S(k,5)` + the caterpillar ties) are the ONLY saturating shapes, so bulk-cert + tie-arithmetic covers
   all trees (the `emit_preconnected_cover` sign-cell discipline is the template).
4. **Do NOT chase a single closed-form `k/11` `τ` tight everywhere** — F3 (and BG Phase 2) show it cannot
   exist.

## Honest limits (unchanged)

The crux is untouched by tooling: the **monotonicity reduction to finitely many degree cases** (is it
finite *and* complete?) and the **tie arithmetic** are the new mathematics. RH de-risks the *backend*
(a validated cert→emit→verify loop, now equality-augmented) and supplies the *reframing* (search the
cone / split at the tie), but the wall — cover-complete degree-case reduction + the `27·23` tie — remains
open research. `conjecture1_proved = False`.

## First real BG bulk certificate (leaf discharge) — DONE

`bg_leaf_discharge_bernstein.py` certifies the simplest bulk vertex, the leaf. A leaf sends message `1`,
so `Bof_leaf = Aarg_leaf` and `exp(11φ_leaf) = Aarg_leaf^{11−k}`; the `k=4`, neighbor-degree-3 discharge
clears (denominators removed) to

    Q(h) = 621·3^7 − 64·(3+h)^7 ≥ 0    on the reachable box h ∈ [0,1].

**Certified EXACTLY at degree 7** (no elevation): all Bernstein coefficients `b_i ≥ 0` (min `= 309551`),
so `Q = Σ_i b_i·C(7,i)·h^i·(1−h)^{7−i}` — an exact Positivstellensatz certificate over `[0,1]` (each
`h^i(1−h)^{7−i} ≥ 0` there). This is the first real BG bulk discharge certified over the reachable field
range.

**Tooling gap found.** The generic `find_putinar_certificate` (SDP→rational rounding) and
`find_handelman_certificate` (subset enumeration) both stall on this degree-7, ~10^6-coefficient box
polynomial — Putinar's denominator-ladder rounding can't match `10^6`-scale Grams, Handelman's column-
subset search is `C(36,8)`. The **Bernstein / degree-elevation path** is the right engine for univariate/
box discharge polynomials (exact, immediate, guaranteed to succeed by Bernstein's theorem for a positive
polynomial). Phase-1 follow-up: add a Bernstein fast-path to `find_handelman_certificate` for box cases
before the subset enumeration.

## Armmid discharge CERTIFIED (the hardest bulk vertex) — DONE

The armmid (degree 2, the RH probe's `+0.243` free-box violator, hardest bulk vertex) is now certified
over a realizable sub-box. Exact structure (verified against `bethe_terms` on `S(k,5)`; leaf neighbor
deg 1, center neighbor deg 6, one free field `g = h_{center→armmid}`, leaf message pinned to 1):

    Aarg_v = (18+g)/12,   Bof_leaf = (18+g)/(12+g),   Bof_other = (18+g)/18.

Three findings:

1. **Realizability removes the free-box violation.** The `+0.243` was the *free* box `h_leaf ∈ [0,1]`
   including the unrealizable `h_leaf = 0`. Pinning the leaf message to `1` (its recursion value) drops
   the armmid to a 1-field problem in `g`, with real slack `−0.0077` at every `g` (feasible everywhere,
   NOT tie-dominated — an earlier worry, refuted).

2. **The `11τ ∈ ℤ` grid (F2) is too coarse; a finer grid resolves the bulk.** Integer-11 discharge fails
   the armmid by `+0.024` over the whole range (the tight `τ_leaf = F*/log Bof_leaf ≈ 0.538` sits between
   `5/11` and `6/11` — F3, concretely). Raising the grid to `k/33` (bound `exp(33φ) ≤ (621/64)^3`, still
   polynomial) leaves margin over a sub-range. `bg_armmid_grid_resolution.py` maps this: `D=11 → +0.024`,
   `D=33 → +0.001` (whole wide range), and a constant `k/33` `τ` certifies with margin on a sub-box.

3. **The real degree-50 armmid polynomial is Bernstein-certified.** With `(k_leaf, k_other) = (17, 33)`,
   `exp(33φ_arm) = Aarg^{33}·Bof_leaf^{−17}·Bof_other^{−33} ≤ (621/64)^3` clears to a degree-50 polynomial
   in `g`; `bg_armmid_discharge_cert.py` gets an EXACT **51-term Bernstein certificate** (all coefficients
   `≥ 0`) over the realizable sub-box `g ∈ [0.5, 0.72]` — so `φ_arm ≤ F*` there with a fixed rational
   `k/33` discharge. First certification of the hard 2-edge bulk vertex over the reachable variety.

## Honest scope of the armmid result

One sub-box of one local case (deg-2 armmid + leaf + deg-6 center). The full armmid still needs: (a) the
exact reachable `g`-range (a reachability computation), (b) tiling it with finitely many sub-boxes, each a
constant rational `τ` (the optimal `τ` drifts with `g`, so one constant `τ` leaves `+0.001` over the whole
wide range — piecewise fixes it), and (c) the tie at `g → sup` where the tight `τ` is transcendental →
exact `27·23` arithmetic. And there are other local cases (other neighbor-degree configs). But the METHOD
is validated end-to-end: **realizability + finer-grid rational `τ` + Bernstein certifies bulk vertices.**

## Next steps

1. **Reachable-range + tiling.** Compute the exact reachable `g`-interval for each local case and tile it
   with sub-boxes, each certified by a constant `k/D` `τ` (a finite cover — `emit_preconnected_cover`
   discipline for completeness).
2. **The tie arithmetic.** Isolate the `g → sup` saturation and discharge it by the exact `27·23` identity
   (`emit_padic`), not SOS — F3 proves no polynomial `τ` is tight there.
3. **Emit Lean.** Feed the Bernstein certificates through `HandelmanEmitter` / the equality-augmented
   `ConstrainedSOSEmitter` to kernel-gated Lean atoms.
