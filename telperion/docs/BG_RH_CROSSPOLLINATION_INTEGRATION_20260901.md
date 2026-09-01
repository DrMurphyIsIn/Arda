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

## Next step (Phase 3, the equality engine's real test)

The leaf is the *easy* bulk case (1 field, `Bof = Aarg`). The genuine test of the Phase 1 equality engine
is the **armmid** (degree 2, the `+0.243` free-box violator): its incident fields are the pinned leaf
message (`h_leaf→armmid = 1`, a recursion equality) and the center field (a reachable range), so the
free-box positivity is FALSE but the realizable-variety positivity holds — exactly the case where the
equality multipliers `λ_j·h_j` are load-bearing. Set that up, clear the exponent with integer `k`, and
run the equality-constrained finder (with a Bernstein path for the box directions).
