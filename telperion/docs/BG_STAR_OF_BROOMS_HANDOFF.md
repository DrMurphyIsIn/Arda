# Handoff — Brualdi–Goldwasser / star-of-cherry-brooms (2026-08-31)

Entry point for the next session. Branch `bg/combinatorial-program` (merged to `main`). `conjecture1_proved =
False` throughout. All claims below are exact (`Fraction` via `telperion.matching_free_energy.rho`) and, where
stated, kernel-gated (`lake build` green in CI: jobs `bg-arm-balancing-compiles`, `bg-broom-optimum-compiles`).

## TL;DR — what changed this session

1. **The prior target was refuted (exactly).** The length-2-arm caterpillar does **not** maximize the Laplacian
   ratio `π(T) = per(L)/∏deg`. This corrects a misreading of Pant 2026 (arXiv:2605.14176): Pant gives caterpillar
   *counterexamples* to Wu–Dong–Lai, and leaves the maximizer **open**.
2. **New result (novel, literature-confirmed, exact).** The **star-of-cherry-brooms** `S(k,c)` — one central hub
   joined to `k` branch-hubs of degree `c+1`, each carrying `c` length-2 cherries — beats Pant's caterpillars.
   Growth rate `F(c) = log(total(c))/(2c+1)`, `total(c) = (3/2)^(c-1)(4c+3)/(2(c+1))`, maximized at **`c = 5`**:
   `total(5) = 621/64`, `F* = log(621/64)/11 = 0.2065864 > 0.205098` (caterpillar sup) `> 0.202733` (WDL).
3. **Also refuted (7th caught overclaim):** the interim P1 step "reduce every tree to the caterpillar family by
   local Z-monotone moves" — n=16 spider `S(3;2,2,2)` is a strict single-edge-swap local max below the family.
4. **Upper-bound proof framework built + reduced** to a single tight pointwise inequality (see §Open).

## Connection to the prior Φ¹¹ program (important)

`total(5) = 621/64` is the **same constant** as the earlier near-star/Φ¹¹ work (`64·243·23 = 621·576`, ties at
`c+k = 5`; see memory `laplacian_proof_state_2026-08-06`, `phi11_not_classical_bg_2026-08-29`). The prior
`near_star_arithmetic_proof.py` proved `Φ ≤ 1` on the near-star family `N(c,k)` with equality iff `c+k = 5` — the
**same `c=5` optimum**. The Φ¹¹ invariant is a *rooted-branch* quantity; this session works the *classical BG*
`per(L)/∏deg`. They meet at `621/64`. **Next session should reconcile the two programs** — the branch-reduction
upper bound here (§Open) is plausibly the missing bridge from the Φ¹¹ near-star result to classical BG.

## What is proven / kernel-gated (safe to build on)

- **Closed forms** (verified `== rho`): two-hub caterpillar `two_hub_Z(a,b)`; star-of-brooms `spider_Z(k,c)`;
  caterpillar transfer `Z_recurrence`; decorated-spider transfer recurrence.
- **`c = 5` discrete optimum** — `BroomOptimumCertificate`, kernel-gated in `examples/bg_broom_optimum` via
  cross-exponentiation `rate(5) > rate(c) ⟺ total(5)^(2c+1) > total(c)^11` (exact `norm_num` rationals).
- **m=2 arm-balancing lemma** — general `∀a,b`: `g(a-1,b+1) − g(a,b) = 2(a-b-1)(2a+2b-1)/(a(a+1)(b+1)(b+2)) > 0`
  for `a ≥ b+2`; kernel-gated in `examples/bg_arm_balancing`.
- **Rooted-branch ceiling** — exhaustive over all rooted branches ≤ 18 vertices: `B(5)` is the *unique* density
  maximizer; robust under large/recursive branch extensions.
- **Finite-n dominance** — `S(19,3)`/`S(15,4)` beat the best caterpillar exactly at n=134/136 (crossover ≈134).
- **Exact Bethe decomposition** on trees (verified `== rho`, N≤12): `log π = Σ_v A_v − Σ_e B_e`, `h ∈ (0,1]`.

## Open (the remaining Brualdi–Goldwasser core)

**Upper bound `F* ≤ 0.2065864`**, i.e. `F* = lim_n (1/n) log max_{|T|=n} π(T) = log(621/64)/11`. The `≥`
direction is proven (exhibit `S(k,5)`). The target is **asymptotic**, not per-tree (small trees exceed `F*`:
`F(P_2) = 0.347`; the max-density-per-n sequence *decreases* to `F*` from above). The correct provable form is a
**bulk bound** `log π(T) ≤ F*·n + C`.

**Reduced to a tight pointwise discharge inequality (this session's advance).** With the exact Bethe form, define
`φ_v = A_v − Σ_{u} τ_{v,u} B_{uv}` for an edge-discharge `τ` (`τ_{v,u}+τ_{u,v}=1`). On the extremal `S(k,5)` fixed
point the minimax LP gives an optimal discharge `(a,b,g) = (0, 0.1737, 0.5380)` making **all three bulk vertex
types saturate `F*` exactly** (`φ_bh = φ_arm = φ_leaf = 0.206586`), center exempt (`0.1226`). So `max = average =
F*` — tight. **Remaining task:** a *universal* discharge rule `τ(d_v, d_u, h_{u→v}, h_{v→u})` with `φ_v ≤ F*` for
every local configuration (degree `d`, neighbour degrees, incoming fields `h ∈ (0,1]`), equality only at the
`B(5)` bulk, off an `O(1)` boundary set. Naive rules are provably spoofed (equal-split by star centers; degree-
weighted by leaves) — the acyclicity/surface barrier.

## Concrete next steps

1. **Attack the pointwise inequality.** Parametrize the universal discharge; reduce to finitely many degree cases
   via monotonicity of `φ_v` in the incoming fields `h` (bound `h ∈ (0,1]`); certify each degree case as a
   rational-positivity / interval / SOS atom (`worst_corner`, `cone`, `emit_constrained_sos`). Target: a
   `bg_bulk_discharge` kernel-gated example.
2. **Reconcile with Φ¹¹.** Check whether the near-star `Φ ≤ 1` arithmetic proof (`R(s)` unimodal, `R(5)=1`)
   supplies the `d = c+1` single-hub case of the discharge, and whether the "no smooth certificate / 23-adic"
   no-go from that program applies here (the `621` = `27·23` factor is the tell).
3. **Paper.** `docs/BG_STAR_OF_BROOMS_RESULT.md` is the draft. Frame as *asymptotic family dominance* + a new
   lower bound on the BG maximum growth rate — **not** a global-maximizer proof. Cite BG 1984, Wu–Dong–Lai 2025
   (DAM 372), Wu–Dong–Lai–Zeng 2024 (arXiv:2402.15669), Pant 2026 (arXiv:2605.14176). Terminology: name it
   *star-of-cherry-brooms* `S(k,c)` and contrast Wu–Dong–Lai's `S(n,a,b)` — "broom" already denotes the
   diameter-constrained *minimizer* in the 2024 paper.

## Key files

| File | What |
|------|------|
| `docs/BG_STAR_OF_BROOMS_RESULT.md` | main results note / paper draft (§5b = proof framework) |
| `docs/BG_PIECE3_OBSTRUCTION_MAP.md` | premise-refutation banner + Pant reconciliation + P1 refutation |
| `src/telperion/spider_broom.py` | `spider_Z`, `broom_total`, `broom_free_energy`, `BroomOptimumCertificate` |
| `src/telperion/transfer_caterpillar.py` | `two_hub_Z`, `arm_balance_delta_g`, `Z_recurrence`, Perron `free_energy` |
| `src/telperion/vdb_exchange.py`, `majorization.py`, `weighted_matching.py` | supporting skills (S1b/S1a/S0a) |
| `examples/bg_broom_optimum/`, `examples/bg_arm_balancing/` | kernel-gated Lean (CI green) |
| tests | `tests/test_spider_broom.py`, `tests/test_transfer_caterpillar.py` (+ vdb/majorization/weighted) |

Verify locally (no Lean build — CI only, per the SoC-watchdog constraint): `PYTHONPATH=src python -m pytest
tests/test_spider_broom.py tests/test_transfer_caterpillar.py -q`. `conjecture1_proved = False`.

---

## Round-2 update (2026-08-31) — unified ownership + upper-bound engine

Now sole owner of the WHOLE BG program (analytic + Lean structural + Φ¹¹). Branch `bg/unified-program`.
See `proof/docs/design/BG_UNIFIED_PROGRAM_20260831.md` and `docs/BG_23ADIC_RECONCILIATION_20260831.md`.

**Reconciliation (done, exact):** the Φ¹¹ near-star `R(s)` **is** the classical-BG broom ratio
`total(5)^(2s+1)/total(s)^11`; the two programs coincide on the extremal family. This gave the `c=5` optimum a
**closed all-c proof** (single-crossing), and it is ALREADY kernel-gated — the frozen `examples/evolve_nearstar`
champion `(486/529)(1+1/(4s²+11s+6))^11` equals `1/broom_ratio(s)` exactly (`test_evolve_nearstar_is_the_broom_c5_gate`).

**Gates (kernel-gated, CI):** `bg_broom_optimum` (c=5 cross-exponent), `bg_arm_balancing` (m=2 general),
`evolve_nearstar` (closed c=5), and **`bg_bulk_discharge`** (NEW — the free-field `τ=1` full-edge atoms for
c=4,5 as Handelman box-positivity, wired into the Audit lake-build). The RH zero-free witness certifies via the
same Handelman engine (`probe/bg-handelman-shared-engine`) — one box-positivity cone, `621/64 = 27·23`.

**Upper-bound engine (new):** `src/telperion/bg_bulk_discharge.py` — exact Bethe decomposition
(`prod Aarg/prod Barg == rho`, `Σφ_v == log π`) + the algebraic target `exp(11 φ_v) ≤ 621/64`.

**The tight-τ crux (open, narrowed):** `docs/probes/bg_tight_tau_probe.py` — a universal *degree-only* discharge
FAILS (`+0.0033`); a per-tree *field-adaptive* one HOLDS (`≤ F*`). So τ must be field-dependent; the equalizing
τ is clean on low-degree (leaf/armmid) edges but the hub-hub backbone is **flow-underdetermined**, and its
universal resolution is the arithmetic (`emit_padic`, `27·23`) / box-positivity piece — NOT more field-data.
That is the open frontier: a universal closed-form field-`τ` on the cavity-field box, or the transfer-operator
variational bound.

**Merges:** GitHub tree→hub (PRs #166–#176, merged). GitLab MR !75 (rung2 972-cell identity) merged; MR !76
(the `test_mcp_server.py` mcp<2.0 pin) auto-merge armed — clears the CI `test` gate for the whole branch.
`conjecture1_proved = False`.
