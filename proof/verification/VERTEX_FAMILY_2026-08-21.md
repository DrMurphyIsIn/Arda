# Heterogeneous achievable master bound — vertex lemma + canonical family (2026-08-21)

**Branch:** `probe/vertex-family` (worktree `Arda-wt-vertex`).
**Probe:** `proof/verification/vertex_family_probe.py` (exact, self-verifying `run_all()` — ALL EXACT ASSERTIONS PASSED).
**Lean:** `telperion/examples/g1_floors/lean/HeteroFamily.lean` — `lake build HeteroFamily` GREEN (39s), every theorem axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`).
**conjecture1_proved = False.**

This executes the bang-bang / vertex-lemma route of the scoping doc
`proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md`, replacing the broken
heterogeneous→homogeneous reduction. It scopes and (per-piece) certifies the
HETEROGENEOUS ACHIEVABLE face, turning the homogeneous face
(`HOMOG_MASTER_2026-08-21.md`) into the full achievable master bound modulo an
explicit leaf-splice obligation.

## 0. Target (re-derived from source, cited)

From `proof/formalization/R3Cert/CappedJointConfig.lean`:
`W = 64/621`, `GAMMA = W^2 (5/3)^11`, `T = W (5/3)^11`,
`glemma(mu) = GAMMA/(1+mu/3)^11`, `master_ub(mu) = W(3/(2+mu))^11`,
`Bcap(mu) = min(master_ub, glemma, 1)` (`= min(1, glemma)` on `(0,1/2]`),
`baseOf(l) = (3d+3S+1)/(3d)`, `d = |l|+1`, `S = Σ l`, and
`GS(l) = baseOf(l)^11 · Π_i Bcap(mu_i)`.

**CLAIM (heterogeneous achievable master bound):** for every achievable config
`l` (a multiset of children, each `mu_i ∈ {1} ∪ (0,1/2]`), `GS(l) ≤ T`, with
equality iff `l = [1]` (the arm).

## 1. Scan verdict

Canonical family (scoping §"CANONICAL FAMILY"):

    GS_fam(a, b, nu) = base_of(a+b+1, a·SPLIT + b/2 + nu)^11 · glemma(1/2)^b · glemma(nu)

with `SPLIT = 74/240 = 37/120` (rational relaxation of the knee `mu_c`), `nu ∈
[SPLIT, 1/2]` the single interior child, `b` children at `1/2`, `a` below-knee
children at the relaxed cap.

- **Family max** (exact scan `a,b ≤ 12`, `nu` grid `1/960`, plus the no-interior
  boundary sub-family): `GS/T = 0.8722040853` at `(a=0, b=0, nu=1/2)`.
- **This is exactly the homogeneous C-argmax** `GS(1, 1/2)/T =
  34271896307633/39293437036896 ≈ 0.87220408526` (the `k=1, mu=1/2` single-child
  config). Confirmed exact: `GS_fam(0,0,1/2) = GS([1/2])`. So the heterogeneous
  relaxed family adds **no new max above the homogeneous sector value** — every
  heterogeneous configuration is dominated by that single homogeneous point,
  well below `T`.
- **Argmax:** `a = 0` always (see §3 a-tail). Below-knee children never help; the
  family maximum is pinned at `a = 0` and `nu = 1/2`, which is the kink/boundary,
  consistent with the scoping doc's "kink-pinning, not exchange monotonicity" for
  the maximizer.

**Empirical vertex check:** 120,000 random heterogeneous achievable configs
(mixed sizes `j ≤ 8`, `~20%` leaf children `mu=1`, rest uniform in `(0,1/2]`).
Each was `≤` the max over its canonical projection (leaves kept, `(0,1/2]`
children spread to a vertex). **Worst excess of a config over its projection:
`3.375e-14`** (float round-off; the projection dominates). **Zero configs exceed
`T`.** No violation — the vertex claim holds empirically.

## 2. Vertex lemma status

**The exact exchange inequality is PROVED (kernel-green over ℝ).** The one new
piece of mathematics: for `fixed (j, S)`, the max of `Π min(1, glemma(mu_i))` over
`{0 < mu_i ≤ 1/2, Σ = S}` is attained with at most one interior coordinate.

- **Convexity of the log-objective (exact):** `f(mu) = log glemma(mu) = log GAMMA
  − 11 log(1+mu/3)` has `f''(mu) = 11/(3+mu)^2 > 0` (verified symbolically,
  `fact_convexity`). So `log Π glemma` is a sum of strictly convex terms, and
  fixed-sum maximization is at an extreme point (spreading increases the product).
- **Two-point spreading exchange (exact identity + witness):** for above-knee
  `mu_i ≤ mu_j` (both with `Bcap = glemma ≤ 1`) and `t ≥ 0` keeping feasibility,

      (1 + mu_i/3)(1 + mu_j/3) − (1 + (mu_i−t)/3)(1 + (mu_j+t)/3) = t·(mu_j − mu_i + t)/9 ≥ 0,

  hence `glemma(mu_i−t)·glemma(mu_j+t) ≥ glemma(mu_i)·glemma(mu_j)` (bigger
  denominators ⇒ smaller RHS product). This is `HeteroFamily.exchange_identity`
  (a `ring` identity) + `HeteroFamily.exchange_nonneg` (the `nlinarith` corollary),
  both kernel-green. **This is the same convexity that killed the merging
  argument, now in its correct direction.**
- **Assembly argument (constructive projection, sound; numerically verified):**
  given a config, repeatedly apply the exchange to any two strictly-interior
  above-knee coordinates, pushing them apart until one hits a bound (`knee` or
  `1/2`). Each step does not decrease the objective (exact) and strictly reduces
  the interior-coordinate count, so it terminates at `≤ 1` interior coordinate.
  Below-knee coordinates (`Bcap = 1`) contribute factor `1` and only their
  aggregate mass matters (enters `base` only), so they collapse to one mass
  variable `s_low`. Verified as a constructive projection on 20,000 random
  above-knee multi-configs (`fact_extreme_point_reduction`): spreading never
  decreased the objective (worst drop `≥ −1e-9`) and always terminated with `≤ 1`
  interior coordinate.

**Honest caveat on the assembly.** The two-point exchange is exact and
kernel-green. The *iterate-to-a-vertex* assembly is a standard finite exchange
argument, verified numerically here but **not yet Lean-formalized** (it needs a
`List`-induction over interior coordinates with a decreasing measure). The
below/above-knee bookkeeping is respected: the exchange is stated on above-knee
coordinates only (where `Bcap = glemma`), and below-knee mass is aggregated — the
subtlety that produced the chain's fixed points is handled by never spreading
across the knee. **Lean shape:** `exchange_nonneg` is done; the assembly is a
`List.rec` with a "number of interior coordinates" termination metric plus a
`baseOf`-invariance-under-mass-preserving-below-knee-moves lemma — mechanical,
`armGS_step`-flavored, not new mathematics.

## 3. Certification: cert list + tail lemmas

### Family Bernstein cells (exact)

Per-`(a,b)` cell integrand (clearing the `glemma(nu)` denominator):

    P_{a,b}(nu) = T·(1+nu/3)^11 − base_of(a+b+1, a·SPLIT + b/2 + nu)^11 · glemma(1/2)^b · GAMMA

`P_{a,b} ≥ 0 on [SPLIT, 1/2] ⟺ GS_fam(a,b,nu) ≤ T`. Scanned all `(a,b) ≤ 6`
(49 cells): **49/49 nonnegative-Bernstein certs found**, every cell with **min
endpoint margin ≈ 19.79 > 0** (far positive), max Bernstein degree 11. Margins
comfortably exceed the homogeneous margins (the homogeneous C-cells needed degree
up to 34; these family cells are degree ≤ 11 because the `glemma(1/2)^b` factor
suppresses the competitor). `fam_cell_a0_b0` is provably the same integrand as the
already-proven `certC1_k1` (the `k=1, mu=1/2` homogeneous cell) — exact identity
checked.

> **Bug fixed:** the shared `find_bernstein` (inherited from
> `homog_master_probe.py`) applied `sympy.nsimplify` to the exact `solve` output,
> which re-parsed the huge rational coefficients and occasionally perturbed them so
> the exact reconstruction check failed, silently dropping *valid* certs (cell
> `(2,3)` was rejected despite min Bernstein coefficient `+65.8`). Using the exact
> `solve` rationals directly recovers all 49. Worth back-porting to the homogeneous
> probe.

### Tail lemmas (exact)

- **b-tail (geometric, clean):** `glemma(1/2) = 409600000000000/762538262497263 ≈
  0.5372 < 1` (exact; integer cert `64^2·5^11·2^11 < 621^2·7^11`,
  `HeteroFamily.glemma_half_lt_one`). The base is uniformly bounded: `base_of(j,S)
  ≤ base_of(j, j/2) = 1 + (3j/2+1)/(3(j+1)) ↑ 3/2` (sup-base `= 3/2`, exact limit).
  So `GS_fam ≤ (3/2)^11·glemma(1/2)^b·glemma(nu) ≤ (3/2)^11·glemma(1/2)^b → 0`, and
  `(3/2)^11·glemma(1/2)^b ≤ T` already at **`b = 2`** (uniform in `a, nu`). The
  `b`-tail is therefore a two-line geometric domination; only `b ∈ {0,1}` need the
  explicit cells (all present).
- **a-tail (NOT a clean monotone — corrected):** adding a below-knee child at the
  capped mass multiplies `GS_fam` by `(base_of(j+1,S+SPLIT)/base_of(j,S))^11` (the
  `Bcap = 1` factors cancel). The base difference numerator is `3·SPLIT·(j+1) − 3S
  − 1`, which is **NOT sign-definite** (positive for small `S`, negative for large
  `S`). So "a-tail via base monotonicity" is not a single-direction lemma. The
  load-bearing fact is instead **kink-pinning: the family max over `a` is ALWAYS at
  `a = 0`** — verified exactly over the full `(b, nu)` grid (`argmax-a = 0`
  everywhere, `fact_a_tail`). Below-knee children never increase the maximum.
- **s_low monotone (exact):** `d base_of/dS = 1/(d) > 0`, and `SPLIT = 74/240 >
  mu_c`, so pushing below-knee mass up to the relaxed cap `a·SPLIT`
  over-approximates `GS` (`fact_s_low_monotone`). The relaxation is sound (an
  upper bound on the true achievable configs).

## 4. Leaf-splice status — an EXPLICIT OBLIGATION, not kernel-checked

The scoping doc says leaves (`mu = 1` children) are "monotone-safe by the existing
argument." **This is only partially true, and I flag it loudly:**

- The homogeneous face proves the **all-leaf line** (`armGS_le`: `k` copies of
  `mu = 1` give `GS ≤ T`, equality iff `k = 1`). ✅ kernel-checked.
- A **MIXED** config (some leaves `mu = 1`, some children in `(0,1/2]`) is **NOT**
  covered by `armGS_le`. The scoping doc's "already monotone-safe" claim is an
  informal appeal to the arm line; **the mixed case is a genuine open obligation.**

What IS established here:
- `Bcap(1) = W` exactly (`master_ub(1) = W`, `glemma(1) ≥ W`; integer cert
  `HeteroFamily.glemma_one_ge_W: 621·4^11 ≤ 64·5^11`). ✅ kernel-green.
- Per-leaf ratio `GS(l + [1])/GS(l) = W·(base_of(j+1,S+1)/base_of(j,S))^11` (exact
  symbolic).
- **Empirical:** adding leaves to any canonical `(a,b,nu)` config never pushes
  `GS/T` above the no-leaf family max — worst mixed value `0.8668 < 0.8722` (at
  `nleaf = 0`), and exhaustive half-child + leaf mixes peak at exactly the arm
  `GS([1])/T = 1` (`nhalf=0, nleaf=1`), never above.

**Obligation (stated for the record):** prove `GS(l + [1]^m) ≤ T` for any
canonical `l`, i.e. the mixed leaf splice. Empirically safe; the proof shape is a
per-leaf ratio bound `W·(base ratio)^11 ≤ 1` combined with the family bound on `l`
— an `armGS_step`-style integer cert per leaf, but interacting with `base_of`'s
`j`-dependence, so it is a real (if modest) lemma, not a citation.

## 5. Lean kernel-green pieces

`telperion/examples/g1_floors/lean/HeteroFamily.lean` (`lean_lib HeteroFamily`
added to the `g1_floors` lakefile), `lake build HeteroFamily` GREEN, all axioms
`[propext, Classical.choice, Quot.sound]`:

- `exchange_identity` — the two-point exchange `ring` identity (over ℝ).
- `exchange_nonneg` — the exchange inequality `(1+(mi−t)/3)(1+(mj+t)/3) ≤
  (1+mi/3)(1+mj/3)` for `t ≥ 0`, `mi ≤ mj` (the vertex-lemma engine).
- `glemma_half_lt_one` — `64^2·5^11·2^11 < 621^2·7^11` (b-tail geometric ratio `< 1`).
- `glemma_one_ge_W` — `621·4^11 ≤ 64·5^11` (`Bcap(1) = W` anchor).
- `fam_cell_a0_b0 … fam_cell_a1_b1` — 6 family Bernstein positivity certs on
  `nu ∈ [37/120, 1/2]` (the small `(a,b)`; `fam_cell_a0_b0` = the `certC1_k1`
  integrand).

**NOT assembled (honest):** the full `∀ l achievable, GS(l) ≤ T` theorem is not
compiled. What is missing to assemble it, in order of remaining work:
1. the vertex-lemma *assembly* (`List`-induction with the interior-coordinate
   metric; the exchange step is done);
2. the family reduction wiring (`baseOf`-relaxation to `GS_fam`, `s_low` up to cap,
   b-tail geometric domination beyond `b ≤ 1`, a=0 pinning) — mechanical, mirrors
   `HomogMasterAssembled.lean`'s region dispatch;
3. the **leaf splice** (§4, a genuine lemma);
4. the remaining family cells `(a,b) ≤ 6` as Lean certs (I emitted 6 of 49; the
   emitter and certs exist, emitting the rest is mechanical but the file grows).

Per the brief, the full assembled hetero theorem is STRETCH and not forced —
per-piece green + this honest gap list is the deliverable.

## 6. Interface: what remains for the full master inequality

After this lands, the full Brualdi-Goldwasser master inequality
(`baseOf(l)^11·prodBcap(l) ≤ T` for every achievable `l`, equality iff arm) needs:

1. **Vertex-lemma assembly in Lean** (the exchange is proved; iterate-to-vertex is
   the remaining formalization — a finite exchange induction, no new math).
2. **Leaf splice** (§4) — the one genuine open obligation the scoping doc
   under-stated; empirically safe, needs a per-leaf ratio lemma.
3. **Family certification assembly** — glue the 49 cells + two tail lemmas + a=0
   pinning + s_low relaxation into `∀ (a,b,nu), GS_fam ≤ T`, then compose with the
   vertex lemma to get `∀ l, GS(l) ≤ GS_fam(canonical(l)) ≤ T`. Mechanical, mirrors
   the homogeneous assembly.
4. **Strictness / equality characterization** (`GS(l) = T ↔ l = [1]`) — needs
   strict Bernstein endpoint margins (the `≤` certs exist with margins ≈ 19.8 > 0;
   strict certs are a small addition), same stretch item as the homogeneous face.

**Not in scope (respected):** the continuous `mu ∈ (1/2,1)` integrality wall —
achievability (`mu ∈ {1} ∪ (0,1/2]`) is load-bearing throughout; no
continuous-`(1/2,1)` certificate is attempted, and the family relaxation stays
within the achievable box.

`conjecture1_proved = False`.
