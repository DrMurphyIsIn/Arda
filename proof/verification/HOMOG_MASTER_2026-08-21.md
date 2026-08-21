# Achievable Homogeneous Master Bound — probe report (2026-08-21)

**Branch:** `probe/homog-master-bound` (worktree `Arda-wt-homog`).
**Probe:** `proof/verification/homog_master_probe.py` (exact, self-verifying `run_all()` — ALL EXACT ASSERTIONS PASSED).
**Lean:** `telperion/examples/g1_floors/lean/HomogMaster.lean` — 12 theorems, `lake build HomogMaster` GREEN, every theorem axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`).
**conjecture1_proved = False.**

## 0. Target (re-derived from source, cited)

From `proof/formalization/R3Cert/CappedJointConfig.lean`:
- `W = 64/621` (`GStepCore.lean:25`).
- `glemma(mu) = W^2 (5/3)^11 / (1+mu/3)^11` (`CappedJointConfig.lean:33`).
- `master_ub(mu) = W (3/(2+mu))^11` (`:36`).
- `Bcap(mu) = min(master_ub, min(glemma, 1))` (`:39`).
- `baseOf l = (3(|l|+1) + 3 Σl + 1)/(3(|l|+1))` (`:42-43`); on `k` copies of `mu` this is
  `base(k,mu) = (3(k+1) + 3k mu + 1)/(3(k+1))`.
- `GAMMA = W^2 (5/3)^11`, `T = W (5/3)^11`.

`GS(k,mu) = base(k,mu)^11 · Bcap(mu)^k`.

**CLAIM (achievable homogeneous master bound):** for all integers `k >= 1` and ACHIEVABLE `mu`
(`mu = 1`, or `0 < mu <= 1/2`), `GS(k,mu) <= T`, equality iff `(k,mu) = (1,1)` (the arm).

## 1. Corrections to the brief

Two figures in the brief were imprecise; both corrected LOUDLY:

1. **Region-C argmax is NOT interior.** The brief said "LOCATE the exact interior argmax
   (the 0.8722 point)". The max of `GS(k,mu)/T` over `[1/3,1/2] x {k>=1}` sits at the **boundary**
   `(k=1, mu=1/2)`. `GS(1,mu)/T` is strictly increasing on `[1/3,1/2]` (its derivative is positive
   at both endpoints and it is a smooth ratio with no interior critical point there), so the max is
   the right endpoint. Exact value:
   `GS(1,1/2)/T = 34271896307633/39293437036896 ≈ 0.8722040852637`.
   (`base(1,1/2)=17/12`, `Bcap(1/2)=glemma(1/2)=409600000000000/762538262497263`.)

2. **`base` d/dk identity sign.** Confirmed the brief's sign (`(1/3 - mu)`), but the exact identity is
   `base(1,mu) - base(k,mu) = (k-1)(1 - 3mu)/(6(k+1))` (my first-draft target formula was wrong and
   the probe caught it). Sign is that of `(1-3mu)`, i.e. `(1/3 - mu)`. Verified symbolically over real
   `k` (`base_dk_identity`, kernel-green).

Everything else in the brief verified exactly (see §3).

## 2. Decomposition status (L1–L5)

| piece | statement | status |
|---|---|---|
| L1 | `mu<=1/3`: `base(k,mu)<=base(1,mu)` (from d/dk identity), `Bcap<=1` ⇒ `GS(k)<=base(1,mu)^11`; CERT-A `T-(7/6+mu/2)^11>=0` on `[0,74/240]` | **proved-symbolic + cert-found (Bernstein deg 12) + Lean** |
| L2 | `[74/240,1/3]`: `glemma<1` and base decreasing in k ⇒ `GS(k)<=GS(1)`; CERT-B `T(1+mu/3)^11-(7/6+mu/2)^11 GAMMA>=0` on `[74/240,1/3]` | **proved-symbolic + cert-found (Bernstein deg 11) + Lean** |
| L3 | `[1/3,1/2]`: CERT-C1 (k=1), CERT-C2 (k=2, `base(2,mu)=(10+6mu)/9`), CERT-C3 (k>=3 via exact `base(k,mu)<=1+mu` and `glemma<1`) | **proved-symbolic + 3 certs (Bernstein deg 12/22/34) + Lean** |
| L4 | `mu=1` arm line: `GS(1,1)=T` exact; `GS(k,1)` antitone (`base ratio<=16/15`, `(16/15)^11 W<=1`) ⇒ `GS(k,1)<=T` all k | **proved-symbolic + ASSEMBLED Lean induction (`armGS_le`)** |
| L5 | equality only at `(1,1)`: every region cert strict (positive endpoint margins), arm ratio `<1` strict | **proved-symbolic (margins exact)** |

### Exact certificate data

- **CERT-A** `T - (7/6 + mu/2)^11 >= 0` on `[0, 74/240]`: Bernstein degree 12, all coeffs `>= 0`.
  Endpoint margin at `mu=74/240` `> 0` (relaxation `Bcap<=1` crosses the irrational knee
  `mu_c = 5 W^(2/11)-3 ≈ 0.30774 ∈ (73/240,74/240)` at the rational split 74/240).
- **CERT-B** `T(1+mu/3)^11 - (7/6+mu/2)^11 GAMMA >= 0` on `[74/240, 1/3]`: Bernstein degree 11.
- **CERT-C1** same integrand on `[1/3, 1/2]`: Bernstein degree 12 (min value ~21.2 at mu=1/3).
- **CERT-C2** `T(1+mu/3)^22 - ((10+6mu)/9)^11 GAMMA^2 >= 0` on `[1/3,1/2]`: Bernstein degree 22.
- **CERT-C3** `T(1+mu/3)^33 - (1+mu)^11 GAMMA^3 >= 0` on `[1/3,1/2]`: Bernstein degree 34
  (values 325..2428, large margin). Exact `1+mu - base(k,mu) = (3mu-1)/(3(k+1)) >= 0` on `mu>=1/3`
  gives `base(k,mu) <= 1+mu` for all k; `glemma<1` on `[1/3,1/2]` extends k=3 to all k>=3.

### Integer / algebra companion lemmas (all `norm_num`, kernel-green)

- `leafI_cert`: `64^2·5^11·9^11 < 621^2·3^11·10^11` (⟺ `glemma(1/3)=486/529<1` ⟺ `GAMMA<(10/9)^11`).
- `master_inactive_cert`: `64·25^11 <= 621·21^11` (master_ub inactive on `(0,1/2]`; reused from DirectPolya probe).
- `armline_ratio_cert`: `64·16^11 < 621·15^11` (⟺ `(16/15)^11 W < 1`, the L4 per-step decrease).
- `base_dk_identity` (symbolic over ℝ): `base(1,mu)-base(k,mu) = (k-1)(1-3mu)/(6(k+1))`.

## 3. Region worst cases (grid, re-verified exact)

| region | worst `GS/T` | at |
|---|---|---|
| A (`mu<=73/240`, k<=44) | 0.7385 | k=1, mu=73/240 |
| B (`[74/240,1/3]`) | 0.7657 | k=1, mu=1/3 |
| mu=1/3 (all k<=200) | 0.7657 | k=1 |
| C (`[1/3,1/2]`) | **0.8722** | **k=1, mu=1/2 (boundary)** |
| arm line mu=1 (all k) | 1.0000 | **k=1 exactly (unique equality)** |

## 4. C-argmax (exact)

`GS(1, 1/2)/T = 34271896307633 / 39293437036896 ≈ 0.87220408526`, at the **boundary** `(k=1, mu=1/2)`.
Not interior. `GS(1,mu)/T` increases monotonically across `[1/3,1/2]`.

## 5. MasterCore correspondence verdict: **NOT the same object.**

`R3Cert/MasterCore.lean` proves `f(p) = ((4p+3)/(p+1))^11 · W^p <= 3^11`. My arm line is
`armGS(k) = ((6k+4)/(3(k+1)))^11 · W^k <= T`. The bases differ (`(4p+3)/(p+1) = 3.5` at p=1 vs
`(6k+4)/(3(k+1)) = 5/3` at k=1) and the bounds differ (`3^11` vs `T`). MasterCore is the CRUDE
per-type relaxation `∏Bcap <= W^p` (0.56 margin makes crude suffice); the arm line is the EXACT
homogeneous value with `Bcap(1)=W`. They are structurally analogous — both `(affine/affine)^11·W^k`,
both proven antitone by clearing denominators to a single integer cert — but they are DIFFERENT
sequences. L4 is therefore proven directly (`armGS_le`), not cited from MasterCore.

## 6. Lean deliverable

`telperion/examples/g1_floors/lean/HomogMaster.lean` (lean_lib target added to lakefile),
`lake build HomogMaster` GREEN, 12 theorems all axioms `[propext, Classical.choice, Quot.sound]`:

- `certA_small_mu, certB_mid, certC1_k1, certC2_k2, certC3_kge3` — the 5 Bernstein interval certs (over ℝ).
- `leafI_cert, master_inactive_cert, armline_ratio_cert` — integer certs.
- `base_dk_identity` — the d/dk algebra identity.
- `armGS, Tval, armGS_one, armGS_step, armGS_le` — the **assembled L4 arm-line theorem** over ℚ with
  a genuine `k : ℕ` induction (`armGS_le : ∀ k, 1 ≤ k → armGS k ≤ Tval`).

**Assembled full theorem (all regions, single statement): NOT compiled.** The stretch goal — one
Lean theorem quantifying `k : ℕ` and `mu ∈ {1} ∪ (0,1/2]` with the region split and the `min`-based
`Bcap` — was not assembled. What IS assembled is the k-quantified arm line (`armGS_le`, the hardest
k-induction) plus every region as a kernel-green Bernstein cert; wiring the region split + the
Bcap-min case analysis + the L1/L2 k-domination into a single `∀ k mu` theorem is a mechanical but
large glue task left open (it needs the cavity `Bcap` defs lifted to a shared ℚ config and the
piecewise mu-interval dispatch — several more sessions of Lean plumbing, no new mathematics).

## 7. INTERFACE STATEMENT (honest scope)

This probe closes the **HOMOGENEOUS face** of the unified Brualdi-Goldwasser crux over **ACHIEVABLE
`mu` only** (`mu = 1`, or `0 < mu <= 1/2`): for every homogeneous config (all `k` children at one
achievable `mu`), `GS(k,mu) <= T` with equality exactly at the arm `(k,mu)=(1,1)`. The
integer-tight wall at continuous `mu ∈ (1/2,1)` (the brief's `GS/T = 1.0351` at `mu=3/4` etc.) is
respected — achievability is load-bearing and no continuous-`(1/2,1)` certificate is attempted.

**STILL OPEN — THE crux going forward:**
1. The **heterogeneous → homogeneous reduction** (below-average chain / non-homogeneous fixed
   points) — NOT addressed here, remains the open item that turns this homogeneous face into the
   full master inequality.
2. The **assembled single Lean theorem** over `∀ k, ∀ achievable mu` (mechanical glue, §6).

`conjecture1_proved = False`.
