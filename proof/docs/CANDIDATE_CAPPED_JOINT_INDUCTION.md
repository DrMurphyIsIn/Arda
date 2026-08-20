# CANDIDATE: capped joint {master ∧ g-lemma} induction (Gap 1 lead, 2026-08-19)

**Status: STRONG EMPIRICAL CANDIDATE — NOT a proof. `conjecture1_proved = False`.**
This is a lead on Gap 1 (the R3 crux / master inequality), surfaced for coordination
with the parallel session that owns the master-inequality / AM-GM wiring line. It may
be the ingredient that "blocked AM-GM wiring" (`R1_WIRING_SCOPING`) was missing — or it
may hide an obstruction in its step inequalities. It needs an all-`n` proof or a
refutation, not acceptance.

## The scheme

Prove, by strong induction on block size, that **every** block `B` satisfies BOTH:
- **(master)** `(2+μ_B)^11 F_B ≤ MASTER_C = (64/621)·3^11`   (equality iff leaf)
- **(g-lemma)** `g(B) = F_B·(1+μ_B/3)^11 ≤ γ = (64/621)²(5/3)^11`   (equality iff arm)

using the per-child bound that combines both IH targets **capped by `phi_le_one`**:

  `F_c ≤ Bcap(μ_c) := min( master_ub(μ_c), glemma_ub(μ_c), 1 )`,
  `master_ub(μ)=(64/621)(3/(2+μ))^11`,  `glemma_ub(μ)=γ/(1+μ/3)^11`.

`F_c ≤ 1` is `phi_le_one` (proven unconditionally), so `Bcap` is a valid, cheaper
child bound. `μ_B = 1/(j+1+S)`, `a_B = 1+S/(j+1)`, `S = Σ_c μ_c`, `j` = #children.

## What it evades, and how

`envelope.py` ruled out the **tight single envelope** `h*` (`F_v ≤ h*(μ_v)`, `h* ≤ 1`
everywhere): the pure step `W a_v^11 ∏h*(μ_c) ≤ h*(μ_v)` overshoots ~100×, because the
per-child maxima are not jointly realizable (sibling correlation). This scheme is a
**different object**:
- **Two targets, not one** — `master_ub` and `glemma_ub` (their min is the parent
  envelope), looser than `h*` at small-μ parents (`h_target(0)=γ=2.93 ≫ h*<1`).
- **Children capped at 1** — the `phi_le_one` cap stops the small-μ product blow-up
  that killed the pure envelope. The campaign's g-lemma already uses `min(1, glemma)`;
  this **adds `master_ub`** to the cap (which binds for near-leaf children,
  `master_ub(1)=64/621 < glemma_ub(1)`) and inducts on **both** invariants at once.

The asymmetry — tight bound where it matters (small-μ children inside a product), loose
target where it is easy (small-μ parent) — is what makes it inductive where `h*` is not.

## Evidence (exhaustive + adversarial; all exact `Fraction`)

| test | result |
|---|---|
| full enumeration n ≤ 15 | **0 failures** in 275,605 induction steps; master worst 0.5617, g-lemma worst **1.0000** |
| adversarial deep-subtree (j≤9, path-depth L≤39) | 0 failures |
| heterogeneous extremizer mixes (12,869: tie, arm, leaf, …) | 0 failures |
| worst-case locus | g-slack `= 1` **only** at the arm/tie extremizers (the known equality cases) |

Tight exactly at the extremizers, margin everywhere else — the signature of a genuine
inductive envelope. This survives the adversarial pressure that refuted five prior
would-be closures this arc.

## What remains (the proof obligation — where it could still fail)

Reduce to and prove, for **all** realizable `(j, {μ_c})` with `μ_c ∈ (0,1/2] ∪ {1}`:
1. **master step**  `(2+μ_B)^11 · W · a_B^11 · ∏_c Bcap(μ_c) ≤ MASTER_C`
2. **g-lemma step**  `(1+μ_B/3)^11 · W · a_B^11 · ∏_c Bcap(μ_c) ≤ γ`

These are per-child-product inequalities in the messages alone (the cap is what makes
the product tractable). If they close analytically for all `n`, Gap 1 / R3 closes. If
they hide the same joint obstruction in the `Bcap` product, this is a strong census
lead but not a proof. **Do not mark R3 proven until (1)+(2) are theorems.**

## Validation progress (2026-08-19, same session) — a concrete proof path

Attacking the two step inequalities directly (all exact `Fraction`):

1. **The joint `a_B` coupling is reducible.** `a_B = 1 + S/(j+1) ≤ ∏_c (1+μ_c/(j+1))`
   (since `∏(1+x_i) ≥ 1+Σx_i`), and this factorized bound is **tight enough** — both
   steps still close with it (11,439 realizable multisets, worst exactly 1.0 at the arm).
   So the proof need not keep the joint `a_B`; it becomes a per-child product.
2. **Not Schur-maximized at equal children** (1014/16000 unequal cases exceed equal),
   so a naive "reduce to homogeneous" fails — BUT the excesses are tiny (≤0.0055) and
   deep in the interior where values are ≪1, so they do not threaten the margin.
3. **The inequality splits cleanly by `j`, tight in exactly one case** (census n≤13 +
   dense menu; g-step shown, master-step has even more margin, worst 0.562):

   | case | g-step sup | role |
   |---|---|---|
   | `j ≥ 2` | **≤ 0.693**, decreasing in `j` (max at equal mid-μ children) | loose interior |
   | `j = 1`, `μ_c ∈ (0,½]` | **≤ 0.872** (margin 0.128) | 1-variable inequality |
   | `j = 1`, `μ_c = 1` (leaf child = the arm) | **= 1 exactly** | the sole equality case |

**Consequence.** Proving the step reduces to: (a) a **single-variable** rational
inequality `g_1(μ) ≤ 1` on `μ ∈ (0,½]` (Telperion-shaped), (b) the **exact** arm
boundary (`j=1`, `μ_c=1`, `=1`), and (c) a **loose uniform bound** `g-step ≤ 0.7 < 1`
for `j ≥ 2` (margin ≈ 0.3; the factorization + cap should give it since more children
⇒ smaller `μ_B` ⇒ smaller prefix). No tight interior analysis, no exact worst-case.

**Still not a proof.** (a)/(c) are tractable but unproven; the `j≥2` all-`n` uniform
bound needs its argument written. But the crux is no longer "collective and joint" —
it is a 1-D boundary inequality plus a loose interior. `conjecture1_proved = False`.

## PROVEN: the j=1 g-step (the tight/binding case) — 2026-08-19

The `j=1` g-lemma step (a single child, message `μ`) is now **proved analytically**,
every step exact-verified. For one child, `μ_B=1/(2+μ)`, `a_B=(2+μ)/2`, and

  `(1+μ_B/3)·a_B = (7+3μ)/6`  ⟹  `g_1(μ) = ((7+3μ)/10)^11 · Bcap(μ)/W`.

- **On `μ ∈ (0,½]`** (non-leaf children): `Bcap ≤ glemma_ub`, and
  `glemma_ub(μ)/W = W·(5/(3+μ))^11`, so
  `g_1(μ) ≤ W·((7+3μ)/(2(3+μ)))^11`.
  Since `14(7+3μ) ≤ 34(3+μ) ⟺ 8μ ≤ 4 ⟺ μ ≤ ½`, we get `(7+3μ)/(2(3+μ)) ≤ 17/14`, hence
  `g_1(μ) ≤ W·(17/14)^11`, and this is `≤ 1` iff the **integer inequality**
  **`64·17^11 ≤ 621·14^11`** (`2193401363688512 ≤ 2514779970361344` — `norm_num`).
- **At `μ = 1`** (leaf child = the arm): `Bcap(1) = master_ub(1) = W`, so
  `g_1(1) = ((10)/10)^11 · W/W = 1` — the exact equality. (The glemma bound is loose here,
  `1.20`; the arm needs `master_ub`, handled by the isolated `μ=1` case — messages live in
  `(0,½] ∪ {1}`, no gap.)

This is the **binding** case (arm/tie tightness lives at `j=1`), and it holds
**continuously** on `(0,½]` — no integer-tightness — corroborating the parallel
session's integrality probe: the dual-target + `phi_le_one` cap genuinely evades the
`k≈4.82` obstruction, which is why an analytic proof exists here where every prior route
was blocked. Lean-formalizable (elementary + one `norm_num`). `conjecture1_proved = False`.

**Remaining for the full g-step:** the `j ≥ 2` case. **Validated but not yet proven.**

Characterized exactly (all `Fraction`): the g-step identity is
`L2 = W·[(3d+3S+1)/(3d)]^11·∏Bcap` (`d=j+1`, `Bcap=W` for leaves, `min(1,glemma_ub(ν))`
for non-leaves). The worst case is at **`p=0` (no leaves — leaves only help)**, dominated
by **`q=2` two non-leaves near `μ≈0.31`**, sup **0.72163** (margin **0.278**), decreasing
in `q`. BUT it **resists clean reduction**: not monotone in leaves (205/30k increase), not
monotone in non-leaves (5151/30k), not Schur-max at equal children (380/2500) — and the
crude `∏Bcap≤1`/`≤W^p` bound that closed the loose master step is *too weak* here (the
g-step needs the per-child glemma suppression counted). So `j≥2` is a genuine
loose-but-multivariate inequality (margin 0.28, holds in all n≤15 + adversarial tests).

**Reduction of j≥2 (2026-08-19, further).** The `p=0` case (the dominant one, leaves only
help) splits at the cap boundary `ν* ≈ 0.307` (`Bcap(ν)=1 ⟺ (1+ν/3)^11 ≤ γ`):
- **CASE 1 — all children small (`Bcap=1`):** closes by the **base bound alone**,
  `[(3d+3S+1)/(3d)]^11 ≤ W(5/3)^11` (worst at all `ν=ν*`, ratio 0.720 < 1); `∏Bcap=1`, no
  suppression needed. Clean hand proof (modulo a rational `ν*` bound). **Essentially done.**
- **CASE 2 — at least one large child (`Bcap=glemma<1`):** the residual, **dominated by
  `q=2`** (two large children near `ν≈0.31`, sup 0.72163; `q=3`→0.705, `q=4`→0.693, both
  smaller). So the entire hard residual is a **2-variable, degree-11 rational inequality
  with margin ≈ 0.28** — a tractable SOS/Positivstellensatz target (or a careful 2-var hand
  bound), plus the `q≥3 ≤ q=2` domination.

**Final object.** The CASE-2 `q=2` sup sits at the cap boundary `ν*≈0.308` (meeting CASE 1
continuously), and on the equal-children diagonal has the closed form
`g₂(ν) = W³·10¹¹·(5+3ν)¹¹ / (3¹¹·(3+ν)²²)`. So the last inequality is the **single-variable
polynomial** `g₂(ν) ≤ 1 ⟺ W³·10¹¹·(5+3ν)¹¹ ≤ 3¹¹·(3+ν)²²` on `ν ∈ (ν*, ½]` (ratio 0.723 at
`ν*`, 0.580 at `½`) — Telperion-shaped (DirectPolya / interval bracket).

**q=2 is now PROVEN (all child messages), reusing the arm certificate.** For any two
children `a,b`, `Bcap ≤ glemma_ub` gives the exact
`L2([a,b]) = W³·(5/3)¹¹·[(10+3a+3b)/((3+a)(3+b))]¹¹`. The factor
`f(a,b)=(10+3a+3b)/((3+a)(3+b))` is decreasing in each variable (`∂f/∂a=(3+b)(−1−3b)/(…)²<0`),
so `f ≤ f(0,0) = 10/9`, hence `L2 ≤ W³·(50/27)¹¹`, which is `<1` by the **integer certificate
`64³·50¹¹ < 621³·27¹¹`** (`= 0.9615`) — *identical* to `arm_maximal`'s final rational
certificate. No cap needed (the single `γ` is absorbed by the constant); covers leaves too.

**So the full remaining gap of the entire crux is now:** (a) the **`q≥3` CASE-2** case (large
children with `q≥3` — the glemma bound's `γ^{q-1}` needs the cap here; CASE 1 all-small is
done, q=2 is done, and it is dominated by q=2 empirically, sup ≤ 0.705); and (b) Lean
formalization of the whole induction. Everything else — master (all j), g-step j=1, g-step
j≥2 q=2, g-step j≥2 CASE 1 — is proven. `conjecture1_proved = False`.

## Status of the whole scheme (2026-08-19)
- **master step (all j):** PROVEN — crude per-type bound, reduces to `[(4p+3)/(p+1)]^11 W^p ≤ 3^11`, `p=0` exact equality (parallel session).
- **g-step, j=1 (binding):** PROVEN — this doc (`64·17^11 ≤ 621·14^11`, arm `=1`).
- **g-step, j≥2 (loose):** VALIDATED, not proven — one multi-variable inequality, margin 0.28.

The capped joint induction is proven **except the single loose j≥2 g-step**. That is the
entire remaining distance to closing Gap 1 / R3.

## Coordination

Overlaps the parallel session's master-inequality / AM-GM line. If they have already
tried `min(master,glemma,1)` joint induction and found where it breaks, this is
subsumed — please point at the break. Otherwise (1)+(2) are the next target, and are
Telperion-shaped (per-message rational inequalities with a cap).
