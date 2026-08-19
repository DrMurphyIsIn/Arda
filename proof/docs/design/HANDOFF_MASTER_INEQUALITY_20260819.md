# Hand-off: the master-inequality arc (2026-08-19)

For the next session (or the parallel one) picking up the Brualdi–Goldwasser closure.
Everything below is on `origin/main` (tip `a8f00ef` at write time). `conjecture1_proved
= False` everywhere, correctly. This arc did **not** move the crux — it *localized* it
as tightly as honest work reaches, and caught five would-be closures before any shipped.

## Read in this order

1. `MASTER_INEQUALITY.md` — the frontier. §1–5 state the open core and the kernel-checked
   bricks around it; §6a–6e are this arc's sharpening (finite-domain validation, the
   located obstruction, the sharpest attackable face, the homogeneous-face localization +
   first proven slice). This is the map.
2. This file — the arc's honest tally and the next attackable targets.

## Where the proof stands

**Open core (unchanged):** the *tight* master inequality `F(C) ≤ env★(μ_C)` — the
quantified slack, not the weak `F(C) ≤ 1` (which is `phi_le_one`, proven). Equality only
at the tie (`μ=3/23`, F=1).

**Kernel-checked / already-green bricks:** `phi_le_one` (PotentialFinal), tie-dominant
half `tie_dominant_half(_lt_one)` (TieClosure), near-star family `nearStar_family_le_zero`
(NearStar), arms+ties `aHubAT_add_tie_le` (R47LegsAT), ℓ≥3 legs `legs_rate_ge3`
(R47LegsRate), single-child rate `pi_le_rate` (R47RateZBound). The arm's homogeneous
bound is green via `R(s)`.

**This arc's cleanest new result (proven, elementary):** the homogeneous face
`max_j H_C(j) ≤ 1`, `H_C(j) = W(1+jμ/(j+1))^11 F^j`, holds **unconditionally from
`phi_le_one` alone** for `μ_C ≤ μ0 = (621/64)^{1/11} − 1 ≈ 0.2295` (rational under-approx
`229/1000`): `H_C(j) ≤ W(1+μ)^11 ≤ 1` since `jμ/(j+1) < μ` and `F^j ≤ 1`. Disposes of the
entire small-μ tail incl. the §6c `m=1/15` envelope-killer. **Caveat:** it is the *easy*
piece — the tight point (arm, μ=1/3) sits above μ0, so the summit stays open.

## The homogeneous-face reformulation (the sharpest attackable framing)

The near-star half ⟸ `{reduction: F_hub ≤ max_child H(μ_i,F_i)}` + `{homogeneous bound:
H ≤ 1}`. The homogeneous bound is **not a surrogate** — the C-broom (j copies of a real
block C) is a real tree with factor `W(1+jμ/(j+1))^11 F^j` exactly, so it is symmetric-hub
BG. It is 1-parameter, unimodal-in-j (crossing-once, the `R(s)` shape), tight only at the
arm. Its tight set is *exactly* the Lean-green families (arm + leaf + near-stars); **every
non-near-star block has H ≤ 0.3637** (a 0.63 margin, n≤11).

## Why it's genuinely hard (the located obstruction)

The achievable `(μ,F)` set is a **jagged discrete scatter** (3373/7508 upward kinks, no
closed form), not a curve. So no proven convex surrogate certifies `H ≤ 1` off the arm:
g-lemma (`F ≤ γ/(1+μ/3)^11`, γ=2.93) and its cap both permit unachievable `(μ,F)` (e.g.
`(0.307, F=1)` → `W(1+μ)^11 = 1.97`) that no real block realizes. The uniform `(μ,F)`
certificate that would close it **is** the master inequality. The elementary ceiling is
`μ ≤ μ0`; past it you must use `F<1` quantitatively = the envelope = the crux.

## Five would-be closures caught this arc (none shipped)

1. `∏env ≤ 1` — unsound (continuous `F_ns > 1` at k≈4.82); tie-dominant half survived
   because it never used env (pure algebra).
2. reduce-to-homogeneous via below-average lemma — the below-average chain has
   **non-homogeneous fixed points** (μ=(1/5,2/5) fixed, not equal); reduction is
   empirically true but its proof is broken.
3. reduce-to-dominating-family — `general_induction.py`'s already-pinned dead route
   (near-stars don't dominate at m=1/15; bare leaf beats cherry-arm).
4. `j*≥2 ⟺ near-star` dichotomy — false (block μ=0.1594,F=0.7657,n=12,j*=2 non-near-star).
5. a tuple-evaluation-order bug (`return W**n*prod**11, rec(...)` computes F before the
   recursion mutates prod) — produced a false "only-leaf" picture; caught on a 6-line
   minimal recheck before it reached the doc.

## REDIRECT (parallel session, branch `feat/homogeneous-face-handoff` @ 695b42c)

**Do not attack the homogeneous face directly — attack its upstream, the g-lemma.**
The parallel crux session found the homogeneous face is a *downstream shadow* of the
g-lemma `g(C) = F·(1+μ/3)^11 ≤ γ`, `γ = W²(5/3)^11 = 2.9276`:

- The arm is the **unique saturator**: `g(arm) = γ` exactly (independently confirmed
  here, exact `Fraction`).
- **Non-near-star blocks obey a strictly stronger bound**: `max g = 1.8524`, a `1.075`
  gap below γ (confirmed here to n=12; parallel session: enumeration to n=14, adversarial
  to n=28, no creep toward γ — the first lead to survive past the n=22–56 range where
  every prior gap broke).
- Under that gap the homogeneous bound closes with margin (`H ≤ 0.588 < 1`).

So the g-lemma **plus its equality characterization** (`g(C) ≤ γ`, equality iff arm) is
the real object; the homogeneous face and the near-star half both fall automatically,
with margin, once it closes. Per the parallel session, R1 single-hub extremality reduces
to the same object (not independently re-verified here). **Next session: attack
`g(C) ≤ γ` with equality iff arm — the g-lemma / master-inequality branching residual.**

## Superseded targets (kept for context)

1. **Proven slice** (`μ ≤ μ0 ⟹ H ≤ 1`) — DONE, kernel-checked: `HomogeneousSlice.lean`
   (`H_le_one`, `H_le_one_of_muLe`) on main. First proven piece of the homogeneous face;
   now understood as a downstream slice, still valid.
2. The leaf + near-star k=1,2 cases, and the generic non-near-star band — all subsumed by
   the redirect: they are the downstream shadow, not the target. Attack the g-lemma.

## Verification

Python probes are ad-hoc (this arc, not committed as modules) — use `.venv` py3.14
(`~/arda-trading/.venv/bin/python3`); system py3.9 can't import arda. All numeric claims
in `MASTER_INEQUALITY.md` are exact `Fraction`, no floats at decision points. Lean verified
via GitHub Actions only (no local `lake build` — SoC-watchdog hardware fault).
