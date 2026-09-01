# BG discharge-certification — Phase 0 gate verdict (2026-09-01)

Phase 0 of the recursion-constrained pointwise-certification plan (`sorted-conjuring-clock`) is the
**go/no-go gate**: does a *universal* edge-discharge `τ` making the local Bethe free energy
`φ_v = A_v − Σ_u τ_{v,u} B_{v,u} ≤ F* = log(621/64)/11` at every vertex plausibly exist, or is the
obstruction genuinely arithmetic (cheaters on the reachable variety → Fallback)?

`conjecture1_proved = False` throughout. This is empirical de-risking over a finite tree pool, not a proof.

## Tests run

Three probes, over spiders `S(k,c)` and mixed/high-degree caterpillars (`bg_bulk_discharge`'s exact
cavity recursion + Bethe terms; `EXEMPT` degree ≥ 15 gated as high-degree tail):

1. **Threading** (necessary condition) — per-degree affine `τ(1,h_ab,h_ba,A_a,A_b)` threads every edge's
   feasible τ-interval: **46/47 degree-pairs exact**, last at solver tolerance (`+6e-7`). A local rule can
   pick a valid τ *per edge in isolation*.

2. **Universal simple-affine `τ`** (`bg_phase0_universal_tau_lp.py`) — exact LP: `φ_v` is *linear* in a
   per-degree affine `τ` (`τ_{b,a}=1−τ_{a,b}` auto sum-to-1), so `min max_v φ_v` over the pool is an LP.
   Result: fits `F*` **exactly on train** but **overfits** — held-out (even with train covering the full
   degree range `c≤8` + mixed caterpillars, held-out *interior*) fails: `cat[6,8,4] +0.044`, `S(6,8) +0.011`,
   `cat[7,5,3] +0.008`. **Not** solver tolerance, **not** extrapolation.

3. **Per-tree feasibility** (`bg_phase0_pertree_feasibility.py`) — per-tree LP for the field-adaptive τ:
   **every** tree in the pool achieves `min max_v φ_v ≤ F*`, **worst gap `+5.6e-17` (machine zero)**.
   `F*` is **sharp**: hit exactly by `S(k,5)` *and* by `cat[8,4,6,5]`, `cat[5,9,3]`; strictly beaten by all
   others (all in `[0.2056, 0.20659]`).

## Verdict: GO — with a sharpened target

- **Feasibility is not the wall.** Every reachable tree has a discharge `τ` with `φ_v ≤ F*` exactly, and
  `F*` is the sharp universal bound (achieved on a *variety* of tie configs, not just the broom — consistent
  with the 23-adic zero-face picture). The plan's premise that the cheaters are excluded from the reachable
  set holds in the strong sense: **no reachable tree is infeasible.**
- **The obstruction is precisely a universal closed-form `τ`**, and it is **not** a simple local affine
  function of the two endpoints' immediate data (degrees + incident-field aggregates `A_v`). The mixed-degree
  caterpillar failures (`+0.02`–`+0.04`) show the required rule needs richer structure than two-endpoint
  affine.

This is exactly the object Phase 2 constructs: the **principled rational `τ`** from the Bethe convex-dual /
Perron eigenvector of the cavity Jacobian — derived, not fit. Phase 0 confirms it is worth deriving (the
target exists per-tree and `F*` is sharp) and rules out the cheap shortcut (simple affine).

## What this does *not* establish

- Per-tree feasibility over a finite pool is not feasibility over all trees (though combined with the
  certified broom optimum and the sharp-`F*` tie structure it is strong evidence).
- A universal closed form is not yet exhibited; Phase 2 must produce the rational rule and verify it
  reproduces `φ_v = F*` at the ties and `< F*` elsewhere out-of-sample.

## Phase 2 opening — is the discharge a LOCAL function? (empirical)

Two probes on whether a *universal local* `τ` (not per-tree) can reproduce feasibility:

- **Principled closed forms** (`bg_phase2_principled_tau.py`) — the Bethe-marginal split
  `τ_{v,u}=p_{v,u}/(p_{v,u}+p_{u,v})` with `p_{v,u}=(h_{u→v}/(d_ud_v))/exp(A_v)` (the fractional
  field contribution `∂A_v/∂log h_{u→v}`), degree split, and squared variants. **All fail** on the tie
  configs (`cat[5,9,3] +0.046`): at a tie tree the discharge must equal the exact dual optimum, which a
  simple split can't reproduce.

- **Flexible local learner** (`bg_phase2_tau_locality.py`) — canonical least-committal per-tree `τ`
  (`min Σ(τ−½)²` s.t. `φ_v≤F*`, a convex QP) as target; gradient-boosted regression on radius-1.5 local
  features (endpoint degrees, both cavity fields, `A_v,A_u`, and each endpoint's *other* incident-field
  max/sum/count). Applied out-of-sample (split by tree): **worst gap `+0.0059`**, and the *tie* configs
  now generalize (`cat[4,6,8] +0.0001`, `cat[5,9,3] +0.0019`); residual is on generic mid-degree
  (`cat[7]×8`, `S(k,4)` `≈+0.005`).

**Trend:** the out-of-sample gap shrinks monotonically with model capacity
(`+0.046 → +0.02..0.04 → +0.006`), and ties are captured — evidence a bounded-radius local `τ` **exists**
but its exact form is not reachable by fitting (you cannot hit exactly-`0` empirically). This is the
signal that motivates the plan's actual Phase 2/3: *derive* the rational `τ` from the Bethe convex-dual /
Perron eigenvector and *certify* `exp(11φ_v)≤621/64` per integer-degree case over the recursion-constrained
field set — the fit residual `≈0.005` is exactly the "last mile" a principled derivation + facial/23-adic
certificate must close, not more regression.

## Reproduce

```
PYTHONPATH=telperion/src python3 telperion/docs/probes/bg_phase0_universal_tau_lp.py
PYTHONPATH=telperion/src python3 telperion/docs/probes/bg_phase0_pertree_feasibility.py
PYTHONPATH=telperion/src python3 telperion/docs/probes/bg_phase2_principled_tau.py
PYTHONPATH=telperion/src python3 telperion/docs/probes/bg_phase2_tau_locality.py
```
