# Gap 2 audit: the Branch→per(L) bridge — what is formalized, what is open

2026-08-22. `conjecture1_proved = False`. A source audit of the realization-bridge Lean
(`R3Cert/Bridge*.lean`), done after confirming the g-step / R3 crux is already closed on `main`
(`gstep_le_one_achievable`; see `STEP1_INTERIOR_CHILD_REDUCTION_20260822.md`). This states the
bridge's current Lean state and pinpoints the single open piece. Audit, not a closure.

## Where the whole conjecture now sits

The R-ladder crux (R3, `Φ≤1` / the heterogeneous g-step over all achievable configs) is **closed** in
Lean — `CappedJointConfig.gstep_le_one_achievable`, unconditional, no `sorry`/`axiom`, verified
non-vacuous. What remains for Conjecture 1 is **Gap 2 (this bridge)** and **Gap 3 (R7 assembly)**. This
doc audits Gap 2.

## What the bridge must do

Transfer the proven Branch-model bound to the actual object: `Branch.logPhi ≤ 0` (equiv. `Φ^11 ≤ 1`,
proven) ⟹ `per(L(T)) / ∏ deg` satisfies the maximizer inequality. The design route is: (a) a finite-`p`
**amplitude-ratio identity** tying `Branch.logPhi` to the RTree matching partition function `Ztot`;
(b) a **uniform `O(1/p²)` remainder** so the `p→∞` cherry-hub limit transfers the *inequality* (not
just the pointwise limit); (c) compose with the cavity/realization/matching-sum steps.

## What IS formalized (CI-green on `main`, no `sorry`)

| Step | File | Content |
|---|---|---|
| **1** | `Bridge.lean` | `cav_eq_zc_mul_rho0` — the DEC child-contribution factors as `zc · rho0` (cavity structure) |
| **2** | `BridgeStep2.lean` | `realize : Branch → RTree`, `q_realize_eq_rho0` (`Zopen/Ztot = rho0`), `q_realizeCh_sum`, positivity — the Branch↔RTree realization and its matching identities |
| **3** | `BridgeStep3.lean` | `msum`, `VDisj`, `msum_append` — vertex-disjoint-union **multiplicativity of the matching sum**, plus the `rEdges`/`rRoot`/`rSub` edge realization |
| **4 core** | `BridgeStep4.lean` | `hub_rho0_limit` — a `p`-arm hub decouples: `rho0(node ...) → 1/(1+cav arm)` as `p→∞` (a clean Mathlib `Tendsto`, `field_simp`+`ring`+`Tendsto.div_atTop`) |

All genuine (audited: no `sorry`, `axiom`, `opaque`, `Prop:=True`, `native_decide` anywhere in `R3Cert`).

## What is OPEN (the single remaining bridge gap)

A whole-tree grep of `R3Cert/**` for `per`, `permanent`, `amplitude`, `1/p`, `O(1/p`, `logPhi_le`,
"uniform … remainder" returns **nothing**. So **the capstone is not in Lean at all**:

- **No `per(L(T))`** (the actual tree-Laplacian matching permanent) is defined or connected — the Lean
  works with the RTree-side `Ztot`/`msum`; the identity `msum/Ztot ↔ per(L(T))/∏deg` is unformalized.
- **No uniform `O(1/p²)` rate.** `hub_rho0_limit` gives the *limit* (`Tendsto`), not the *rate*; the
  design needs the uniform remainder to carry `logPhi ≤ 0` through the limit as an inequality.
- **No capstone assembly** composing Steps 1–4 into `logPhi ≤ 0 ⟹ per(L(T))/∏deg ≤ …`.

This matches the standing description ("last + hardest bridge gap", memory
`laplacian_crux_closed_bridge_open_2026-08-18`, tag `G-1`).

## Concrete next steps (schedulable)

1. **Definitional bridge `msum/Ztot ↔ per(L(T))/∏deg`.** Pin down, in Lean, that the RTree matching sum
   `msum (realize t)` equals the tree-Laplacian matching permanent (up to `∏deg`). This is combinatorial
   (matching-sum = permanent of the incidence/Laplacian structure) and is the missing *object*; Step 3's
   `msum_append` multiplicativity is the tool. Do this first — it makes the target expressible.
2. **Finite-`p` amplitude-ratio identity.** State `Branch.logPhi` at finite `p` in terms of `Ztot(realize)`
   (Steps 1–2 give `rho0 = Zopen/Ztot`; assemble the product form).
3. **Uniform `O(1/p²)` remainder.** Strengthen `hub_rho0_limit` from `Tendsto` to a rate: bound
   `|rho0(hub_p) − 1/(1+cav arm)| ≤ C/p²` uniformly in the fixed branches — the genuine analytic core.
4. **Compose** → `logPhi ≤ 0 ⟹ per(L(T))` and splice with R7.

Step 3 is the hard piece; steps 1–2 are mechanical Lean given the existing infrastructure. `conjecture1_proved = False`.
