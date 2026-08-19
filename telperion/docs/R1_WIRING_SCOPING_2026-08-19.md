# R1 single-hub branch-induction wiring — scoping & attack plan

Target: close R1 (single-hub extremality) = the master inequality
`(2+μ_B)^11 · F_B ≤ (64/621)·3^11 =: C` for **every** rooted tree `B`, equality iff `B` is a
leaf (`arm_maximal.py`). This is the load-bearing open piece of R1. `conjecture1_proved = False`.

## Where R1 actually stands (sharper than PROOF_ASSEMBLY's coarse tags)

The master inequality is proved by strong induction on `n_B`, `F_B = (64/621)·a_B^11·∏_c F_c`,
`a_B = 1 + S/(j+1)`, `μ_B = 1/(j+1+S)`, `S = Σ_c μ_c`.

| Induction case | Status | Where |
|---|---|---|
| Base: leaf (`3^11·64/621 = C`, tight) | **PROVEN** | `arm_maximal` |
| `j=1` (one child): telescopes via `(1+μ_c/2)·3/(2+μ_c)=3/2` | **PROVEN** | `arm_maximal.master_telescopes_to_arm` |
| `j≥2` branching: g-step **coordinate-wise unimodality**, box-max at symmetric `μ*` | **PROVEN over ℝ** | `branching_unimodality` (T1 `11/((j'+1)boost)>0`; T2 via exact `(j'+1)boost=j'+4/3+S ≥ 10/3+μ_i > 3+μ_i`) |
| g-step symmetric value `< γ` (two rational leaves `μ*<1/3`, `W(4/3)^11<γ`) | **PROVEN** | `gstep_reduction` |
| leaf-child case (message `μ=1`) | **PROVEN** (subsumed) | `branching_unimodality`: the descent needs only `μ_i≤1`, so the same box-max over `(0,1]^{j'}` covers it |

So R1's **analytic** content is complete. What remains are two **all-n structural** lemmas,
both currently *verified on the census (n≤11, 0 violations)* but not proved for all n:

### (L-relax) The relaxation lemma — `g_bound(child messages) ≥ g(C)` for every block `C`
The g-step optimization bounds the *true* per-block quantity `g(C)` by the relaxed
`g_bound(μ_1..μ_{j'}) = W·boost^11·∏_i min(1, γ/(1+μ_i/3)^11)`. The unimodality proof bounds
`g_bound`; it only closes `g(C) ≤ γ` if `g_bound ≥ g(C)`. Verified on the census (0 failures /
582 leaf-child blocks, extended to `μ=1`); the all-n proof is the parallel session's relaxation
lemma. **Shape: a per-block inequality over an infinite tree family — structural, not a
fixed-grid rational inequality (not an evolve target).**

### (L-wire) The g-lemma ⟹ master wiring (the "AM-GM split")
Given the induction hypothesis (each child `c` satisfies master: `(2+μ_c)^11 F_c ≤ C`) and the
g-lemma (`g(C) ≤ γ`), derive the parent master `(2+μ_B)^11 F_B ≤ C`. The obstruction is explicit
(`arm_maximal.naive_induction_is_lossy`): naive per-child substitution `F_c ≤ (64/621)(3/(2+μ_c))^11`
injects a factor `C^{j-1}` (`C≈18257`) that blows up for `j≥2`. The g-lemma's two-regime product
is what defeats it; the wiring — an **AM-GM split** redistributing the blow-up across children —
is *verified sound on the census (n≤11)* but not proved all-n.

## Proposed attack (in priority order)

1. **(L-wire) first — it is the true crux and the more self-contained algebra.** Make the AM-GM
   split *explicit and symbolic*: write the parent master LHS `(2+μ_B)^11 F_B` in terms of the
   children `(μ_c, F_c)` via the recursion, substitute the g-lemma bound, and exhibit the exact
   AM-GM inequality that collapses the `C^{j-1}` factor to `1`. If the split closes symbolically
   for general `j`, that *is* the wiring. Deliverable: a `MasterWiringCertificate` that certifies
   the AM-GM step in exact arithmetic per-`j`, plus a Lean-emittable form of the scalar AM-GM
   inequality it rests on.
2. **(L-relax) second.** The relaxation `g_bound ≥ g(C)` is a per-block monotone-envelope claim;
   its all-n proof likely follows the same message-recursion + two-regime structure. Confirm
   whether the parallel session's lemma already covers `μ∈(0,1]` (the leaf-child extension) or
   needs the `μ=1` endpoint argued separately.
3. Only once (L-wire)+(L-relax) are proved: assemble base + chains + branching + leaf-child into
   the full strong induction and emit the R1 closure to Lean (CI-verified).

## Step 1 result — the census slack map (2026-08-19)

Naive term-by-term bounding closes the master induction at a branching vertex `B` iff
`R(B) = (2+μ_B)^11·W·a_B^11·C^{j-1}/∏_c(2+μ_c)^11 ≤ 1` (a function of the children's messages
only). Computed exactly (Fractions), cross-checked at the cherry (`R≈0.0966`):

- **Naive fails on 66 / 339 census branching blocks** (m≤9), and the failure is **unbounded over
  real trees**: max slack by size `m=5:1.15` (first failure) → `m=9:3.55` → `m=11:6.05`, worst
  branching degree climbing `j=2→3→4`.
- **Per-degree blow-up `~κ^j`, with the exact constant `κ = W·(3/2)^11 = 8.9144`**, approached as
  all child messages `→ 0` (deep-subtree children). Leaves (`μ=1`) give tiny `R` — the loss comes
  from *several small-message children*.
- `κ = 8.914` is **exactly** the "~8.9 crude separable bound" the g-lemma's docstring says its
  two-regime product `∏ min(1, γ/(1+μ_i/3)^11)` exists to defeat. So the diagnosis is precise:
  **the AM-GM split must convert an unbounded `κ^j` naive blow-up into `≤1`, and the g-lemma's
  per-child suppression is the intended lever.**

## Step 2 status — BLOCKED on a missing prerequisite (`g(C)` recursion)

Attempting the AM-GM split requires the exact `g(C)` the g-lemma bounds (`g(C) ≤ γ`). **That
recursion is not materialized in the accessible codebase**: `γ` is *defined* (`gstep_reduction`,
`branching_unimodality`) but **never used to bound `F`** in any master/interior module; no `g(C)`
recursion or "relaxation lemma" is implemented; the wiring is only *asserted* ("verified sound on
census, n≤11") in prose. Deriving the AM-GM split without `g(C)` would be fabrication — and
`envelope.py` already proved the closing invariant must be **joint over siblings** (no per-message
`h(μ)` is a supersolution), so this is the genuine collective crux, not a separable estimate.

**Concrete unblock for step 2:** materialize `g(C)` — either recover the parallel session's
relaxation-lemma / g-recursion code, or reconstruct `g(C)` as its own defined+census-validated
sub-task — *then* derive the AM-GM split against the step-1 worst locus (high-degree,
small-message children) and emit the scalar AM-GM inequality to Lean. Until then step 2 cannot
proceed honestly.

## Step 2 reconstruction attempt — candidate-space map (2026-08-19)

Tried to materialize `g(C)` directly, verifying every candidate in exact arithmetic on the
census. Result: the natural **separable** candidates are refuted, and refuted in the way
`envelope.py` predicted.

| Candidate invariant | Valid? | Propagates (naive)? | Why it fails |
|---|---|---|---|
| master `(2+μ)^11 F ≤ C` | yes | **no** | per-child blow-up `κ=W(3/2)^11=8.91`, unbounded `κ^j` (step 1) |
| message-based `g₁ = W·boost^11·∏min(1,γ/(1+μ_c/3)^11)` | `≤γ` on census (the proven g-step bound) | n/a | uses child *messages*, not `F` — `g₁≤γ` doesn't bound `F_c`, so it isn't an `F`-induction |
| F-based `(3+μ)^11 F ≤ W·4^11` (tight at leaf) | **no** — fails at the **arm** (`gt/T=1.20`) | slack `~0.7`, but **creeping up** with `m` (0.25→0.84 at m=12) | tight at the leaf but overshoots the extremal arm; a single reweighting can't be tight at *both* fixed points |

**The lesson (verified, not asserted):** the per-child factor improves `8.91 → 2.44` under the
`(3+μ)` reweighting but never reaches `≤1`, and the invariant must be **tight simultaneously at
the two extremal blocks — the leaf (`μ=1`) and the arm (`μ=1/3`, `F=486/529`)**. No single-formula
separable reweighting of `F` can do that; it forces the piecewise **two-regime `min(·)`** structure,
i.e. a genuinely **joint / non-separable** invariant. That is exactly `envelope.py`'s theorem
("no single-variable `h(μ)` is a supersolution; the closing invariant must be joint over
siblings") — now reconfirmed constructively from the master side.

**Conclusion:** reconstructing `g(C)` is not a normalization exercise — it *is* constructing the
joint collective-cancellation invariant, i.e. re-solving the R1 crux. The reconstruction attempt
mapped the separable candidate space, quantified each failure exactly, and pinned the two-point
(leaf+arm) tightness constraint that forces non-separability. It did **not** produce a valid
self-propagating `g(C)` — and honestly cannot short of the crux. `conjecture1_proved = False`.

## Joint-invariant construction attempt (2026-08-19)

Formulated the wiring as a super-solution: with potential `P(B)=11log(2+μ_B)+log F_B−log C`
(master ⟺ `P≤0`), the recursion is `P(B)=Σ_c P(c)+Δ`, `Δ=log R` (the step-1 slack). A potential
invariant `P ≤ −σ(·)` propagates iff `Δ ≤ Σ_c σ(child) − σ(parent)`. Tested by LP with proper
out-of-sample validation on **achievable** configs (diverse trees to n≈30, messages to 0.067):

| Invariant form | Result |
|---|---|
| separable `σ(μ)` | census-feasible `t*=−0.75`, **held-out +0.87** (overfit); box stress `+2.5…+10`. No-go. |
| structural reason | for `P ≤ −σ(μ)`, the propagation worst case pins each child to its boundary `P(c)=−σ(μ_c)`, collapsing back to the separable condition — a per-block-`μ` invariant provably cannot close it. |
| 2-param joint `σ(μ,S)` (S = own children-sum) | held-out improved to `+0.27`, but **cutting-plane does not converge**: fresh larger trees give violations `+3…+61` that the form fits in-sample but never generalizes past. |

**The no-go extends to all *local* invariants, including discharging.** Any per-vertex scheme
(potential `P≤−σ(μ)` or a charge-redistribution `child → parent`) has its propagation worst case
at the child boundary — the induction may only assume `P(c) ≤ −σ(μ_c)`, so the tightest case is
`P(c) = −σ(μ_c)` (zero surplus), which collapses back to the separable condition `Δ ≤ Σσ(μ_c) −
σ(μ_B)`. Discharging cannot rely on deep children having spare credit, because the IH does not
guarantee it; requiring it *is* a tighter separable bound, already refuted. So the genuine
closure must be **non-local** — an invariant coupling a vertex to its descendants beyond one
level — which is exactly the collective crux.

**Result:** finite-basis potential invariants — separable *and* the `(μ,S)`-joint form — do **not**
close the R1 wiring under cutting-plane, and no *local* per-vertex invariant can (boundary
argument above). Each fits any finite sample and fails on the next, the
signature of the collective crux. This reproduces the program's documented no-go
("LP cutting-plane… no finite-basis `P` closes it") for the master formulation, and rules out the
tractable potential-method routes constructively. The genuine closure needs the
arithmetic/non-potential structure the crux is known to require — i.e. constructing it *is*
solving the crux, not an LP fit. `conjecture1_proved = False`.

## Honest scope
R1 is **one front** (single-hub); R2 multi-hub maximality is a *separate* open extremality theorem
(verified n≤13) and is the collective crux — out of scope here. Neither remaining R1 lemma is a
Pólya/parameter-search shape, so `telperion.evolve` is not the tool (per the evolve/BG scoping
doc); this is symbolic-algebra + structural-induction + Lean formalization. `conjecture1_proved
= False` until both all-n lemmas land and the induction is assembled and kernel-checked.
