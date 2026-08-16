# Laplacian-Ratio (Brualdi–Goldwasser) — session report, 2026-08-11

Branch `review/bush-bound-closed` (fork off `experiment/laplacian-fischer-cavity` @ `caeadad7`).
All modules are self-verifying (`verify()` / `__main__`) with exact `fractions` where it matters and
cross-checks against the ground-truth `general_children_crux.log_phi`. Nothing here overclaims:
**Φ≤1 and Conjecture 1 remain OPEN.**

## TL;DR

- **Piece (ii) of Φ≤1 is now a theorem** — in two forms. The unconditional **bush bound** and the
  corrected **mixed bush bound** are proven for all parameters, closing what the parallel session left
  at `bush_bound_proved=False`.
- **Piece (i), the depth-collapse lemma, is the sole remaining pillar**, and this session pinned its
  obstruction precisely and ruled out the entire local-rearrangement class *and* the nonlinear-JSR cone
  route.
- The invariant-measure dual reveals the extremal object is a **finitely-supported critical (mean-
  offspring-1) branching measure** — pointing the remaining work at smoothing-transform boundary theory.

## The factorisation

Φ≤1 ⟸ **(i) depth-collapse**: every tree's `logΦ(T) ≤` a *mixed bush* at its V — **+ (ii) bush bound**:
every bush `≤ 0`. (`logΦ = Σ_v e_root(v)`; the global maximiser is the near-star tie variety `N(c,k)`,
`c+k=5`, all at cavity `3/23`, `logΦ=0`.)

## Theorems proven this session (exact, verified)

1. **`bush_k1_slice_proof.py` — Q1 (k=1 slice).** `logΦ(B(c,1,t)) ≤ 0` for all `c,t≥0`.
   `bs_val = K·ρ^{c+t}·(D/N)^11`, `ρ=529/486>1`; exact identity `16D−9N = 72t+36c+45 > 0 ⇒ D/N>9/16`;
   geometric escape closes `c+t≥22`, finite core `c+t<22` exact.
2. **`bush_bound_closed.py` — the unconditional bush bound.** `logΦ(B(c,k,t)) ≤ 0` for all `c≥0,k≥1,t≥0`.
   The bush family has a **uniform gap** (max `= ω = −0.0077` at the ARM; no interior tie). Three-piece
   cover: c=0 star; c≥1 easy (R2 monotonicity → Q1); c≥1 non-easy (geometric escape + 60-pt core).
   Verified against ground truth + a 70³ direct scan + extreme spot-checks.
3. **`mixed_bush_bound_closed.py` — the corrected piece (ii).** `logΦ(G) ≤ 0` for the *mixed* bush
   `G=(c,[(t_1,[]),…,(t_k,[])])` (leaf children of **different** cherry-counts — the true per-V
   maximiser; the uniform bush is ~0.001–0.005 suboptimal). Separable bound `U(c,k) = log a + k·max_t[
   gVal(t)+z·m(t)] ≤ 0` (argmax-at-5 tail, `c·ω+0.2115≤0` for c≥28); c=0 handled by k=1 (Q1), k=2
   (finite core), k≥3 (separable). 0 violations over 38k adversarial mixed bushes.

## The depth-collapse (piece i): obstruction pinned, routes ruled out

- **`depth_collapse_probe.py`.** The **per-cavity** framing (the one Locality.lean's rearrangement lives
  in) is circular + integrality-dead. The **per-V** framing is viable; the collapse target is the mixed
  bush. Both natural moves fail: cavity-preserving swap → circular; single-leaf V-flatten → parity-
  blocked ~½ and decreases logΦ ~19%.
- **`flatten_nogo_probe.py` — the parity-aware multiset flatten fails (sharp obstruction).** Replacing a
  subtree by the max-logΦ *same-V mixed bush* is never parity-blocked (mixed bushes exist at every V),
  but still **decreases logΦ ~8%**, and no cavity constraint fixes it. Sharp form: **per-V domination
  holds (0 fails) but per-(V,cavity) domination FAILS** — witness `b=(5,[(4,[]),(4,[]),(5,[(3,[])])])`,
  V=47, cav=21/233, `logΦ=−0.053` beats *every* same-(V,cavity) mixed bush (best `−0.365`, gap 0.312).
  **No mixed bush can both dominate `b` and match `cav(b)`** — that is the wall.
- **`nonlinear_jsr_probe.py` — nonlinear-JSR (Deidda–Guglielmi–Tudisco) audit.** Recast Φ≤1 as
  "nonlinear spectral radius ≤ 1" of the order-preserving `(Φ,μ)` node operator. H1 order-preserving ✓,
  H3 marginal 6-point tie variety ✓, but **H2 sub-homogeneous ✗**: the branching map is degree-k
  (ratios 2,4,8,16), super-homogeneous for k≥2 — outside DGT's cone theory (which covers only k=1
  chains, already certified by `invariant_polytope.py`). The branching amplitude is a critical
  multiplicative cascade; its tropical/log form's Collatz–Wielandt eigenvalue is the circular potential.
- **`invariant_measure_probe.py` — the invariant-measure dual (a run, not a proof).** Occupation-measure
  LP with flow conservation ⇒ **mean offspring = 1 (critical branching)**. `max avg e_root ≈ −0.003`,
  →0 from below as the discretization refines; maximiser **finitely supported (~5 configs), mean
  offspring exactly 1** = the tie structure. Honest limitation: the LP is a finite *restriction*
  (lower-bounds the true max 0), and its dual is the per-point potential (dense/accumulating = the wall).
- **`smoothing_transform_probe.py` — boundary route, regime diagnosis (corrects the premise).** The
  per-V maximum of logΦ has a **unique peak = 0 at V=11** (the tie) and is **strictly < 0 for all V≠11,
  decaying (slowly, ~linear) to −∞**. So sup logΦ = 0 is a **unique isolated *finite* maximiser**, NOT
  a limit approached by large trees — the smoothing-transform **boundary-at-infinity** regime does **not**
  apply. The "mean offspring 1" was an n→∞ idealisation artifact (the finite tie has 10/11); the measure
  dual done exactly gives rate 0 with **zero slack**, so the real content is the finite O(1/n) correction.
  **Redirect:** the right tool is **coercivity / constrained-JSR (~0.9817<1) decay** (extend
  `invariant_polytope` from chains to trees) or **global integrality arithmetic** — not boundary
  martingales. Because the decay is slow there is no cheap finite cutoff.

## Where it stands / next

Φ≤1 rests entirely on the depth-collapse (piece i). The **local-rearrangement class is exhausted**
(cavity-swap circular; single-leaf flatten parity+decrease; multiset flatten mis-cavity; discharging
circular; arm-ification refuted), the **nonlinear-JSR cone route is ruled out** (super-homogeneity), and
the **smoothing-transform boundary route is a mis-diagnosis** (finite isolated maximiser, not a critical
limit). Two candidate routes remain, both heavy:

1. **Coercivity / constrained-JSR decay** — the sup is a unique *finite* maximiser (tie, V=11) with
   slow geometric decay (JSR ~0.9817<1) away from it; extend the chain invariant-polytope
   (`invariant_polytope.py`) to the branching/tree operator. (No cheap finite cutoff — decay is slow.)
2. **Global arithmetic through integrality** — the 23-adic `Rval≤1` style, extended to arbitrary
   branching.

## Verify

```
cd proof/verification
for m in bush_k1_slice_proof bush_bound_closed mixed_bush_bound_closed \
         depth_collapse_probe flatten_nogo_probe nonlinear_jsr_probe invariant_measure_probe; do
  PYTHONPATH="$PWD" python3 -c "import $m as M, json; print('$m', json.dumps(M.verify(), default=str)[:200])"
done
```
(Python 3.14 venv; `invariant_measure_probe` needs scipy — it self-skips if absent.)
