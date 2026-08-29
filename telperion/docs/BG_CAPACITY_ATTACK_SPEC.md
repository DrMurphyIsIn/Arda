# Capacity-attack spec — the upper bound for classical Brualdi–Goldwasser

**Status:** planning spec for route (b), the Gurvits-capacity upper bound. Written as a deliberate,
pick-up-cleanly effort — NOT a proof grind. Prerequisites (all done, see `BG_TRUE_MAX_PROBE.md`):
`ρ*` pinned exactly, achievability proven, and BOTH cheaper routes closed as negatives (the `g_r`
bridge from Φ¹¹, and the local Bethe certificate (a)). `conjecture1_proved = False`.

## 0. The target

Prove, for every tree `T` on `n` vertices:

    per(L(T)) / ∏_v deg(v)  ≤  ρ*^n · poly(n),      ρ* = 1.2276458…

equivalently, the matching free-energy-per-site `sup_T (1/n) log Z(T) = log ρ*`, attained (in the
Benjamini–Schramm / unimodular-tree-limit sense) by the **uniform ~7-arm, length-2-arm periodic
caterpillar**. `ρ*` is the exact algebraic maximum of the closed-form single-motif free-energy

    ρ(a) = [ a_spine · (3/2)^a ]^{1/(1+2a)},   a_spine = 1/((a+2)μ),
    μ = (−(d+a/3) + √((d+a/3)² + 4)) / 2,   d = a+2,     max at a* ≈ 7.02.

Achievability `ρ* ≥ 1.22765` is done in closed form; globality is strongly evidenced (no broader
family — cherry-arms, 2-level, non-uniform — exceeds it). The OPEN direction is the matching upper
bound over ALL trees.

## 1. The quantity and its four exact forms

`Z(T) := per(L(T))/∏deg`. On a tree these all coincide (verified n ≤ 8/9):

1. **Monomer–dimer sum:** `Z = Σ_{matchings M} ∏_{(i,j)∈M} t_{ij}`, edge weight `t_{ij} = 1/(deg_i deg_j)`.
2. **Free-fermion / spectral:** `Z = ∏_{λ>0}(1+λ²)`, `λ` = eigenvalues of the normalized adjacency
   `N = D^{-1/2} A D^{-1/2}`. So `F(T) = (1/2)∫ log(1+x²) dμ_N(x)`, `μ_N` = spectral measure of `N`.
3. **Functional determinant:** `Z = |det(I + iN)|`.
4. **Bethe vertex–edge (exact on trees):** `Z = ∏_v V_v / ∏_e E_e`, `V_v = 1+Σ_{u~v} t_{vu} g_{u→v}`,
   `E_{uv} = 1 + t_{uv} g_{u→v} g_{v→u}`, messages `g_{u→v} = 1/(1+Σ_{w~u, w≠v} t_{uw} g_{w→u}) ∈ (0,1]`.

Form 2 is the key for (b2): `F` is a **spectral functional** of `μ_N`. Form 4 is why (a) was even
attempted (per-vertex decomposition).

## 2. Why (a) failed, and the precise job for (b)

From Form 4, `φ_v := log V_v − ½ Σ_{e∋v} log E_e` gives `Σ_v φ_v = log Z`, so a *local* certificate
would be `φ_v ≤ log ρ*` for all `v`. **This fails** at the extremal caterpillar: `φ` is non-uniform
(`φ_mid = 0.225 > log ρ* = 0.205 > φ_spine = 0.135`), with a **tight, zero-margin discharging** (total
arm-mid excess ≈ total spine+leaf slack). The excess and slack cancel only *globally*. This is the
**same collective-cancellation wall the rooted Φ¹¹ hit** (its `+0.199` stall) — a unifying finding:
the difficulty is intrinsic to the matching free-energy, not to the rooting.

So (b) must produce a **global/collective** bound in which the discharging is built in — the dual
"fields" are allowed to be non-uniform and route the excess. Two rigorous handles follow.

## 3. Route (b1): Gurvits capacity of the matching generating polynomial

**Objects.** The matching generating polynomial `g_T(z, {t_e})` is **real-stable** (Heilmann–Lieb
real-rootedness) — the setting where Gurvits capacity is sharp. Capacity:
`cap(p; α) = inf_{x>0} p(x) / ∏_i x_i^{α_i}`.

**The idea.** Encode `Z(T)` (or its `n`-th root) as a coefficient / evaluation of a real-stable
polynomial, then use **weak duality**: *any* positive field configuration `y = (y_v)` gives a valid
upper bound `Z ≤ p(y)/∏ y_v^{α_v}`. The dual fields `y_v` are exactly the "discharging" from (a),
but now **coupled through the inf** — so non-uniform routing is legal (this is the fix for (a)).

**Milestones.**
- **M1.** Write `Z(T)` as `cap` (or a weak-duality evaluation) of a real-stable polynomial; verify
  numerically `cap = Z` on trees (Gurvits capacity is exact for real-stable degree-n-in-n; confirm).
- **M2.** Derive the inf-over-fields dual form; find the tight dual `y*` at the ~7-arm caterpillar —
  it should coincide with the zero-margin discharging measured in (a).
- **M3.** Prove `y*` (or a uniform-in-`T` field construction) is valid for ALL trees (the global
  inequality via weak duality — this is the real theorem).
- **M4.** Prove the bound is **tight to `ρ*^n`** (not merely `e^{cn} ρ*^n`) — the hard collective core.

**Why it can work / the sharpness caveat.** Capacity is variational and collective (it bounds the
whole permanent at once) — the right shape for a collective wall, and **not** blocked by Koiran's
real-root SOS/Positivstellensatz no-go (capacity is not a sum-of-squares certificate). BUT classical
Gurvits/Van-der-Waerden capacity bounds are loose by `n!/n^n ≈ e^{-n}` — for BG we need the bound
**exact** to `ρ*^n`. Closing that multiplicative gap for THIS quantity is the crux, and is open.

## 4. Route (b2): spectral / free-probability upper bound

From Form 2, `sup_T F = (1/2) sup_μ ∫ log(1+x²) dμ` over `μ` = spectral measures of normalized
adjacencies of unimodular tree limits. `μ_N` is symmetric, supported in `(−1,1)`, with moments =
normalized closed-walk densities of a tree (a **tree Jacobi operator** / free-convolution object).

**The idea.** Characterize the achievable-`μ_N` variational class for unimodular trees (Kesten–McKay /
Abért–Csikvári–Frenkel–Kun **matching-measure** framework), then maximize `∫ log(1+x²) dμ`. The
maximizer is the ~7-arm caterpillar's spectral measure. This is a genuine moment/entropy optimization
over tree spectral measures.

**Milestones.**
- **M5.** State the exact variational class of unimodular tree spectral measures (the constraint set).
- **M6.** Solve `max ∫ log(1+x²) dμ` over it; confirm the maximizer = the caterpillar measure and value
  `= log ρ*`.
- **M7.** Convert the measure-level max into a finite-`n` bound `Z(T) ≤ ρ*^n · poly(n)` (Benjamini–Schramm
  continuity + a finite-size correction).

**Csikvári handle.** The matching measure is monotone/extremal under tree operations (Csikvári's
`per(L)`-immanant and matching-polynomial results); the concavity-in-the-motif evidence from
`BG_TRUE_MAX_PROBE.md` (uniform beats non-uniform) is the finite-side shadow of a free-energy
concavity that (b2) would make rigorous.

## 5. The tightness requirement (non-negotiable)

Any valid upper bound `U(T) ≥ Z(T)` must have `U(caterpillar) = ρ*^n·(1+o(1))` — the caterpillar
*achieves* `ρ*` and the zero-margin discharging leaves NO slack. So the certificate/dual point must be
**exactly optimal at the extremum**, not merely valid. A loose relaxation (e.g. `e^{cn} ρ*^n`, `c>0`)
does NOT settle BG. This is what makes (b) hard: the collective bound has to be sharp, and sharpness
at a zero-margin extremum is precisely the collective core.

## 6. Decision gate (pick-up guidance)

- Start with **(b1) M1–M2** — cheap and diagnostic: if `cap = Z` on trees and the tight dual at the
  caterpillar reproduces the (a) zero-margin discharging, the dual variables ARE the flow, and (b1) is
  live. If the capacity is loose (M1 shows an `e^{cn}` gap), switch to **(b2)** — the spectral route
  doesn't have the Van-der-Waerden slack.
- Milestone with a certifiable payoff: **M3** (a valid global upper bound, even if not tight) is
  already a publishable rigorous ceiling on classical BG; **M4/M7** (tightness) is the full solution.

## 7. Honest risks

- **Tightness (primary):** capacity/free-energy upper bounds are generically loose; nobody has proven a
  tight `ρ*^n` bound for this quantity. Real, open, no guaranteed close.
- **Tree-class characterization (b2):** the exact variational class of unimodular tree spectral measures
  is itself hard free-probability.
- **Both routes are multi-step research**, not increments. This spec pins the target and the tools; it
  does not claim (b) is close.

## 8. Reproduce / verify hooks

`girardeau.hard_core_boson_partition(n, edges)` (= `per(L)/∏deg`, exact rational); the Bethe form and
`φ_v` split (§2); the closed-form `ρ(a)` and the caterpillar builder (`BG_TRUE_MAX_PROBE.md`);
`rooted_phi._all_tree_edges(n)` for exhaustive small-`n` checks. Verify any proposed dual/certificate
against these before scaling.
