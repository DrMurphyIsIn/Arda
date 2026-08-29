# Classical Brualdi–Goldwasser (`max per(L)/∏deg`): empirical maximizer probe

**Target:** the *actual* BG (1984) open problem — `max_{T tree on n vertices} per(L(T))/∏deg(v)` —
computed exactly with `girardeau.hard_core_boson_partition` (= `∏(1+λ²)`, verified against the
literature to the digit). This is **not** the repo's rooted-branch `Φ¹¹` invariant (see the SCOPE
CORRECTION in `PROOF_STATUS.md`). `conjecture1_proved = False`.

## Findings (exact rational computation)

**1. Small-n maximizer (exhaustive over all trees, n ≤ 17):**
- **odd n:** the near-star `N(0,(n-1)/2)` (single hub, all length-2 arms) — matches Wu–Dong–Lai (2025).
- **n = 4k:** two hubs of degrees differing by 1. **n = 4k+2:** two equal hubs.

**2. Regime change at n = 23 (odd branch).** The near-star wins for odd `n ≤ 21`; at `n = 23` Pant's
caterpillar `T(3,t,3)` overtakes it (margin grows: `cat/ns` = 1.007 at n=23 → 1.029 at n=45). This
reproduces Pant (2026, arXiv:2605.14176) refuting the WDL conjecture, and pins the crossover **exactly
at n=23**.

**3. Pant's `T(3,t,3)` is NOT the true maximizer.** Searching all caterpillars `T(a₁,…,a_m)` with
length-2 pendants: the maximizer is the **balanced equal-thirds `T(a,a,a)`** (m=3, `a=(n-3)/6`), which
beats `T(3,t,3)`:

| n | Pant `T(3,t,3)` | best caterpillar | winner |
|---|---|---|---|
| 27 | 263.55 | **`T(4,4,4)` = 265.39** | equal-thirds |
| 33 | — | **`T(5,5,5)`** | equal-thirds |
| 39/45/51 | — | **`T(6,6,6)`/`T(7,7,7)`/`T(8,8,8)`** | equal-thirds |

**4. Length-2 is the optimal pendant length** (single-hub per-vertex rate: L=1→1.023, **L=2→1.226**,
L=3→1.207, L=4→1.209). The extremal local motif is a hub with length-2 arms.

## Globality test (2026-08-29): `T(a,a,a)` is NOT the global max

Tested `T(a,a,a)` against non-caterpillar and multi-block competitors at matched large n:
- `T(a,a,a)` beats the near-star at matched n with **exponentially growing margin** (ratio 1.02→1.16
  over n=27→303) — so it beats WDL and Pant, but…
- **Rate increases with block count** (m=2→1.2254, m=3→1.2257, m=10→1.2272 at n≈300) and **with
  arms-per-vertex up to an optimum** — so 3 equal blocks is *not* extremal.
- The true large-n extremal is a **periodic caterpillar with ~8 length-2 arms per spine vertex**
  (m→∞). `ρ(a)` = periodic rate peaks at **a≈8**: ρ(6)=1.22762, **ρ(8)=1.22763**, ρ(10)=1.22747.
- Non-caterpillar competitors (star-of-k-hubs, cherry-arms) all score **lower**.
- The per-vertex rate is **maximized at small n** (exhaustive: ~1.231 at n≤19) and **decreases
  monotonically to ρ\* ≈ 1.22763** — the archimedean "approach, no clean finite maximizer" pattern.

## The true target: ρ\* as a matching free-energy

`per(L)/∏deg = ∏(1+λ²)` ⟹ `(per/∏deg)^{1/n} = exp((1/n)Σ log(1+λ²))`, so
**`ρ* = exp( max_μ ∫ log(1+λ²) dμ )`** over unimodular (Benjamini–Schramm) tree spectral measures `μ`
(Csikvári's matching-measure framework). Empirically `ρ* ≈ 1.22763`, achieved by the ~8-arm periodic
caterpillar. **This — not `T(a,a,a)` — is the object the Gurvits-capacity / free-energy proof-attack
must target.** Open: the exact `ρ*` (closed form?), the exact extremal motif, and the finite-n
optimizer per residue class.

## Proof-attack plan (the synthesized strategy)

`ρ*` is a **free-energy-per-site / Benjamini–Schramm** quantity — the max matching-free-energy over
unimodular tree limits (Csikvári; Abért–Csikvári–Frenkel–Kun). The collective upper bound is a
**Gurvits-capacity** problem (variational, not pure-SOS, so not blocked by Koiran's real-root barrier);
strictness/exact extremal structure needs the arithmetic layer. See `~/.claude/plans/quiet-singing-kahn.md`.

## The exact Φ¹¹ ↔ classical-BG bridge (2026-08-29)

The repo's rooted-branch `Φ¹¹` is **not** a separate object — it is the classical BG quantity times a
single root-local factor. Verified exactly for all trees n=4–8, all roots:

- The plain cavity product `∏_v a_v` with `z_v = 1/deg_v` for **all** v **equals `per(L)/∏deg`** (the
  classical BG quantity; root-independent).
- `Φ¹¹`'s amplitude uses `z_root = 1/(deg_root+1)` — a **virtual-parent half-edge**, *not* a phantom
  leaf (a phantom leaf gives `351/32 ≠ 621/64`; refuted). This changes exactly one factor:

  **`Φ¹¹(T) = max_r (64/621)^n · [ (per(L)/∏deg) · g_r ]^{11}`,  `g_r = (1+S_r/(d+1))/(1+S_r/d) < 1`**

  where `d = deg(root)`, `S_r = Σ` root-children cavity messages.

**Consequences.**
- `Φ¹¹` "root-closes" `per(L)/∏deg`: giving the root a virtual parent makes *every* vertex obey the
  identical cavity recursion ⟹ cavity-factorizable ⟹ the extremality is provable (the entire
  star-archetype / tmaxHub / IDENTITY-2 machine). Plain `per(L)/∏deg`'s max-over-roots has no such
  closure — which is exactly why classical BG is open.
- Exact bridge: `Φ¹¹ ≤ 1 ⟺ per(L)/∏deg ≤ ρ_B^n / g_r*` (at the deficiency-minimizing root `r*`).
  Since `g_r* < 1`, this is *weaker* than `per ≤ ρ_B^n` (which is false ∀n≥4) — the factor `g_r`
  absorbs the difference. This quantifies the rooted↔unrooted gap **in closed form**: it is the single
  local factor `g_r`. Closing the gap (bounding `g_r*` structurally) is the precise, well-posed research
  question linking the provable rooted invariant to the open classical problem.

Reproduce: `girardeau.hard_core_boson_partition(n, edges)` on `_all_tree_edges(n)` (rooted_phi) and the
`caterpillar(pendants)` builder above; the plain-vs-rooted cavity and the `g_r` factor are direct.

## The g_r bridge FAILS to bound classical BG (2026-08-29, negative result)

Using the exact identity `per(L)/∏deg = ρ_B^n · Φ¹¹^{1/11} / g_r*`, the rooted bound `Φ¹¹ ≤ 1` gives
`per ≤ ρ_B^n/g_r*`. Tested on the classical maximizer `T(a,a,a)`: the overshoot `UB/per = 1/Φ¹¹^{1/11}`
**grows** (1.05 at n=15 → 1.32 at n=123). Reason: at the classical maximizer **`Φ¹¹ → 0`** (0.59→0.049),
because that tree is structurally far from the rooted optimum — so `Φ¹¹≤1` is nearly vacuous there and
`g_r*` (which stays ≈1) can't help. The rooted invariant does not "see" the classical maximizer;
`ρ_B > ρ*` makes the rooted bound overshoot by `~(ρ_B/ρ*)^n`. **The bridge cannot prove classical BG.**

## Capacity attack on ρ*: exact free-energy + globality evidence (achievability done)

**Closed-form free-energy** of the periodic a-arm caterpillar via the cavity fixed point (verified vs
empirical to <1e-4):

`ρ(a) = [ a_spine · (3/2)^a ]^{1/(1+2a)}`, `a_spine = 1/((a+2)μ)`,
`μ = (-(d+a/3)+√((d+a/3)²+4))/2`, `d=a+2`.

Maximized over the (continuous) motif at **a\* ≈ 7.02, ρ\* = 1.2276458** — the empirical peak, now an
exact algebraic object. **Achievability / lower bound `ρ* ≥ 1.22765` is done in closed form.**

**Globality evidence (strong):** no broader family exceeds ρ\* — cherry-arms (1.185), 2-level
decorated (1.222–1.224), non-uniform alternating a=6/8 (1.22762, *below* uniform a=7). Uniform beats
non-uniform ⟹ the free-energy is **concave in the motif**, and length-2 is the optimal arm length.

**Remaining (the hard open direction):** the rigorous **upper bound** `per(L)/∏deg ≤ ρ*^n · poly(n)` for
*all* trees — i.e. the matching-free-energy-per-site is globally maximized by the ~7-arm caterpillar.
Route: Gurvits capacity of the degree-normalized permanent (variational, not pure-SOS ⟹ not blocked by
Koiran) and/or a free-energy concavity/entropy argument (Csikvári). This is genuine research; the target
(ρ\*, exact) and the extremal family (~7-arm periodic caterpillar) are now pinned. `conjecture1_proved = False`.

## Upper-bound attempt (a): local certificate FAILS (same collective wall as Φ¹¹)

Exact Bethe form (verified all trees n≤8): `per(L)/∏deg = ∏_v V_v / ∏_e E_e`, with
`V_v = 1+Σ_{u~v} t_{vu} g_{u→v}`, `E_e = 1+t_e g_{u→v}g_{v→u}`, `t_{uv}=1/(deg_u deg_v)`, messages
`g_{u→v}=1/(1+Σ_{w≠v}t_{uw}g_{w→u})∈(0,1]`. Splitting each edge 50/50 gives per-vertex
`φ_v = log V_v − ½Σ_{e∋v} log E_e` with `Σφ_v = log Z`, so `φ_v ≤ log ρ* ∀v ⟹ per/∏deg ≤ ρ*^n`.

**It fails.** At the extremal ~7-arm caterpillar the split is non-uniform: `φ_leaf=0.196`,
**`φ_mid=0.225 > log ρ*=0.205`**, `φ_spine=0.135`. Arm-mids exceed the bound; spine/leaves are below;
they average to `log ρ*`. The relaxed max over free messages is far worse (0.35–0.44). This is the
**same collective-cancellation obstruction the repo found for the rooted `Φ¹¹`** — classical BG is *not*
a "nicer" object with a local bound; both are genuinely collective.

**But the discharging is exactly balanced:** total mid-excess (7×0.0195=0.137) ≈ total slack
(spine 0.070 + 7 leaves 0.067 = 0.137); each mid pulls slack from its leaf + spine-share to *zero
margin*. So a *tight discharging / flow* certificate (non-equal edge weights) is the right structure —
but exactly-tight (zero margin at the extremum), which is the hard collective core. **Conclusion:**
naive approach (a) is closed off; the upper bound needs either a tight discharging argument or the
Gurvits-capacity route (b). Both the rooted `Φ¹¹` and classical BG hit the identical wall — a unifying
finding. `conjecture1_proved = False`.
