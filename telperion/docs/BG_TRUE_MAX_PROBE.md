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

Reproduce: `girardeau.hard_core_boson_partition(n, edges)` on `_all_tree_edges(n)` (rooted_phi) and the
`caterpillar(pendants)` builder above.
