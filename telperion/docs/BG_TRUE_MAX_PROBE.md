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
