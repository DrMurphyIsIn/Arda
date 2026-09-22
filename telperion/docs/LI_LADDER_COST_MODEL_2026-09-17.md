# Li ladder — honest cost model (Route B / B1, 2026-09-17)

**Read this first.** Certified prefixes of the Li ladder are *instrumentation, not evidence*
(RH_ROUTES_ROADMAP_2026-09-16.md, §3): they are morally forced by the on-line verification of
zeros that already exists to height 3·10¹² and carry no independent RH content. This document
measures what the instrument costs and how it must be packaged, states why its tail cannot be
bought, and installs the negative-control twin that shows the instrument fires on something
false. Nothing here is progress on RH. `conjecture1_proved = False`.

Scope of the milestone (roadmap B1): *ladder throughput: certified λ-prefix to n ≈ 10³ + honest
cost model + negative-control twin*. Delivered: the enclosure side measured to N = 10⁴, the Lean
side measured to N = 10³, a bundled-hypothesis packaging discipline prototyped on the committed
20 rungs, and an in-kernel negative control. The committed ladder stays at 20 rungs.

## 0. What the instrument is

`examples/li_positivity/generate.py` encloses the coefficients

    taylorCoeff riemannXi n  =  [zⁿ] (d/dz) log ξ(1/(1−z))  =  Li's λ_{n+1}

with Arb ball arithmetic on the pole-free series route (`telperion.li_coeff.enclose_li_coeffs`:
ξ expanded at s = 0 through the functional equation, F′/F read off `xi.derivative() * xi.inv()`
as truncated power series — one `acb_series` computation per prefix). It self-checks the first
three enclosures against the published Li–Keiper values (Keiper 1992 / Li 1997 / Coffey 2004)
and otherwise relies on Arb's ball soundness: every returned `(lo, hi)` is an outward dyadic
enclosure of the true coefficient. Each rung is then the theorem

    li_rung_n (hlo : (lo : ℝ) ≤ (taylorCoeff riemannXi n).re) : 0 ≤ (taylorCoeff riemannXi n).re

against the upstream `LiCriterion.li_criterion_rh_iff` (RH ⟺ ∀ n, 0 ≤ this). The Arb enclosure
is the ONE documented non-kernel input, carried as the hypothesis `hlo`.

The self-check is an index/normalization anchor only: rungs n ≥ 3 have no external anchor and
rest on ball soundness. (A genuinely independent cross-check — e.g. the Bombieri–Lagarias sum over
verified zeros with a rigorous tail — is not in tree; it would be a sanity anchor, not a rigor
input, and is listed under open items.)

## 1. Enclosure cost (Arb side)

Bench: `examples/li_positivity/bench_li_ladder.py` (Apple M3 Ultra, python-flint 0.6.0, single
thread). For each N: the smallest working precision (bisected to 32-bit granularity) at which
*every* rung n < N keeps ≥ 40 relative bits (= the 12-significant-decimal literal the emitter
writes), and the wall time at that precision.

| N (rungs) | min. precision (bits) | wall time at min. prec. | λ_N (last rung, midpoint) | max ‖ξ-series coeff‖ (log₂) |
|---:|---:|---:|---:|---:|
| 20 | 96 | < 1 ms | 8.769276872 | −1.0 |
| 50 | 96 | 1 ms | 43.53109649 | 2.6 |
| 100 | 160 | 4 ms | 118.6037754 | 7.8 |
| 200 | 256 | 13 ms | 306.6557649 | 16.2 |
| 500 | 544 | 85 ms | 991.9000930 | 35.2 |
| 1 000 | 1 056 | 0.43 s | 2 326.053162 | 58.9 |
| 2 000 | 2 048 | 3.7 s | 5 351.759538 | 95.1 |
| 5 000 | 5 024 | 38 s | 15 639.09422 | 173.2 |
| 10 000 | in (8 192, 16 384] | 519 s at 16 384 bits | 34 736.57973 | 267.6 |

(All lower bounds positive at every N; all enclosures at the listed precision have ≥ 40 relative
bits, most far more — at N = 1000 and 2048 bits the last rung has 1049 bits.)

**Fits.**

* *Precision.* `prec_min(N) ≈ N + 56 bits` (100 → 160, 200 → 256, 500 → 544, 1000 → 1056,
  2000 → 2048, 5000 → 5024). The ladder loses **about one bit per rung**. Below that precision the
  balls are honest but useless (N = 1000 at 1024 bits: 24 bits at the worst rung; at 512 bits the
  radii are 10¹⁴⁶ — the self-check catches nothing there because rungs 0–2 are still fine; the bench
  catches it by the width criterion). The loss is not in the ξ series itself — its largest
  coefficient grows only like 2^{0.06 N} (last column) — it is in the truncated inversion `xi.inv()`:
  1/F has radius of convergence exactly 1 (the zeros of F are the images of ξ's zeros on the unit
  circle), so nothing geometric damps the compounding of ball radii through N orders of the
  inversion. This is a measured statement; the mechanism sentence is the natural reading, not a
  theorem.
* *Time.* `t(N) ≈ 4·10⁻¹⁰ · N³ s` (1000 → 0.43 s, 5000 → 38 s vs. fit 54 s, 10 000 → 519 s at
  twice the minimal precision vs. fit 430 s). Series operations quadratic in N at precision linear
  in N: **cubic, polynomial**, no worse. With `prec_bits_for(N) = max(192, 2N + 128)` (the
  generator's default, a ≥ N-bit safety margin) the 10³ ladder encloses in ~0.7 s and the 10⁴
  ladder in ~9 min.

**Verdict.** The enclosure side is not a bottleneck at any N anyone would want: n ≈ 10³ is under
a second, n ≈ 10⁴ is minutes. This is exactly the roadmap's point — the prefix is cheap *because*
it is instrumentation.

## 2. Kernel / Lean cost

Trial files from `generate.py --trial N` (namespace `LiPositivityTrial`, never wired into the
lakefile, ignored by git; sizes 54 KB / 107 KB / 267 KB / 532 KB for N = 100 / 200 / 500 / 1000).
Timing: `lake env lean <file>` wall clock, warm, two repetitions each; import-only baselines
`import Lc.LiCriterion.XiOrderBridge` = 3.2 s (14.9 s cold) and `import LiLadder` = 3.2 s.

| file | N | wall (warm) | over import baseline | per rung |
|---|---:|---:|---:|---:|
| ladder (per-rung theorems) | 100 | 2.8 s | ≈ 0 | — |
| | 200 | 3.8 s | 0.6 s | 3 ms |
| | 500 | 3.7–4.2 s | 0.5–1.0 s | 1–2 ms |
| | 1 000 | 5.6–5.7 s | 2.4 s | **2.4 ms** |
| bundle (one list + one hypothesis) | 20 | 3.3 s | ≈ 0 | — |
| | 100 | 2.7–3.2 s | ≈ 0 | — |
| | 200 | 2.8–3.5 s | ≈ 0 | — |
| | 500 | 3.6–3.7 s | 0.4 s | 0.8 ms |
| | 1 000 | 4.0 s | 0.8 s | 0.8 ms |

* *Literals.* The emitter rounds each lower bound DOWN to 12 significant decimals, so the
  literal is a 12-digit numerator over a power of ten regardless of n (rung 0:
  `230957089661/10000000000000`; rung 999: `232605316168/100000000`). `norm_num` on
  `(0:ℝ) ≤ a/b` is O(1) per rung — the ladder's kernel cost is **linear in N with a ~2 ms constant**
  and does not grow with the size of λ_n. (The digit count is a design choice: the enclosure has
  ≥ 40 bits at the emitter's precision, and rounding down keeps the bound rigorous.)
* *Bundle.* `liLowerBounds_length` (`rfl`) and `liLowerBounds_pos` (`decide` over
  `List (ℤ × ℕ)`) recurse ~N deep in the elaborator: N = 500 hit the default `maxRecDepth 512`,
  fixed by an emitted `set_option maxRecDepth (8N + 512) in`. The kernel `decide` over 1000
  integer pairs is 0.8 s. `ℤ × ℕ` pairs rather than `ℚ` literals on purpose: `Rat` normalisation
  does not kernel-reduce well (the P-vs-NP ladder's footgun), integer comparisons do.
* *Elaboration vs kernel.* Not separated here (wall clock only); at 2 ms/rung the split is moot.

**Verdict.** n = 10³ in-kernel is a 6-second file. The whole 10³ ladder — enclose, emit, check —
is under ten seconds on one core. Largest N certified in-kernel in this milestone: **1000** (trial
files, measured, not committed); the committed ladder stays at 20 by design.

## 3. The hypothesis-aggregation problem, and the packaging discipline

A 1000-rung ladder in the per-rung form is 1000 theorems with 1000 *independent* hypotheses
`hlo₀ … hlo₉₉₉`; whoever consumes the prefix (e.g. `li_rh_iff_tail`) must supply all of them,
one Arb fact each. That does not scale and it obscures the trust boundary (a thousand seams
instead of one).

**Discipline (prototyped on the committed 20 rungs — `lean/LiPositivityBundle.lean`, generated
with `LiPositivity.lean` by the same `generate.py` run and drift-checked with it):**

```lean
def liLowerBounds : List (ℤ × ℕ) := [ (230957089661, 10000000000000), … ]   -- SAME literals as li_rung_i
theorem liLowerBounds_pos : liLowerBounds.all (fun p => decide (0 < p.1)) = true := by decide
def LiBundleHyp : Prop :=                      -- THE one Arb trust seam for the whole prefix
  ∀ i (h : i < liLowerBounds.length), liLo liLowerBounds[i] ≤ (taylorCoeff riemannXi i).re
theorem li_prefix_of_bundle (hlo : LiBundleHyp) : ∀ n, n < 20 → 0 ≤ (taylorCoeff riemannXi n).re
theorem li_rh_iff_tail_of_bundle (hlo : LiBundleHyp) :
    RiemannHypothesis ↔ ∀ n, 20 ≤ n → 0 ≤ (taylorCoeff riemannXi n).re
```

* One data literal (the certificate), one kernel `decide` (the certificate is well-formed:
  every numerator positive), one hypothesis (the trust seam), one theorem (the prefix), and the
  tail reduction stated once from that one hypothesis.
* The bundle carries *the same* numbers as the per-rung file — `generate.py --check` verifies
  both faces byte-for-byte against regeneration — so the per-rung theorems remain as the
  human-readable, one-rung-at-a-time face, and the bundle is what a consumer instantiates.
* Alternatives considered: a `Fin N → ℚ` function (needs `Rat` kernel evaluation — rejected, see
  above); a `structure` with N fields (no `decide`, no scaling); `native_decide` (adds the
  `Lean.ofReduceBool` axiom — rejected, the guard must stay at `[propext, Classical.choice,
  Quot.sound]`).
* Guarded in `AxiomGuardLiPositivity.lean`: `liLowerBounds_pos`, `li_prefix_of_bundle`,
  `li_rh_iff_tail_of_bundle`.

## 4. Why the tail cannot be bought (the roadmap's own words, with the twin's numbers)

The roadmap's "Why finite fails, quantitatively" paragraph (§3) is the operative statement; this
milestone adds a measured miniature of it and changes none of it.

* **The BL identity holds for arbitrary symmetric multisets.** The finite core
  `bl_finite_multiset` (RvMBlFiniteMultiset.lean, B7-i): for a finite symmetric S avoiding 0, 1,
  all Li-type sums are ≥ 0 iff every point has Re = ½. A finite prefix of positive sums carries
  zero zeta-specific content — any symmetric multiset with its off-line points high enough
  produces it.
* **Freitas-type delocalization: the first negativity is pushable arbitrarily far.** Measured on
  the negative-control family `S = {¾ ± it, ¼ ± it}` (exact rationals, `generate_negative_control.py`):

  | height t | first n with Li-type sum < 0 |
  |---:|---:|
  | 1 | 6 |
  | 2 | 12 |
  | 5 | 31 |
  | 10 | 62 |
  | 20 | 125 |
  | 50 | 313 |

  First negativity ≈ 6.25·t — linear in the height of the off-line quadruple. An N-rung certified
  prefix is silent about any off-line quadruple of this shape above height ≈ N/6, and zeros are
  already verified on the line to height 3·10¹². A 10³ or 10⁴ ladder therefore cannot see anything
  that on-line verification has not already settled — this is what "morally forced by on-line
  verification" means, in numbers.
* **Window certification cost is doubly exponential in support.** Two claims of Zhu 2608.24827,
  which that paper separates and this note previously fused:
  * *Proved* (Thm 1.4): the certificate size needed to certify positivity on `supp f ⊆ [−L, L]`
    grows doubly exponentially in `L`. This is a theorem, and it is the one that closes the route.
  * *Measured, not proved* (Rmk 1.5): the margin `−ln λ*(L)` of the optimal window form is
    observed to collapse at the Landau–Widom rate. The constant `2π² ≈ 19.74` is a **fit**, and
    the fit is to a measurement of `20.13 ± 0.10` — close, but a numerical observation with an
    unexplained residual, not a derived constant.

  Both concern `λ*(L)`, the least eigenvalue of the *optimal* window form, not `λ_min(L)` of any
  particular Gram block. The B3/B9 Weil–Gram route buys support only at the Thm 1.4 price; "grow
  L" has no known method (roadmap B9).
* **The totally-positive tail budget buys ~1 bit per doubling of certified height** (Groskin
  2607.02828) — the height-side analogue: exponentially more verification for each additional bit
  of tail control.
* **Route-unique value is falsifiability, one-directional.** `li_neg_refutes_rh` (a certified
  negative rung refutes RH) is the payload; no number of positive rungs is a payload. The
  negative control is what makes that face credible.

## 5. The negative-control twin (`lean/LiNegativeControl.lean`)

An instrument that can only say "positive" is not an instrument. The twin is the same certificate
shape (rung index + rational bound) on a synthetic symmetric multiset with ONE off-line quadruple

    S₀ = {3/4 + i, 3/4 − i, 1/4 + i, 1/4 − i}     (closed under ρ ↦ 1 − conj ρ; avoids 0, 1)

for which `w(ρ) = (1 − 1/ρ)⁻¹` is Gaussian-rational, `(13 ∓ 16i)/17` (|w| > 1) and
`(13 ∓ 16i)/25` (|w| < 1), so every Li-type sum is an exact rational:

| n | Re ∑ (1 − w^n) | |
|---:|---:|---|
| 1 | 608/425 ≈ 1.43 | silent |
| 2 | ≈ 4.88 | silent |
| 3 | ≈ 8.17 | silent |
| 4 | ≈ 8.81 | silent |
| 5 | ≈ 5.60 | silent |
| **6** | **−309804177801344/5892961181640625 ≈ −0.0526** | **FIRES** |
| 7 | ≈ −4.22 | |

In Lean, everything is decided in-kernel with `simp`/`norm_num` on exact rationals — **no
hypothesis at all** (the finite rational multiset needs no Arb):

* `negctrl_rung_1_nonneg … negctrl_rung_5_nonneg` — the silent stretch (delocalization in
  miniature);
* `negctrl_fires_value : liTypeSum S₀ 6 = −309804177801344/5892961181640625` and
  `negctrl_fires : liTypeSum S₀ 6 < 0` — the instrument fires;
* `negctrl_neg_refutes_online` — the exact structural twin of `li_neg_refutes_rh`: a certified
  negative upper bound on any rung refutes "every point on the line", through
  `bl_finite_multiset`'s forward direction;
* `negctrl_detects_offline : ¬ ∀ ρ ∈ S₀, ρ.re = 1/2` — the twin instantiated with the in-kernel
  value: the `hhi` that is a trust seam on the real ladder is *discharged* here.

Guarded in `AxiomGuardLiPositivity.lean` (expected `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`). Zero zeta content, zero RH content: S₀ is not the zero set of anything. What it
certifies is that the positivity instrument is not tautologically positive and that the
refutation face has the right shape — same certificate, opposite sign, proof goes through.

## 6. Findings that changed code

* **`sp.nsimplify` in the rung certificate** (`emit_li_positivity.li_rung_certificate`) ran every
  certified `Fraction` through mpmath's `identify` closed-form search at 10⁻¹⁵ tolerance. On the
  12-digit literals of rungs n ≳ 150 it returned radicals (`60·2^{39/245}·3^{6/35}·…`, a loud
  `TypeError`); in principle it could return a nearby *different* rational silently. Fractions,
  ints and Rationals now convert verbatim; floats are refused. The committed 20 rungs regenerate
  byte-identically before and after. (A latent seam found only by pushing N.)
* Bundle `decide`/`rfl` recursion budget (§2).
* `prec_bits_for(N) = max(192, 2N + 128)` replaces the flat 192 bits for N > 32.

## 7. Open items (not started, deliberately)

* Independent numeric anchor for rungs n ≥ 3 (BL sum over verified zeros with a rigorous tail
  bound) — a sanity check, not a rigor input.
* Committing a longer ladder: pointless by §4 unless something downstream (B4 defect counting on
  ANDÚRIL data) consumes it; if it does, commit the *bundle* face only and keep the per-rung face
  at 20.
* The per-rung ↔ bundle equivalence as a Lean theorem (`li_rung_i` from `li_prefix_of_bundle`
  and back) — trivial, unneeded until a consumer exists.
* B2 (λ₁ hypothesis-free in-kernel) is a different kind of object (a Taylor coefficient of log ξ,
  not a function value) and is not touched by any of this.

## Reproduce

```
cd telperion
python examples/li_positivity/generate.py --check                 # 20 rungs + bundle, byte-for-byte
python examples/li_positivity/generate_negative_control.py --check
python examples/li_positivity/bench_li_ladder.py out.jsonl 20,50,100,200,500,1000
python examples/li_positivity/generate.py --trial 1000            # LiPositivityTrial_n1000.lean (+ bundle), ignored by git
cd examples/li_positivity/lean && lake env lean LiPositivityTrial_n1000.lean
```
