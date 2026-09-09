# Leading the Window to 1,000,000: the Costed Roadmap

**Goal.** All nontrivial zeta zeros to height `T = 10⁶` — ≈ **1,747,000 zeros** — kernel-certified.
**Status.** The unbounded-depth infrastructure now EXISTS (`height_chain` +
`all_nontrivial_zeros_in_segment_on_line`, first exercised at T=4000).  What separates us from 10⁶
is measured compute and one width adjustment — no new mathematics on the primary route, and a
~10× cost cut available on the Turing route.  `conjecture1_proved = False` throughout.

## The measured constants (M3 Ultra, 2026-09-09)
| Quantity | Value | Source |
|---|---|---|
| Per-band Lean elaboration | ~90–110 s at n≈41–46 zeros | T=1000..4000 builds |
| Per-band elaboration scaling | O(n²) in zeros, ×~2 per corner-digit-doubling | scaling law 1 |
| Safe band ceiling at width 5·10⁻⁷ | n ≈ 45 | measured timeout boundary |
| Driver emission | seconds–minutes per band (height-dependent) | T≤4000 runs |
| Close-pair refusal rate | rising with height (~16% at 2–4k), 6× sweep cures all so far | 25/25 lifetime |
| Glue cost | constant per chain link; ≤50-band segments elaborate in seconds | h2000/h4000 |

## The two binding adjustments for 10⁶
1. **Width.** `a ≤ dlvpRateC / log T` requires `a ≤ 4.76·10⁻⁷` at `T = 10⁶` — the current
   `5·10⁻⁷` fails past `T ≈ 5·10⁵`.  A 10⁶ campaign fixes `a = 1/4·10⁶` from the start (same
   digit count as `1/2·10⁶` ⟹ same elaboration ceiling).  Existing certificates to 4000 stay
   valid as-is; the chain composes segments of DIFFERENT widths only through their common
   conclusions, so no re-emission of the low ladder is needed *(each `up-to-A` certificate's
   conclusion is width-free)*.
2. **Band height tracks density.** Zero density at height T is `log(T/2π)/2π` per unit — at
   10⁶ that is ≈1.9/unit ⟹ **~23-height bands** near the top (n ≈ 44).  Total bands to 10⁶:
   ≈ **39,000**; segment files of ≤50 bands ⟹ ≈ 800 segment certificates chained.

## Cost model (primary route, current emitter)
* **Lean:** 1.75M zeros ÷ 43/band × ~100 s ≈ 4.1M core-seconds ≈ **48 core-days** ≈
  **3.5–4 wall-days** on the M3 Ultra (13 effective parallel lanes).
* **Driver:** zeta enclosures at height 10⁶ need Riemann–Siegel-regime evaluation (mpmath
  provides it; per-eval cost grows ~√T); extrapolated **1–2 wall-weeks** single-machine,
  embarrassingly parallel — or ~1 day on a 30-node burst.
* **Mechanics:** 39k modules exceed one lakefile; shard into ~80 lake packages of ~500 modules
  (one per 12.5k-height block), each with its own guard; chain across packages via the
  conclusion-level `height_chain` (already package-agnostic).

**Verdict: 10⁶ is a CAMPAIGN, not a session — roughly 2–3 weeks of continuous compute with
current tools, dominated by driver time.**

## The 10× lever: the Turing route (#342, T2 done, T4 the crux)
Replace per-band winding+`hArb` with line-only sign enclosures + `N(T) = θ(T)/π + 1 + S(T)` +
effective `|S(T)|`.  Eliminates the contour integrals AND the O(n²) box-coordinate blocks —
projected ≤10 s/band elaboration and ~5× driver savings ⟹ **10⁶ in ~2–3 wall-days end-to-end**.
θ is BUILT (kernel-clean, with its Archimedean identification); the Binet chain is one
identity-theorem brick from complex effective ψ; T4 (effective Backlund) is the remaining crux —
our BC/Jensen kit is exactly its toolbox.

## Recommended sequence
1. **Now → T=8000** on the primary route (validates the chain at depth 2; hours).
2. **T4 campaign** (effective `|S(T)| ≤ a log T + b`) — the one hard theorem.
3. **T5 band template swap** → re-rate the ladder at ≤10 s/band.
4. **The 10⁶ run**: sharded packages, burst driver, chain fold.  Every band double-checked
   (winding = sign-count), every segment guard-verified, `hγ` discharged by StripClear.

## Edges-to-limits status (parallel front, updated tonight)
The LEFT edge is now STRUCTURALLY CLOSED with zero Arb inputs
(`left_edge_prime_reflection`: `(log ζ)′(s) = L(Λ)(1−s) − (log Γℝ)′(s) − (log Γℝ)′(1−s)` for
`Re s < 0`, `Im s ≠ 0` — all hypotheses derived).  Remaining for the classical limit: the
horizontal edges as `T → ∞`, requiring the `|ζ′/ζ| = O(log² T)` zero-avoiding-corridor lemma —
the flagged research theorem, next campaign's summit alongside T4.
