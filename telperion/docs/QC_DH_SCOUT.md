# QC-A3 — Davenport–Heilbronn driver spike (dh-scout)

**PROGRAM MIRRORMERE, Wave A.** Feasibility spike for a rigorous
Davenport–Heilbronn (DH) evaluation driver — the control object with off-line
zeros that the falsification zoo (B1) needs.  Python + ctypes over the bundled
libflint; no Lean.  `conjecture1_proved = False`.

**Verdict: GO.** The shim evaluates D(s) in rigorous ball arithmetic, reproduces
the published on-line and off-line zeros, and certifies the crown off-line zero
by an argument-principle winding count on a rational-cornered rectangle
strictly off Re = 1/2. Per-eval cost is sub-ms to a few ms; a fully-certified
T ≤ 1000 zero inventory is ~10 minutes of single-thread work.

Deliverable module: `telperion/src/telperion/arb_dh.py`.

> **Correction, 2026-10-14 — please read this before the rest.**
>
> When this scout was written, the winding count it describes in §4 was called
> rigorous. It was not. The routine (`arb_dh.winding_number` at the time, now
> renamed `winding_number_sampled_heuristic`) evaluated D in Arb balls at the
> boundary *nodes* only and added up the quadrant steps between neighbouring
> nodes. Every ball value was rigorous, but nothing bounded how far the
> argument of D could turn *between* two nodes. Two zeros sitting close to an
> edge, between nodes, can add a full turn without changing a single sampled
> quadrant. An independent audit
> (`~/e9-research/review_telperion_winding/REVIEW_telperion_winding_2026-10-14.md`)
> built exactly that: a zero pair at x = 1/7, about 1e-9 above the bottom edge
> of the unit square, which the node count reports as 1 instead of 2 at every
> density. Doubling the density does not help, because 1/7 is never a node.
> The sentence in §4 that "a wrong evaluation yields an abort or a mismatched
> count, never a false certified count" was therefore false.
>
> Since 2026-10-14 every count uses the segment-enclosure method in
> `telperion/src/telperion/arb_winding.py` (`arb_dh.winding_number_rigorous`).
> It encloses D and D' on every boundary *segment*, so the argument change
> along the whole segment is bounded, and it bisects or refuses when it cannot
> certify a segment. All the boxes in this scout were re-run with it, at
> prec 96 and again at prec 144 with a different subdivision, and every
> integer stood: the three on-line boxes of §3(d) give 1, the crown box of §4
> gives 1, and both negative controls give 0. So the facts below hold; it is
> only the method description that was wrong, and it is corrected in place.
>
> The audit also found that the T ≤ 300 inventory built on this scout
> (`examples/quasicrystal/zoo_data/dh_zeros.json`) had missed an off-line zero
> ρ ≈ 0.8695305796 + 240.4046723514i, because its off-line list was seeded from the
> literature and the promised off-line scan was never written. The re-issued
> inventory has that scan, lists 5 off-line zeros, and proves itself complete
> to height 300 (214 = 204 + 2·5). See `examples/quasicrystal/dh_inventory.py`.

---

## 1. The function and its exact constant

The Davenport–Heilbronn function is the period-5 Dirichlet series

    D(s) = sum_{n>=1} c(n) n^{-s},   c = [1, kappa, -kappa, -1, 0]  (period 5)

with the exact real algebraic constant

    kappa = (sqrt(10 - 2 sqrt5) - 2) / (sqrt5 - 1)
          = (sqrt(40 + 8 sqrt5) - 2 sqrt5 - 2) / 4        (rationalized)
          = 0.284079043840412...

**Normalization cross-checked against three sources (charter required ≥2):**

1. **Franca–LeClair**, arXiv:1407.4358, eq. (245)–(247): defines
   `D = (1-i kappa)/2 · L(s,chi_{5,2}) + (1+i kappa)/2 · L(s,chi*_{5,2})` with
   `chi_{5,2} = [1, i, -i, -1, 0]` and **verbatim**
   `kappa = (sqrt(10 - 2 sqrt5) - 2)/(sqrt5 - 1)`.  Expanding the two L-series
   collapses the complex characters to the real coefficients `c` above.
2. **Ferry–Isaila–Pantazi** "On Davenport and Heilbronn-Type of Functions",
   arXiv:1602.06328, §2: the same series `1 + tanθ·2^{-s} - tanθ·3^{-s} -
   4^{-s} + ...` with `tan²θ = (2·sqrt(1-1/sqrt5))/(...)`, numerically
   `tanθ = 0.284079...` — identical constant.
3. **Balanzario–Sánchez-Ortiz**, *Zeros of the Davenport–Heilbronn
   Counterexample*, Math. Comp. **76** (2007) 2045–2056 (ref [7] of the Ferry
   paper; the source of the computed off-line zeros) — same construction,
   deformation of an L-series with known zeros into the DH series.

The rationalized surd form `(sqrt(40 + 8 sqrt5) - 2 sqrt5 - 2)/4` uses only
nested **integer** radicands, so `kappa` is enclosed rigorously from
`arb_sqrt_ui(5)` and `arb_sqrt(10 - 2 sqrt5)` — **no float constant enters** the
ball (`dh_kappa_interval` / `_build_kappa_arb`).  Enclosure width at prec 128 is
~3.5e-38.

**Functional equation** (Franca–LeClair eq. 248):
`xi(s) = (pi/5)^{-(1+s)/2} Gamma((1+s)/2) D(s)` satisfies `xi(s) = xi(1-s)`; the
odd character gives the odd-gamma factor.  D has NO Euler product, which is why
the FE alone does not force zeros onto Re = 1/2.

---

## 2. Evaluation route

Collapsing the period-5 series onto four Hurwitz zetas,
`sum_{n ≡ r (5)} n^{-s} = 5^{-s} zeta(s, r/5)`:

    D(s) = 5^{-s} [ zeta(s,1/5) + kappa zeta(s,2/5)
                    - kappa zeta(s,3/5) - zeta(s,4/5) ]

Each `zeta(s, r/5)` is a rigorous `acb` ball via FLINT
`acb_dirichlet_hurwitz` (verified present in the bundled
`libflint.18.0.dylib`); `5^{-s}` is an exact `acb_pow`; the arb `kappa` ball
multiplies in via `acb_mul_arb`.  Endpoints are extracted dyadically with
`arb_get_interval_fmpz_2exp` — no decimal parsing — mirroring `arb_platt`.

**API** (exact dyadic Fractions, outward-rounded):

    dh_eval(s_re, s_im, prec=128) -> (re_lo, re_hi, im_lo, im_hi)
    dh_kappa_interval(prec=128)  -> (lo, hi)
    winding_number_rigorous(re0, re1, im0, im1, prec, init_per_side) -> int
    certify_offline_zero(re0, re1, im0, im1, prec, n_per_side) -> dict
    winding_number_sampled_heuristic(re0, re1, im0, im1, prec, n_per_side) -> int   # NOT rigorous
    winding_number(...)   # deprecated alias: warns, delegates to winding_number_rigorous

---

## 3. Sanity battery (all PASS)

**(a) Real on the real axis.** `D(x)` for real `x` returns `Im ∈ [0, 0]`
exactly (coefficients are real ⇒ D(s̄) = conj D(s)).  Verified at x = 2, 3, 1/2.

**(b) Conjugate symmetry in balls.** At s = 4/5 + 30i vs 4/5 − 30i: Re boxes
identical, Im boxes exact negatives. PASS.

**(c) Cross-check vs mpmath.** Independent mpmath Hurwitz evaluation (50 dps)
agrees with every shim box to all printed digits at s = 3, 1/2+20i,
4/5 + 85.7i.

**(d) On-line zeros reproduced.** Three critical-line zeros certified by a
winding-1 box straddling Re = 1/2 (first found with the node-sampling count;
re-certified with the segment method on 2026-10-14, winding 1 each):

| Im (approx) | box Re      | box Im             | winding |
|-------------|-------------|--------------------|---------|
| 12.133545   | [0.47,0.53] | [12.103, 12.164]   | 1       |
| 17.130239   | [0.47,0.53] | [17.100, 17.161]   | 1       |
| 22.159708   | [0.47,0.53] | [22.129, 22.190]   | 1       |

---

## 4. CROWN DELIVERABLE — certified off-line zero

Published off-line zero (Franca–LeClair Table IX, matching Balanzario–
Sánchez-Ortiz): **ρ\* = 0.8085171825 + i·85.6993484854**.

`certify_offline_zero` performs an argument-principle winding count.  As first
written it walked the rectangle boundary through `4·n_per_side` rational nodes,
enclosed D in a ball at each, classified each value-box into a strict quadrant,
and summed signed quadrant advances.  That is a **heuristic** count (see the
correction at the top): the ball values are rigorous, but the path between
nodes is not controlled.  Since 2026-10-14 it uses the segment-enclosure
method of `arb_winding` instead: on each boundary segment D and D' are enclosed
over an Arb ball covering the segment, the image is shown to stay in a disc
that avoids 0, and the argument change along that segment is then exact up to
the endpoint balls.  A returned integer from that method is an Arb-trust-class
zero count for the open rectangle.

**Certified box (exact rationals), strictly right of Re = 1/2:**

    Re ∈ [79/100, 83/100]      (= [0.79, 0.83],  entirely > 1/2)
    Im ∈ [8568/100, 8572/100]  (= [85.68, 85.72])
    winding number = 1   ⇒   exactly ONE zero of D in the open box, off-line.

**Re-check (charter requirement):** the original run was repeated at **doubled
precision and doubled boundary density** (prec = 440, n_per_side = 48) → winding
= 1 again.  That recheck did not make the count rigorous, since it shares the
node-sampling flaw.  **Re-certified 2026-10-14** with the segment method: winding
1 at prec 96 (32 segments) and at prec 144 (52 segments).

**Negative controls (PASS):**
- Box left of ρ\* with no zero, Re ∈ [0.60, 0.70], Im ∈ [85.68, 85.72] →
  winding = 0.
- Empty region far from any zero, Re ∈ [1.5, 1.6], Im ∈ [20, 21] → winding = 0.

**Trust label.** With the segment method this is **Arb-interval
(argument-principle) evidence**, the same trust class as `arb_platt` /
`arb_enclosure` — an interval computation, **NOT a Lean-kernel proof**.  The
original text here said "a wrong evaluation yields an abort or a mismatched
count, never a false certified count"; for the node-sampling count that was
false (correction at the top).  `conjecture1_proved = False`.

---

## 5. Per-eval cost and T ≤ 1000 inventory estimate

Single `dh_eval` (one D(s) ball), ms:

| height | prec 64 | prec 128 | prec 300 |
|--------|---------|----------|----------|
| 10     | ~0.3–0.8| ~0.3     | ~0.6     |
| 100    | ~0.3    | ~0.4     | ~2.2     |
| 1000   | ~0.9    | ~2.2     | ~4.2     |

(Cost is dominated by the four Hurwitz evaluations; grows with both precision
and height, as expected.)

**T ≤ 1000 certified inventory estimate** (single thread):
- DH zeros to T = 1000: ~1060 (density `(T/2π)·log(5T/2π)`).
- Locate grid (spacing ≈ mean gap ≈ 0.8): ~1250 evals ≈ **2.5 s**.
- Certify each zero by a winding box (~300 evals at prec 128): ~640 s ≈
  **~11 min** total.
- Comfortably parallelizable across bands; the B1 zoo can afford full
  certification, not just location.

---

## 6. Gotchas for B1

- **Two normalizations coexist in the literature.** The complex-character form
  `(1∓iκ)/2 L(s,χ) + …` (Franca–LeClair) and the real-coefficient form
  `[1, κ, −κ, −1, 0]` (Ferry; this shim) are the **same function**; don't
  double-count κ or drop the `5^{-s}` prefactor when translating.  The real
  form is used here because it maps cleanly to four Hurwitz anchors and makes
  the "real on the real axis" sanity check exact.
- **The Ferry paper is skeptical** — it argues some *published* off-line points
  are approximation artifacts.  That does NOT affect ρ\* = 0.8085+85.699i, which
  this shim certifies by winding number (segment method since 2026-10-14),
  independent of any published numeric.  Trust the winding integer, not the
  literature decimals — and do not trust a literature *list* to be complete
  either: the inventory seeded from it missed the zero ρ ≈ 0.86953 + 240.40467i.
- **No Hurwitz precomputation API needed.** `acb_dirichlet_hurwitz` is a direct
  per-call evaluation; there is no shared-context/precompute step to manage
  (unlike Platt multieval).  Each D(s) is four independent Hurwitz calls.
- **Winding refusals are features.** If a boundary segment cannot be certified
  zero-free within the bisection depth (a zero may sit on or very near the
  contour), `winding_number_rigorous` raises rather than guessing; move the box
  edge.  (The original node-sampling routine also raised on a straddling or
  diagonal step, but it could return a wrong integer WITHOUT raising, so its
  aborts were not a guarantee.)
- **acb/arb struct sizes** (96 / 48 bytes, flint 18.x, 64-bit) are hard-coded to
  match `arb_platt`; if the bundled libflint is ever bumped, re-verify the
  layout before trusting endpoint extraction.
- **Loader reuse:** `_find_libflint` is copied verbatim from `arb_platt`; the
  bundled lib is `flint/.dylibs/libflint.18.0.dylib`.

---

## 7. GO/NO-GO

**GO for B1 (qc-zoo).**  The rigorous DH evaluator exists, is cross-validated,
certifies both on-line and off-line zeros, and prices a full T ≤ 1000 inventory
at ~10 minutes.  The certified off-line zero box (§4) is the control the
falsification matrix needs: any candidate log-lattice FQ axiom that D's zero
comb satisfies is dead, because that comb provably contains an off-line point
(Arb trust class; re-certified with the segment method on 2026-10-14).
