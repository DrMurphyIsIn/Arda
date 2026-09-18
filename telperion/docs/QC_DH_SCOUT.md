# QC-A3 — Davenport–Heilbronn driver spike (dh-scout)

**PROGRAM MIRRORMERE, Wave A.** Feasibility spike for a rigorous
Davenport–Heilbronn (DH) evaluation driver — the control object with off-line
zeros that the falsification zoo (B1) needs.  Python + ctypes over the bundled
libflint; no Lean.  `conjecture1_proved = False`.

**Verdict: GO.** The shim evaluates D(s) in rigorous ball arithmetic, reproduces
the published on-line and off-line zeros, and certifies the crown off-line zero
by a rigorous argument-principle winding count on a rational-cornered rectangle
strictly off Re = 1/2. Per-eval cost is sub-ms to a few ms; a fully-certified
T ≤ 1000 zero inventory is ~10 minutes of single-thread work.

Deliverable module: `telperion/src/telperion/arb_dh.py`.

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
    winding_number(re0, re1, im0, im1, prec, n_per_side) -> int
    certify_offline_zero(re0, re1, im0, im1, prec, n_per_side) -> dict

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
winding-1 box straddling Re = 1/2:

| Im (approx) | box Re      | box Im             | winding |
|-------------|-------------|--------------------|---------|
| 12.133545   | [0.47,0.53] | [12.103, 12.164]   | 1       |
| 17.130239   | [0.47,0.53] | [17.100, 17.161]   | 1       |
| 22.159708   | [0.47,0.53] | [22.129, 22.190]   | 1       |

---

## 4. CROWN DELIVERABLE — certified off-line zero

Published off-line zero (Franca–LeClair Table IX, matching Balanzario–
Sánchez-Ortiz): **ρ\* = 0.8085171825 + i·85.6993484854**.

`certify_offline_zero` performs a rigorous argument-principle winding count: it
walks the rectangle boundary through `4·n_per_side` rational nodes, encloses D
in a ball at each, classifies each value-box into a strict quadrant (aborting if
any box straddles an axis, i.e. sign-ambiguous), and sums signed quadrant
advances (aborting on any diagonal / ±π-ambiguous jump).  A returned integer is
therefore a **rigorous** zero count for the open rectangle.

**Certified box (exact rationals), strictly right of Re = 1/2:**

    Re ∈ [79/100, 83/100]      (= [0.79, 0.83],  entirely > 1/2)
    Im ∈ [8568/100, 8572/100]  (= [85.68, 85.72])
    winding number = 1   ⇒   exactly ONE zero of D in the open box, off-line.

**Independent re-check (charter requirement):** re-run at **doubled precision
and doubled boundary density** (prec = 440, n_per_side = 48) → winding = 1
again.

**Negative controls (PASS):**
- Box left of ρ\* with no zero, Re ∈ [0.60, 0.70], Im ∈ [85.68, 85.72] →
  winding = 0.
- Empty region far from any zero, Re ∈ [1.5, 1.6], Im ∈ [20, 21] → winding = 0.

**Trust label.** This is **Arb-interval (argument-principle) evidence**, the
same trust class as `arb_platt` / `arb_enclosure` — a rigorous interval
computation, **NOT a Lean-kernel proof**.  A wrong evaluation yields an abort
(refine request) or a mismatched count, never a false certified count.
`conjecture1_proved = False`.

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
  this shim certifies rigorously by winding number, independent of any published
  numeric.  Trust the winding integer, not the literature decimals.
- **No Hurwitz precomputation API needed.** `acb_dirichlet_hurwitz` is a direct
  per-call evaluation; there is no shared-context/precompute step to manage
  (unlike Platt multieval).  Each D(s) is four independent Hurwitz calls.
- **Winding aborts are features.** If a value box straddles an axis (a zero may
  sit on the contour) or a step jumps diagonally, `winding_number` raises with a
  "raise n_per_side/prec" message rather than guessing — the count is only
  emitted when every step is rigorous.  For B1, retry with `n_per_side *= 2`.
- **acb/arb struct sizes** (96 / 48 bytes, flint 18.x, 64-bit) are hard-coded to
  match `arb_platt`; if the bundled libflint is ever bumped, re-verify the
  layout before trusting endpoint extraction.
- **Loader reuse:** `_find_libflint` is copied verbatim from `arb_platt`; the
  bundled lib is `flint/.dylibs/libflint.18.0.dylib`.

---

## 7. GO/NO-GO

**GO for B1 (qc-zoo).**  The rigorous DH driver exists, is cross-validated,
certifies both on-line and off-line zeros, and prices a full T ≤ 1000 inventory
at ~10 minutes.  The certified off-line zero box (§4) is the control the
falsification matrix needs: any candidate log-lattice FQ axiom that D's zero
comb satisfies is dead, because that comb provably contains an off-line point.
