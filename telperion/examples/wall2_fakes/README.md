# WALL-2 calibration fakes: Arb certificates for EP5, EPQ2 and DH

conjecture1_proved = False. This directory is not progress on the Riemann Hypothesis. It certifies facts about
functions that are known to violate RH, so that we can check that Telperion's RH-type instruments notice.

## Why these functions

WALL-2's "calibration polygon" is a set of fakes. Each one has some, but not all, of the Riemann zeta function's
ingredients, and each one has zeros off the critical line. Three of them are classical Dirichlet series with a
Riemann-type functional equation:

- **EP5** = ζ L(χ₋₂₀) + L(χ₋₄) L(χ₅). This is the Epstein zeta function of m² + 5n².
- **EPQ2** = ζ L(χ₋₂₀) − L(χ₋₄) L(χ₅). This is the Epstein zeta function of 2m² + 2mn + 3n².
- **DH** is the Davenport–Heilbronn function. Its coefficients are periodic mod 5, with values 1, κ, −κ, −1, 0.

None of the three has an Euler product, and all three have off-line zeros. WALL-1 track C counted those zeros in
double precision. This directory upgrades the counts to interval-arithmetic certificates, and then runs the fakes
through the emitters that make RH-shaped claims.

## What was certified, and how far to trust it

**Status: ARB (bb-reviewed).** The zero boxes, counts, knife-edge certificate and negative Li coefficients were
reviewed by the auditor bb, who judged the core SOUND (`~/e9-research/review_telperion_winding/`,
`~/e9-research/review_wall2_T/REVIEW_wall2_T_2026-10-14.md`). That review covers commits up to d75bf8a86; the
later s = 1 pole guard was not part of it. Each sidecar carries a `status` field that says so.

Everything here is **trust class arb**: python-flint ball arithmetic. It is rigorous if Arb and our code are right,
but it is not a Lean kernel theorem. The one exception is `lean/Ramification.lean`, which the kernel checks with
`decide` (see the last section).

The engine is `telperion.arb_fakes`. It evaluates each fake by collapsing every L-function onto Hurwitz zetas, as
`arb_dh` does for DH. It counts zeros with `rigorous_winding`. That routine encloses the function on every boundary
*segment*, using the centred form f(m) ± r·sup|f′| with sup|f′| from an Arb jet on a ball that covers the segment.
It accepts a segment only if the segment's whole image lies in a disc |w − c| ≤ |c|/2, so the argument change
across that segment is pinned down exactly.

That segment rule is the point. The older `arb_dh.winding_number` looks only at the nodes, and it can be fooled;
`scripts/winding_soundness_demo.py` shows how (more on this below).

1. **Named off-line zeros** (`certs/offline_zero_boxes.cert.json`). The four EP5 and EPQ2 zeros named in the WALL-2
   plan, and the DH zero near 0.8085 + 85.70i, each have winding exactly 1 in a 0.02 × 0.02 box. The check was
   repeated at 1.5× precision with a different subdivision, and both runs agree.
2. **Off-line zero counts** (`certs/*_offline_counts_T*.cert.json`). The count covers (σ₀, σ_R) × (1/20, T), split
   into strips of height 10. The right edge σ_R is a place where a dominant-term bound certifies that the function
   has no zeros for Re s ≥ σ_R: 8/5 for EP5 and DH, 5/2 for EPQ2, because EPQ2 has zeros with σ > 2. So each count is
   the number of *all* zeros with Re s > σ₀ in that height range. Every strip matches track C's list. For EP5 at
   T = 200 the counts are 31/22/15 at σ₀ = 0.6/0.7/0.8. That includes the knife-edge zero at 0.79977772 + 61.14026i,
   which correctly falls outside the σ₀ = 0.8 box; the contour there needed segments as short as 1.5e-4.
   A separate certificate (`certs/EP5_knife_edge.cert.json`) puts that zero, with winding 1, in
   [0.7995, 0.79995] × [61.139, 61.1415]. That box lies strictly left of σ = 0.8, with a certified gap of 5e-5,
   so the σ₀ = 0.8 cut is kept.
3. **Li coefficients** (`certs/li_fakes_summary.cert.json`). `enclose_li_fake` builds each completed function from
   its functional-equation data, written out in the module docstring and self-checked to 1e-35. EPQ2's λ_n is
   certified negative from n = 246, and EP5's from n = 5713. DH's and ζ's are positive for every n ≤ 3000.
   Track H finds DH's first negative at n = 328997, by two independent float methods. That is not Arb-checked:
   at N of about 3.3e5 the series route would need roughly 3.3e5-bit precision.
4. **Negative controls** (`certs/negative_controls.json`). Each fake was offered to the RH-type emitters'
   certification layer. The two function-level emitters, winding_box_zero and grid_modulus_nonvanishing,
   rejected every fake. The others are not function-level tests: they take numbers or counts handed to them, so
   their refusals test only their own bookkeeping. grid_modulus_nonvanishing is a numeric (mpmath) kind, not an
   Arb one. li_rung_certificate accepted a fake's lower bound. What it then emits is a ζ theorem whose
   hypothesis is false, so the theorem is vacuous but not "true of the fake". That is a provenance gap.
   Some finite instruments cannot tell the fakes from ζ at all: finite Bagchi recurrence, and on-line zero
   counts. Finite Li positivity holds for EP5 up to n = 5712 and for DH up to n = 3000. That is expected, and it is
   recorded.

## Exactly what `rigorous_winding` / `count_offline` certify

**The theorem used.** This is the argument principle. Suppose f is holomorphic on a neighbourhood of a closed
rectangle R, has no poles in R, and has no zeros on ∂R. Then the number of zeros in R, counted with multiplicity,
is (1/2π) Δ_∂R arg f. The fakes' only pole is s = 1, which is on the real axis, and every box here has Im s ≥ 1/20.

**What is certified on each segment.** Each edge of R starts as 8 equal axis-parallel segments with rational
endpoints. Take a segment [p, q] with midpoint m and half-length r.

1. B is an Arb ball that contains the whole segment: centre m, radius r(1 + 2⁻⁴⁰) in the moving coordinate.
2. D is an Arb upper bound for |f′| over all of B, from an `acb_series` jet (f, f′) evaluated on the ball B.
   Arb's guarantee is that the ball result encloses f′(z) for every z in B, not just at its centre.
3. c is the exact rational centre of the Arb box for f(m). Let ρ = r·D + (half-width of Re f(m)) + (half-width of
   Im f(m)).
4. By the mean value inequality, |f(z) − f(m)| ≤ |z − m| · sup|f′| ≤ r·D. So |f(z) − c| ≤ ρ for every z on the
   segment.
5. The segment is accepted only if 4ρ² < |c|², checked in exact Fractions. Then, on the WHOLE segment,
   |f| ≥ |c| − ρ > |c|/2 > 0, which certifies the edge zero-free with an explicit lower bound. Also, f/c stays in the
   disc |w − 1| ≤ 1/2, where the principal Arg is continuous and lies in [−π/6, π/6]. So the continuous change of
   arg f along the segment is exactly Arg(f(q)/c) − Arg(f(p)/c), and both terms are computed as Arb balls.

**How segment lengths are chosen.** A segment that fails step 5 is bisected, adaptively. After 40 bisections, a
length of edge/(8·2⁴⁰), the routine REFUSES rather than guess.

**How the integer is read off.** The Arb sum of all segment changes is divided by 2π. The result is accepted only
if the whole ball lies within 1/4 of a single integer, again checked in exact Fractions. `certify_zero_box`
repeats the count at 1.5× precision with 13 initial pieces per edge, and both runs must agree.

**What is trusted, not checked.** Arb's ball semantics for `acb_series.zeta(s, a)` with ball inputs, the
python-flint bindings, and the outward conversion of arb balls to Fractions.

## The soundness finding

`arb_dh.winding_number` and `certify_offline_zero` decide the winding from the quadrants of the value boxes at
boundary nodes, and the default `winding_box_zero` backend is the same routine. A full turn of the argument
*between* two nodes is invisible to that test.

The demo uses f(z) = (z − a)(z − b), with both zeros inside the unit box, 1e-4 above the bottom edge, and between
the same pair of nodes. The true count is 2. The node routine returns 1, and still returns 1 at doubled density.
`winding_box_zero_certificate` therefore issues a trust-class-arb sidecar that says "exactly 1 zero", which is false.

The missing step is precise. The node routine has no bound on how far arg f moves *between* consecutive nodes,
and no lower bound on |f| along a segment. It only knows the quadrant at each node. The function is contrived,
but the algorithm is generic. ζ's main RH-in-box driver is not affected, because it uses
`segment_winding_certificate` on segment enclosures. Whether earlier sidecars came from the node backend has not
been audited here.

## The kernel-checked file

`lean/Ramification.lean` is core Lean, with no Mathlib. For Q(i), Q(√5), Q(∛2) and Q(ζ₅), each theorem covers
an explicit list of rows (p, factors). The generator lists the primes p < 30. For each listed row, `decide`
checks four things:

- that the product of factor^e equals the generator mod p, as coefficient lists;
- that each factor passes a root test: no root mod p for degrees 2 and 3, and for the quartic no root and no
  quadratic divisor either;
- that Σ e·deg = n;
- that (some e > 1) holds exactly when p | disc.

Lean does NOT check that the listed p are prime, and the root tests mean "irreducible" only when p is prime. It
also does not check that the list contains every prime below 30, or that the factors are distinct. Those facts
come from the sympy generator. Dedekind–Kummer and disc = d_K are cited, not checked. A negative-control theorem confirms that a false row is
rejected.

To check it: `lean lean/Ramification.lean` (about 6 s).

## Reproducing

The scripts expect the WALL-2 layout under `~/rh-team/wall2/T` and track C's zero lists in
`~/rh-team/wall1/C/out`. Run them with a venv that has this telperion plus python-flint:

```sh
python scripts/cert_zero_boxes.py
python scripts/cert_counts.py EP5 200
python scripts/li_ramp.py 3000 3600
python scripts/negative_controls.py
python scripts/winding_soundness_demo.py
python scripts/gen_ramification_lean.py
```
