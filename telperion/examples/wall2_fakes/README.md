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
3. **Li coefficients** (`certs/li_fakes_summary.cert.json`). `enclose_li_fake` builds each completed function from
   its functional-equation data, written out in the module docstring and self-checked to 1e-35. EPQ2's λ_n is
   certified negative from n = 246, and EP5's from n = 5713. DH's and ζ's are positive for every n ≤ 3000.
4. **Negative controls** (`certs/negative_controls.json`). Each fake was offered to the RH-type emitters'
   certification layer. Every claim that is false for the fake was refused, and no emitter accepted a false
   statement. Several instruments accept statements that are *true* of the fakes, which means they cannot tell the
   fakes apart from ζ: finite Li positivity, finite Bagchi recurrence, and the on-line zero counts. That is expected,
   and it is recorded.

## The soundness finding

`arb_dh.winding_number` and `certify_offline_zero` decide the winding from the quadrants of the value boxes at
boundary nodes, and the default `winding_box_zero` backend is the same routine. A full turn of the argument
*between* two nodes is invisible to that test.

The demo uses f(z) = (z − a)(z − b), with both zeros inside the unit box, 1e-4 above the bottom edge, and between
the same pair of nodes. The true count is 2. The node routine returns 1, and still returns 1 at doubled density.
`winding_box_zero_certificate` therefore issues a trust-class-arb sidecar that says "exactly 1 zero", which is false.

The function is contrived, but the algorithm is generic. ζ's main RH-in-box driver is not affected, because it uses
`segment_winding_certificate` on segment enclosures. Whether earlier sidecars came from the node backend has not
been audited here.

## The kernel-checked file

`lean/Ramification.lean` is core Lean, with no Mathlib. For Q(i), Q(√5), Q(∛2) and Q(ζ₅), and every prime p < 30,
`decide` checks four things:

- the factorisation of a monogenic generator mod p;
- that each factor is irreducible (no roots, and for the quartic no quadratic factor either);
- that Σ e·f = n;
- that ramified ⇔ p | disc.

Dedekind–Kummer and disc = d_K are cited, not checked. A negative-control theorem confirms that a false row is
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
