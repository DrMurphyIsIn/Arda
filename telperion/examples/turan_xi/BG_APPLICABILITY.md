# Applicability to the Brualdi–Goldwasser effort

Handoff note for the BG proof session. Honest, three-layer assessment of whether
the Turán/enclosure machinery added in 0.1.3 helps BG. Short version:
**the infrastructure yes, the mathematics partly, the open crux no.**

## Layer 1 — the certificate infrastructure: reusable (and BG-derived)

`turan_from_enclosure` (in `src/telperion/turan.py`) is a *worst-corner
monotonicity bridge*: given rational enclosures and a strict rational margin, a
polynomial inequality among the enclosed (transcendental / hard-to-compute)
constants follows by `norm_num`, bridged by one once-proved `nlinarith` lemma.
That is the dominant BG proof pattern already — `bilinear_corner_nonneg`,
`exp_bracket` (rigorous enclosure of exp(−θ) for the R47Encode far constant),
the ρ_B `(1+t)^11 ≤ 621/64` brackets. `TuranEnclosureCertificate` is a new
instance of that existing pattern.

**Directly reusable when a BG step has the shape** `C_left · C_right < C_mid²`
between three enclosed constants (e.g. a ρ_B / tie-constant bracket that happens
to be a product-vs-square). Instantiate:

```python
from telperion import TuranEnclosureCertificate
# enclosures indexed k=0..K as (lo,hi) exact rationals; interior k certified via
# hi_{k-1}*hi_{k+1} < lo_k^2. For a bespoke 3-constant bracket, feed a length-3
# enclosure list [(lo0,hi0),(lo1,hi1),(lo2,hi2)] -> certifies C0*C2 < C1^2.
cert = TuranEnclosureCertificate(name="bg_bracket", enclosures=(...))
assert cert.check()          # exact-rational, blocks emission if margin <= 0
lean = cert.lean()           # bridge lemma + per-index norm_num theorems
```

If the BG step is a *different* algebraic shape (not product-vs-square), the
**pattern** transfers but the emitter does not — write a sibling bridge lemma
(one `nlinarith` monotonicity fact) + per-instance `norm_num` margins, exactly
as `turan.py` does. Do **not** try to bend product-vs-square onto a non-matching
BG bracket; emit a new certificate class instead.

## Layer 2 — the Turán/Laguerre mathematics: partial overlap

BG already lives next door to the real-rootedness toolkit: `interlacing`
(Wronskian-SOS root interlacing), `lorentzian` / `matching_lorentzian`
(Hodge–Riemann / Lorentzian polynomials). Permanents and matching polynomials
are Laguerre–Pólya objects (Heilmann–Lieb real-rootedness; log-concavity of
matching sequences). So **if** a BG sub-step is ever phrased as "this coefficient
sequence is log-concave" or "this polynomial is real-rooted," the
Turán-inequality-from-enclosures certificate drops in. This is opportunistic
reuse, not a lever on the headline.

## Layer 3 — the open BG crux: NOT addressed

The live BG frontier (per the campaign ledger) is the **H2 bridge**
(Branch → per(L), the Step-4 uniform O(1/p²) "G−1") and the **tree→hub Hnorm**
core — permanent-ratio extremal / arithmetic-integrality problems. Turán
inequalities do not touch them. Do not spend BG budget trying to force a
connection here.

## Meta-observation (framing, not a tool transfer)

Both the BG Φ≤1 crux and RH-via-Turán are "no finite smooth certificate closes
it" walls — but for **dual** reasons. BG's Φ≤1 turned out to be an *integrality /
arithmetic* fact (23-adic; no smooth potential). RH-via-Turán is unreachable
because it is *transcendental and infinite* (no uniform-in-k rational bound).
Same symptom, opposite cause. Useful when writing the "why finite certificates
stop here" sections of either paper; not a shortcut for either proof.
