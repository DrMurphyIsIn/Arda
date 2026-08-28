# Applicability to the Brualdi–Goldwasser effort

Handoff note for the BG proof session. Honest, three-layer assessment of whether
the Turán/enclosure machinery added in 0.1.3 helps BG. Short version:
**the infrastructure yes, the mathematics partly, the open crux no.**

## Layer 1 — the certificate infrastructure: reusable (and BG-derived)

`turan_from_enclosure` (in `src/telperion/turan.py`) is a *worst-corner
monotonicity bridge*: given rational enclosures and a strict rational margin, a
polynomial inequality among the enclosed constants follows by `norm_num`, bridged
by one once-proved `nlinarith` lemma. This is the **consume** side — it takes an
enclosure as a hypothesis and proves a product-vs-square inequality.

**Two corrections, both grounded in the code (do not repeat these mistakes).**

1. *ρ_B is not an enclosure target* (per BG-session review, `ExactCruxes.lean`).
   ρ_B is *algebraic* and clears to exact rational via `rhoB_pow11 : rhoB^11 =
   621/64`, so every ρ_B comparison (e.g. `26/23 < rhoB ⟺ (26/23)^11 < 621/64`)
   is a pure `norm_num`. Enclosures cross **only** where the constant is
   transcendental-but-boundable (exp(−θ)), never the algebraic-and-cleared BG
   constants.

2. *`TuranEnclosureCertificate` does NOT generalize `exp_bracket`* — checked
   against `examples/exp_bracket/`. They are opposite pipeline stages:
   `exp_bracket` **derives** a bracket of a transcendental (`exp(−θ) ≤ hi` via a
   Taylor lower bound on `exp(θ)`, Mathlib `Real.sum_le_exp_of_nonneg`), with
   `Real.exp` in its statement; `TuranEnclosureCertificate` **consumes** a given
   enclosure with no transcendental in its Lean at all. Neither generalizes the
   other, and the H2-Bridge exp sites use the bracket as an *amplitude* bound
   (`4/3·exp(−θ)·ρⁿ`), not a product-vs-square — so they do not even compose.
   My earlier "clean refactor onto the general certificate" line was wrong.

**The genuine reusable capability for the H2-Bridge exp sites** (`BridgeStep4*`,
`LemmaA`, `R47RateZBound`) is therefore **not** the Turán certificate but a
generalization of `exp_bracket`'s *own* derive-side machinery:
`ExpBracketCertificate` (in `src/telperion/exp_bracket.py`, added alongside this).
It emits the exact two-theorem `exp(−θ)` bracket for any (θ, N), reproduces the
committed `examples/exp_bracket/` artifact **byte-for-byte** (subsumption test in
`tests/test_exp_bracket.py`), and is the drop-in for each site:

```python
from telperion import ExpBracketCertificate
c = ExpBracketCertificate.build(Fraction(37167, 100000), nterms=9,
                                le_name="...", ge_name="...")  # auto-fills tfloor, hi
assert c.check()          # exact-rational: tfloor <= Taylor_N(theta), 1/tfloor <= hi
lean = c.lean()           # the two Real.exp bracket theorems
```

That is the Bridge/H2 frontier (owned by that session) — infrastructure reuse,
**not** a lever on the crux; the migration of the existing `exp_bracket` example
onto the class is left to them (the byte-subsumption test is the safety net).

**Separately**, `TuranEnclosureCertificate` is reusable if a BG step ever
compares *genuinely transcendental* constants in the shape `C_left · C_right <
C_mid²` (three enclosed — not algebraic — constants). No current BG step does.
Instantiate:

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
