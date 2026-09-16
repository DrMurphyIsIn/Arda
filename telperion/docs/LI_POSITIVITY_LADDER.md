# Li positivity-ladder emitter (RH-roadmap Track 2)

Certifies finite prefixes of **Li's criterion** onto the *already-formalized* upstream
reduction, surfaced by the Palomar miner:

    nicholasbulka/li-criterion-rh-equivalence-lean
    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

(`liSummand n ρ = 1 − (1 − 1/ρ)^{−(n+1)}`; the RHS is the Li–Keiper positivity ladder.)

## What the emitter does

`LiPositivityLadderEmitter` (kind `li_positivity`) emits, per rung `n`:

    theorem li_rung_<n> (hlo : (lo : ℝ) ≤ (taylorCoeff riemannXi n).re) :
        0 ≤ (taylorCoeff riemannXi n).re :=
      le_trans (by norm_num : (0:ℝ) ≤ lo) hlo

- `lo` is a **certified positive rational lower bound** on the n-th ξ Taylor coefficient's
  real part. `certify` refuses `lo ≤ 0` (a non-positive bound cannot witness positivity) and `n < 0`.
- The claim is **load-bearing**: it is about the ACTUAL `(taylorCoeff riemannXi n).re`, not an
  abstract real — so it is non-vacuous.

## Trust seam (documented, honest)

`hlo` — the lower bound `lo ≤ (taylorCoeff riemannXi n).re` — is an EXTERNAL numeric input
(Arb / mpmath interval arithmetic on ξ's Taylor coefficient at 0), carried as a theorem
HYPOTHESIS. The kernel proves only `0 ≤ lo ⟹ 0 ≤ coeff`; it does NOT evaluate the
transcendental coefficient. Same discipline as the RH-in-a-box Arb enclosures and the
effective-dVP inputs.

## Honest ceiling

Each rung is a finite verification. The **uniform `∀ n`** is exactly the RHS of
`li_criterion_rh_iff` — i.e. **RH itself**. Certifying rungs 0..N is NOT progress toward RH;
it is the certificate-shaped, generator-producible prefix of a reduction whose tail is RH.
`conjecture1_proved = False`.

## Wiring status / TODO

- Emitter + `certify` + registry wiring + Python tests: DONE (this branch), classification green.
- The emitted rungs `import Lc.LiCriterion.XiOrderBridge`; **CI compilation needs the upstream
  `li-criterion-rh-equivalence-lean` as a lake dependency** (add a `require` to a new
  `examples/li_positivity/lean/lakefile.toml`, mirroring how `zeta_zero_localization` requires
  its sibling `zero_free_bridge`). Until wired, rungs are emitted-but-not-CI-compiled.
- NEXT: an Arb finder (`enclose_xi_taylor_coeff`) that computes the rigorous `lo` per n
  (reuse/extend `telperion.arb_enclosure`), turning the trust-seam hypothesis into a produced
  certificate — then assemble `∀ n < N, 0 ≤ (taylorCoeff riemannXi n).re` and cite
  `li_criterion_rh_iff` for the "first N rungs verified" statement.
- Reuse the RvM/explicit-formula foundation (`RVM_EXPLICIT_FORMULA_FOUNDATION.md`,
  `DiffractionCore.rect_explicit_formula`) if expressing λ_n via the arithmetic side later.

## The finished ladder (2026-09-09)

The original PR (#393) shipped the emitter with a single hand-picked rung. The finish
replaces that with the full generated ladder:

- **Rigorous backend** — `telperion.li_coeff.enclose_li_coeffs`: exact-rational outward
  enclosures of `taylorCoeff riemannXi n` via python-flint ball arithmetic. The series
  route never meets the ζ-pole: by the functional equation `ξ(1/(1−z)) = ξ(g(z))` with
  `g = −z/(1−z)`, and at 0 the completed form `ξ(s) = (s−1)·π^{−s/2}·Γ(s/2+1)·ζ(s)` is
  analytic factor-by-factor (`s·Γ(s/2)` absorbed into `Γ(s/2+1)`; `ζ(0) = −1/2`). The
  Li coefficients are read off `F′/F`. Self-check: the first three enclosures must
  contain the PUBLISHED Li–Keiper values (Keiper 1992 / Li 1997 / Coffey 2004) or the
  backend refuses — an external anchor against normalization/index bugs.
- **Forty rungs** (extended from 20 on `rh/b1-li-prefix`) —
  `examples/li_positivity/generate.py` regenerates `lean/LiPositivity.lean`
  (drift-checked; manifest group `flint`): rungs `n = 0..39` with lower bounds
  rounded DOWN to 12 significant decimals (still rigorous, readable literals).
  λ₁ through λ₄₀ are all certified positive. (`PREC_BITS` raised 192 → 256 for
  margin; see the cost model below for why prec/n scale together.)
- **The falsifiability face** — `li_neg_refutes_rh`: a certified NEGATIVE upper bound
  on any rung refutes RH outright through `li_criterion_rh_iff` (term-mode proof).
  Never expected to fire; it makes the ladder falsifiable, not confirmation-only.
- **Axiom guard** — `AxiomGuardLiPositivity.lean` re-verifies (at our pin) that the
  rungs, the refutation atom, and the upstream `li_criterion_rh_iff` itself use only
  the three Mathlib axioms. Anchors extended to `li_rung_0 / _19 / _29 / _39`.
- **Negative control** — `negctrl_adapters/adapter_li_positivity.py`: a sign-corrupted
  lower bound (`lo = −1/100`, minted past the Layer-1 refusal) must be kernel-rejected
  at the in-proof `norm_num` gate; the `+1/100` twin compiles. The B1 extension adds
  an identical control at the NEW last rung `n = 39` (forged `lo = −3/100` rejected,
  `+1/100` twin compiles) — both verified `okay = kernel_rejects AND true_compiles`.
- **CI** — `li-positivity-compiles` in telperion-lean-e2e: regenerate `--check`, then
  `lake build` against the pinned upstream (toolchain island v4.34.0-rc1), then the
  axiom guard.

Still true, and stated everywhere: the uniform `∀ n` IS RH; forty rungs are a finite
necessary-condition check and no progress toward it. `conjecture1_proved = False`.

## Cost model & the packaging wall (B1, `rh/b1-li-prefix`)

The load-bearing finding of the B1 extension: **the Arb enclosure is NOT the
bottleneck; the Lean-kernel packaging is.** Two separately-measured costs.

### Arb side (cheap, well-understood)

`enclose_li_coeffs(N, prec_bits)` computes the whole `0..N−1` prefix in ONE
truncated-power-series pass. Measured on this machine (python-flint 0.6.0 / FLINT
Arb):

| prec_bits | N enclosed | wall time | reachable n (lo stays > 0) |
|-----------|-----------|-----------|----------------------------|
| 128 | 178 | 0.009 s | ≈ 126 |
| 192 | 242 | 0.016 s | ≈ 190 |
| 256 | 306 | 0.027 s | ≈ 254 |
| 384 | 434 | 0.052 s | ≈ 383 |
| 512 | 562 | 0.092 s | ≈ 512 |
| 768 | 818 | 0.224 s | ≈ 768 |
| 1024 | 1074 | 0.457 s | ≈ 1024 |

Two clean laws:
- **Reachable-n ≈ prec_bits − 1.** λ_n grows like (n/2)·log n (Arc B), so the
  *magnitude* is never the problem; what fails is ball-width blow-up under
  cap-truncated series arithmetic once the working precision is exhausted around
  order ≈ prec. Past that the lower endpoint goes negative (a refusal, never a
  wrong box — the self-check + outward rounding hold).
- **Enclosing n ≈ 1000 coefficients costs < 0.5 s at 1024 bits.** So even the
  full Li–Keiper prefix to n = 1000 is *trivially* enclosable. The numeric input
  is not the wall.

### Lean side (the wall)

Each rung carries exactly ONE Arb enclosure as its hypothesis `hlo`, and the
certified prefix statement (`li_rh_iff_tail N`) needs all N of them simultaneously:
to state "the first N rungs are nonneg" the caller must supply `∀ n < N, hlo_n` —
**N independent Arb hypotheses discharged together**. At N = 1000 that is ~1000
simultaneous rational-enclosure hypotheses per certified prefix. The discipline to
*package* that many trusted numeric inputs into one auditable, drift-checked,
axiom-guarded bundle **does not yet exist** in this repo (the RH-in-box ladders
package tens of Arb bands, not a thousand). This is the roadmap-errata packaging
wall, and it is real:

- Per-rung Lean cost is otherwise flat and cheap: the proof is a fixed
  `le_trans (by norm_num) hlo`; the `by norm_num` on a 12-significant-digit
  rational literal is O(1). Doubling 20 → 40 rungs added no measurable compile
  time beyond the (dominant, fixed) cost of importing `Lc.LiCriterion.XiOrderBridge`
  + Mathlib.
- What does NOT scale flat is the *audit surface*: every rung adds one trusted
  numeric hypothesis to the seam. Twenty, forty — reviewable. A thousand — not,
  absent a packaging format (a single certificate object carrying the N enclosures
  with a machine-checkable provenance hash, guarded once).

### What n is reachable before the wall bites

- **Numerically:** ~1000 in under a second (raise `PREC_BITS` ≈ n).
- **In kernel, per-rung, today:** unbounded in principle (each rung is independent
  and cheap) — but each is a *separate* trusted seam, so the honest ceiling is set
  by how many seams a human can audit, not by compute. **40 is a comfortable,
  fully-audited extension.** Going to the hundreds is mechanically possible but
  crosses from "audited prefix" into "unreviewed hypothesis pile" without the
  packaging discipline. **n = 1000 is explicitly NOT attempted here** (roadmap
  errata), and this document is why.

### The honesty caveat (roadmap-flagged, restated)

Certified prefixes are *morally forced* by on-line verification: given that ξ's
early Taylor coefficients are known-positive (published Li–Keiper values, and every
Arb enclosure computed so far), the rung theorems are exactly the certificate-shaped
restatement of that fact. They are **instrumentation** — a falsifiable, kernel-checked
harness whose payload is `li_neg_refutes_rh` (one negative rung would refute RH) —
**not evidence toward RH.** The uniform `∀ n` is RH itself; no finite prefix, however
long, moves toward it. `conjecture1_proved = False`.
