# Design: Kernel-Verified Jensen–Pólya Hyperbolicity Certificates for the Riemann ξ

**Date:** 2026-09-05
**Status:** Design (approved for spec; pre-implementation)
**Branch:** `rh/jensen-hyperbolicity` (worktree `arda-rh-wire`)
**Honesty flag:** `conjecture1_proved = False` — this is a formal-verification first, **not** a step that closes RH.

---

## 1. Motivation and framing

The user proposed remapping the Riemann zeta function onto a different
geometry/topology and locating the nontrivial zeros there. That instinct lands on
the **Hilbert–Pólya / spectral program** — the deepest known attack line. Our own
`docs/RH_BARRIER_CRACK_2026-08-30.md` already grades the candidate geometries and
identifies the **Jensen–Pólya reformulation** (Griffin–Ono–Rolen–Zagier 2019,
"GORZ") as graded **ALIVE**: it is the one reformulation whose consequences are
**finite and certificate-shaped**, so Telperion's exact-arithmetic + Lean-kernel
discipline actually applies.

### The reformulation

Let `Ξ(t) = ξ(1/2 + it)`, the real, even entire function built from `ζ`. Its
Maclaurin coefficients form a real sequence `{α(k)}`. The **Jensen polynomial** of
degree `d`, shift `n` is

```
J^{d,n}(X) = Σ_{k=0}^{d} C(d,k) · α(n+k) · X^k.
```

**Pólya's equivalence:** `RH ⟺ every J^{d,n} is hyperbolic (all roots real).**
GORZ proved (i) for each fixed `d`, `J^{d,n}` is hyperbolic for all-but-finitely-many
`n`; (ii) renormalized, `J^{d,n} → H_d` (Hermite) as `d→∞` — the GUE "derivative
aspect". They verified full hyperbolicity for **d ≤ 8, all n**.

### What is certifiable vs. what is not

- **Certifiable (this project):** hyperbolicity of *concrete* `J^{d,n}` — real-rootedness
  of an explicit polynomial whose coefficients are rigorous rational *enclosures* of the
  transcendental `α(n+k)`.
- **NOT certificate-shaped (out of scope):** the genuinely-open piece is an *effective,
  uniform-in-`d`* threshold `N(d)`. That is the coefficient-asymptotics error term — the
  "archimedean magnitude" wall flagged in `PROOF_STATUS.md`. We do not attempt it here.

### Novelty

To the best of our literature knowledge, **no Jensen-polynomial hyperbolicity for `ζ`
has ever been kernel-verified in Lean.** The GORZ verification (d ≤ 8) was
floating-point / computer-algebra, not formal. A kernel-verified certificate family is
a genuine formal-mathematics increment, independent of RH itself.

---

## 2. Existing substrate (what we build on)

From the RH Telperion worktree (`arda-rh-wire/telperion`):

- `emit_bracket.py` — transcendental enclosures (`IntervalBracketEmitter`): the pattern
  we extend for rigorous coefficient enclosures.
- `emit_sturm_positive.py`, `examples/sturm_positive` — Sturm strict-interval positivity
  (`0 < p` on `[a,b]`, i.e. root *exclusion*). **Does not count roots.**
- `emit_interlacing.py`, `examples/interlacing` — emits Wronskian *nonnegativity* (the
  Hermite–Kakeya–Obreschkoff certificate ingredient). **Emits positivity, not a
  hyperbolicity Prop.**
- `emit_psd_form.py`, `examples/psd_form` — `0 ≤ xᵀMx` via LDLᵀ congruence. The general
  Phase-2 engine.

**Critical gap confirmed by inspection:** every existing emitter emits a *positivity /
PSD* Prop — a certificate *ingredient*. **None emits "this polynomial is hyperbolic."**
The bridge from certificate → hyperbolicity Prop is the core mathematical lemma this
project must formalize.

---

## 3. Architecture

Two phases. Phase 1 lands the first verified result on the smallest nontrivial cases
with minimal general-theory formalization; Phase 2 builds the reusable general engine.

### 3.1 The hyperbolicity Prop (how we state the theorem in Lean)

For a real polynomial `J : Polynomial ℝ`, hyperbolicity is stated as

```
J.roots.card = J.natDegree
```

(`Polynomial.roots` counts roots in `ℝ` with multiplicity; `card = natDegree` ⟺ the
polynomial splits over `ℝ` ⟺ all complex roots are real). AXLE's
**signature/statement-match gate** confirms the emitted wrapper theorem is literally this
Prop for the intended `J^{d,n}`, not a weaker surrogate.

### 3.2 Phase 1 — discriminant beachhead (d = 2, 3, 4)

For low degree, real-rootedness has an elementary discriminant criterion, avoiding the
general Hermite-signature theorem:

- **d = 2:** real-rooted ⟺ `b² − 4ac ≥ 0`.
- **d = 3:** three real roots ⟺ discriminant `Δ ≥ 0`.
- **d = 4:** all-real-roots criterion (`Δ ≥ 0` together with the auxiliary `P ≤ 0`,
  `D ≤ 0` conditions).

Each discriminant is an explicit polynomial in the coefficients, hence a rational-interval
expression in the coefficient enclosures. We certify its sign **with margin exceeding the
interval width**, so the enclosure does not flip the criterion.

Per-degree bridge lemmas ("discriminant sign ⟹ all roots real") are small and, for
d = 2,3, near-elementary. These are formalized once each.

### 3.3 Phase 2 — general Hermite/PSD engine

Hyperbolicity ⟺ the `d×d` **Hermite (Bezoutian) matrix** `H(J) ⪰ 0` (⟺ real roots;
`≻ 0` ⟺ real & distinct). `H`'s entries are polynomials in the coefficients, so they are
rational-interval-computable. We certify `H ≻ 0` via LDLᵀ with **pivot margin `δ > 0`
exceeding the interval widths** (`PSDFormEmitter`). A positive-definite margin is exactly
what makes the certificate robust to transcendental coefficient enclosures.

**The one genuine mathematical lift:** formalize **`H(J) ≻ 0 ⟹ J.roots.card =
J.natDegree`** (the Hermite/Sylvester real-root-counting theorem) in Lean — likely absent
from Mathlib v4.32.0. Proved once, reused for every `(d,n)`. Fallback: a Sturm-sequence
real-root *count* theorem (also absent from Mathlib; comparable lift).

### 3.4 Coefficient enclosure module (shared, riskiest link — built first)

The `α(k)` are (up to normalization) moments of an explicit, super-exponentially-decaying
Pólya kernel:

```
Ξ(t) = ∫_0^∞ Φ(u) cos(t u) du,   b_m = ∫_0^∞ u^{2m} Φ(u) du,
Φ(u) = Σ_{n≥1} (2π²n⁴ e^{9u} − 3π n² e^{5u}) · exp(−π n² e^{4u}).
```

Rigorous enclosure of each `b_m` (hence `α(n+k)`) via a split integral:

- **`[0, U]`:** certified interval quadrature (interval arithmetic on a grid with a
  certified derivative/Lipschitz bound, or a Taylor-model bound).
- **`[U, ∞)`:** explicit super-exponential tail bound `∫_U^∞ u^{2m} Φ(u) du ≤ (explicit
  small rational)`.

Output: certified rational intervals `[lo, hi]` for each coefficient. All exact-rational,
kernel-checkable. Precision (choice of `U`, grid, series truncation) is driven **upward**
until interval widths fall below the discriminant/PSD margin.

### 3.5 New emitter: `JensenHyperbolicityEmitter`

`src/telperion/emit_jensen_hyperbolicity.py`. Given `(d, n)` and certified coefficient
enclosures, it renders:

1. coefficient-enclosure facts (`IntervalBracketEmitter` substrate),
2. the Jensen assembly `c_k = C(d,k)·α(n+k)` (`IdentityEmitter`),
3. **Phase 1:** the discriminant identity + sign-with-margin fact + per-degree bridge;
   **Phase 2:** the Hermite-matrix identity + PSD cert (`PSDFormEmitter`) + general bridge,
4. the wrapper theorem `J^{d,n}.roots.card = J^{d,n}.natDegree`, gated by AXLE
   statement-match.

Lean output under `examples/jensen_hyperbolicity/lean/`.

---

## 4. Data flow

```
Φ kernel  ──► coefficient-enclosure module ──► certified [lo,hi] for α(n..n+d)
                                                     │
                                                     ▼
                                    Jensen assembly  c_k = C(d,k)·α(n+k)
                                                     │
                        ┌────────────────────────────┴───────────────────────┐
                Phase 1 │ discriminant Δ(c) sign, margin > width              │ Phase 2
                        │ + per-degree "Δ≥0 ⟹ real-rooted" lemma             │ Hermite H(c) ≻ 0
                        └────────────────────────────┬───────────────────────┘ + "H≻0 ⟹ real-rooted"
                                                     ▼
                          JensenHyperbolicityEmitter ──► Lean text
                                                     │
                                   AXLE warm-verify + statement-match gate
                                                     │
                                          lake build (kernel) ──► frozen cert
```

---

## 5. Scope of the "verified first result"

Phase 1 deliverable: a kernel-verified certificate family for a concrete grid of
`(d, n)` at `d = 2, 3, 4`, prioritizing the **hard small-`n` cases** (where
real-rootedness is tightest and the finitely-many GORZ exceptions live). This is the
*first formally verified Jensen-polynomial hyperbolicity for `ζ`.*

Phase 2 deliverable: the general Hermite/PSD bridge + emitter path, validated by
re-deriving Phase 1 cases through the general engine, then scaling toward `d ≤ 8`.

---

## 6. Testing

- **Coefficient module:** cross-check enclosures against published high-precision GORZ /
  Coffey coefficient values (must lie inside `[lo, hi]`); property test that widths shrink
  monotonically as precision rises; negative control (a deliberately loose enclosure must
  *fail* the margin gate, not silently pass).
- **Discriminant / PSD certs:** exact-rational self-checks at generation time (existing
  Telperion `ValidationReport` discipline); a **kernel-gated negative control** — a
  non-hyperbolic polynomial (e.g. `x²+1`) must *fail* to certify.
- **Bridge lemmas:** stand-alone Lean unit theorems with their own `lake build` target
  before wiring into the emitter.
- **End-to-end:** each emitted `(d,n)` cert compiles under `lake build` with axioms ⊆
  `{propext, Quot.sound, Classical.choice}` and no `sorry`; AXLE statement-match confirms
  the wrapper Prop.
- **CI discipline:** new Lean lives in its own build target, unwired from the green RH CI
  until it is itself green (matches the `zero_free_bridge` / `borel_caratheodory` pattern).

---

## 7. Risks and honest ceilings

1. **Enclosure tightness (Phase 1 gate):** if interval widths exceed the discriminant/PSD
   margin, the cert fails and precision must rise. Mitigated by building the enclosure
   module first and driving `U`/grid/truncation up until margins clear.
2. **Bridge-lemma formalization (Phase 2):** the general Hermite-signature real-root
   theorem is likely not in Mathlib; formalizing it is the bulk of Phase 2. Phase 1's
   per-degree discriminant lemmas sidestep it to land the first result.
3. **Over-claiming:** this does **not** prove RH. It certifies finitely many `J^{d,n}`.
   The uniform-in-`d` effective threshold `N(d)` — the actual RH-closing piece — is not
   certificate-shaped and is explicitly out of scope. Every artifact carries
   `conjecture1_proved = False`.
4. **Coefficient normalization:** the exact GORZ normalization constant of `{α(k)}` must
   be pinned precisely in the enclosure module (a transcription error here is silent);
   guarded by the published-value cross-check test.

---

## 8. Out of scope

- Any claim toward proving RH or an effective `N(d)`.
- The other graded geometries (Connes adelic, 𝔽₁-site, Li/Weil positivity, de
  Bruijn–Newman) — a separate line if pursued.
- Wiring Jensen certs into the main RH zero-free CI (kept isolated until green).
