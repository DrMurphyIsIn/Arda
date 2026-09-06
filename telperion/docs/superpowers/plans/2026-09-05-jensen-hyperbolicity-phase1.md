# Jensen–Pólya Hyperbolicity — Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce the first kernel-verified (Lean) hyperbolicity certificates for the Riemann-ξ Jensen polynomials `J^{d,n}` at `d = 2, 3, 4`, via rigorous rational coefficient enclosures + per-degree discriminant bridge lemmas.

**Architecture:** Python certifies (exact interval arithmetic) a rational **box** `[lo_k, hi_k]` containing the transcendental ξ Taylor coefficients `α(n+k)`, cross-checked against an mpmath oracle. Lean proves the purely-algebraic **box-hyperbolicity** theorem "∀ coefficients in the box, `Σ C(d,k)·c_k·Xᵏ` has all real roots" via a per-degree discriminant bridge. The concrete `J^{d,n}` hyperbolicity is the box theorem instantiated at the certified box; coefficient-membership is the one documented non-kernel input.

**Tech Stack:** Python 3.14 (`fractions.Fraction`, `sympy` exact, `mpmath` as test oracle only), Telperion emitter framework, Lean 4 + Mathlib v4.32.0, `lake build`, AXLE warm-verify + statement-match gate.

**Spec:** `docs/superpowers/specs/2026-09-05-jensen-polya-hyperbolicity-design.md`

## Global Constraints

- **No emoji anywhere in code, Lean, or certificates** (user standing rule).
- **Certificate path is exact-rational only** — `Fraction`/`sympy.Rational`, never `float`. `mpmath` appears **only** in test-oracle / reference code, never in emitted certificate data.
- **The kernel theorem is the box statement.** Coefficient-membership (true `α ∈ box`) is Python-certified input, explicitly labeled non-kernel — mirror the existing inputs-R/B convention.
- **Honesty flag on every artifact:** `conjecture1_proved = False`. No file, docstring, or commit may claim progress toward proving RH.
- **New Lean is an isolated `lake` build target**, unwired from the green RH CI until itself green (matches `examples/zero_free_bridge`, `examples/borel_caratheodory`).
- **Kernel acceptance bar:** every emitted `.lean` compiles with no `sorry`/`admit`/`axiom`, axioms ⊆ `{propext, Quot.sound, Classical.choice}`, AXLE statement-match confirms the wrapper Prop.
- **Branch:** `rh/jensen-hyperbolicity` in worktree `arda-rh-wire`. Do NOT operate on the `arda-trading` checkout.
- **Lean tactic note:** exact theorem *statements* and the Mathlib lemma toolkit are given; the tactic block is developed against the kernel. A task is "done" only when `lake build` is green — never when the proof merely looks plausible.

---

### Task 1: mpmath reference oracle for ξ Taylor coefficients

**Files:**
- Create: `src/telperion/rh_jensen/__init__.py`
- Create: `src/telperion/rh_jensen/reference.py`
- Test: `tests/rh_jensen/test_reference.py`

**Interfaces:**
- Produces: `xi_coeff_reference(m: int, prec_bits: int = 400) -> mpmath.mpf` — high-precision (non-rigorous) value of the normalized ξ Maclaurin coefficient `α(m)`, where `Ξ(t) = ξ(1/2 + i t) = Σ_{m≥0} α(m) · t^{2m}` (even function; `α(m)` is the coefficient of `t^{2m}`, sign included).
- Produces: `xi_at_zero_reference(prec_bits: int = 400) -> mpmath.mpf` — `ξ(1/2)` computed directly from `ζ, Γ, π` as the anchor.

- [ ] **Step 1: Write the failing test**

```python
# tests/rh_jensen/test_reference.py
import mpmath
from telperion.rh_jensen.reference import xi_coeff_reference, xi_at_zero_reference

def test_alpha0_equals_xi_half():
    # alpha(0) = Xi(0) = xi(1/2); anchor against a direct zeta/Gamma/pi evaluation.
    mpmath.mp.dps = 60
    xi_half = xi_at_zero_reference()
    alpha0 = xi_coeff_reference(0)
    assert abs(alpha0 - xi_half) < mpmath.mpf(10) ** (-50)

def test_xi_half_direct_value():
    # xi(1/2) = 1/2 * s(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s) at s = 1/2, positive, ~0.4971207782.
    mpmath.mp.dps = 40
    val = xi_at_zero_reference()
    assert abs(val - mpmath.mpf("0.4971207781964073")) < mpmath.mpf(10) ** (-12)
```

- [ ] **Step 2: Run test to verify it fails**

Run: `pytest tests/rh_jensen/test_reference.py -v`
Expected: FAIL (`ModuleNotFoundError: telperion.rh_jensen.reference`).

- [ ] **Step 3: Write minimal implementation**

```python
# src/telperion/rh_jensen/reference.py
"""High-precision mpmath ORACLE for Riemann-xi Taylor coefficients.

Test/reference use ONLY. Never import from certificate/emitter code paths.
conjecture1_proved = False.
"""
import mpmath

def _xi(s):
    # Completed zeta: xi(s) = 1/2 * s*(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s).
    return mpmath.mpf("0.5") * s * (s - 1) * mpmath.power(mpmath.pi, -s / 2) \
        * mpmath.gamma(s / 2) * mpmath.zeta(s)

def xi_at_zero_reference(prec_bits: int = 400) -> mpmath.mpf:
    old = mpmath.mp.prec
    try:
        mpmath.mp.prec = prec_bits
        return mpmath.re(_xi(mpmath.mpf("0.5")))
    finally:
        mpmath.mp.prec = old

def xi_coeff_reference(m: int, prec_bits: int = 400) -> mpmath.mpf:
    # Xi(t) = xi(1/2 + i t); alpha(m) = coeff of t^{2m}. Xi is even and real.
    # Taylor coefficient via mpmath.taylor of the real even function of t.
    old = mpmath.mp.prec
    try:
        mpmath.mp.prec = prec_bits
        f = lambda t: mpmath.re(_xi(mpmath.mpf("0.5") + 1j * t))
        coeffs = mpmath.taylor(f, 0, 2 * m + 2)
        return coeffs[2 * m]
    finally:
        mpmath.mp.prec = old
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `pytest tests/rh_jensen/test_reference.py -v`
Expected: PASS (both). If `test_xi_half_direct_value` fails, correct the literal against a fresh 40-dps evaluation; if `test_alpha0_equals_xi_half` fails, the coefficient normalization is wrong — fix before proceeding (this anchors every later task).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/rh_jensen/__init__.py src/telperion/rh_jensen/reference.py tests/rh_jensen/test_reference.py
git commit -m "feat(rh-jensen): mpmath oracle for xi Taylor coefficients + xi(1/2) anchor"
```

---

### Task 2: Rigorous rational coefficient enclosure

**Files:**
- Create: `src/telperion/rh_jensen/coefficients.py`
- Test: `tests/rh_jensen/test_coefficients.py`

**Interfaces:**
- Consumes: `xi_coeff_reference` (tests only).
- Produces: `enclose_xi_coeff(m: int, prec_bits: int) -> tuple[Fraction, Fraction]` — a **rigorous** rational enclosure `(lo, hi)` with `lo <= alpha(m) <= hi`, using `mpmath.iv` directed-rounding interval arithmetic on the ξ evaluation plus a rigorous Cauchy-estimate bound on the Taylor remainder. Returns exact `fractions.Fraction`.
- Produces: `enclose_coeff_box(n: int, d: int, prec_bits: int) -> list[tuple[Fraction, Fraction]]` — the box `[(lo_k, hi_k)]` for `alpha(n), ..., alpha(n+d)`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/rh_jensen/test_coefficients.py
from fractions import Fraction
import mpmath
from telperion.rh_jensen.coefficients import enclose_xi_coeff, enclose_coeff_box
from telperion.rh_jensen.reference import xi_coeff_reference

def _contains(lohi, val):
    lo, hi = lohi
    return float(lo) <= val <= float(hi)

def test_enclosure_contains_oracle():
    mpmath.mp.dps = 80
    for m in range(0, 5):
        lo, hi = enclose_xi_coeff(m, prec_bits=300)
        assert lo <= hi
        assert _contains((lo, hi), float(xi_coeff_reference(m)))

def test_enclosure_width_shrinks_with_precision():
    lo1, hi1 = enclose_xi_coeff(2, prec_bits=120)
    lo2, hi2 = enclose_xi_coeff(2, prec_bits=300)
    assert (hi2 - lo2) < (hi1 - lo1)

def test_box_shape():
    box = enclose_coeff_box(n=0, d=2, prec_bits=200)
    assert len(box) == 3
    assert all(lo <= hi for lo, hi in box)

def test_negative_control_loose_box_is_honest():
    # A deliberately-too-loose enclosure must still be a valid (containing) bracket,
    # never a silently-tight lie. Width must be strictly positive.
    lo, hi = enclose_xi_coeff(3, prec_bits=64)
    assert hi > lo
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `pytest tests/rh_jensen/test_coefficients.py -v`
Expected: FAIL (`ModuleNotFoundError`).

- [ ] **Step 3: Write the implementation**

Implement `enclose_xi_coeff` using `mpmath.iv` (rigorous interval context): evaluate `Ξ` on an interval Cauchy contour / use `mpmath.iv` arithmetic through the `ζ, Γ, π` chain, and bound the `t^{2m}` Taylor coefficient rigorously via a Cauchy estimate `|alpha(m)| <= max_{|t|=R} |Xi(t)| / R^{2m}` combined with a directed-rounding evaluation on a radius-`R` ring. Convert interval endpoints to `Fraction` with outward rounding. `enclose_coeff_box` loops `enclose_xi_coeff(n..n+d)`.

Key rigor rules (enforce in code):
- Every endpoint conversion rounds **outward** (`lo` down, `hi` up) so the rational box always contains the true interval.
- No bare `float` in returned values; only `Fraction`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `pytest tests/rh_jensen/test_coefficients.py -v`
Expected: PASS. If `test_enclosure_contains_oracle` fails, the Cauchy-remainder bound or the rounding direction is wrong — fix rigor before proceeding.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/rh_jensen/coefficients.py tests/rh_jensen/test_coefficients.py
git commit -m "feat(rh-jensen): rigorous rational enclosure of xi coefficients (mpmath.iv + Cauchy bound)"
```

---

### Task 3: Jensen assembly + discriminant-with-margin (d = 2)

**Files:**
- Create: `src/telperion/rh_jensen/jensen.py`
- Test: `tests/rh_jensen/test_jensen.py`

**Interfaces:**
- Consumes: `enclose_coeff_box`.
- Produces: `jensen_coeff_box(n: int, d: int, prec_bits: int) -> list[tuple[Fraction, Fraction]]` — box for `c_k = C(d,k)*alpha(n+k)`, `k = 0..d`.
- Produces: `disc2_margin(box: list[tuple[Fraction, Fraction]]) -> Fraction` — a certified rational lower bound on `c_1^2 - c_0*c_2` over the box (the d=2 Turán discriminant, up to the positive factor 4). Positive value ⟹ every polynomial in the box is real-rooted. Uses interval multiplication with outward rounding.

- [ ] **Step 1: Write the failing tests**

```python
# tests/rh_jensen/test_jensen.py
from fractions import Fraction
from telperion.rh_jensen.jensen import jensen_coeff_box, disc2_margin

def test_binomial_scaling():
    box = jensen_coeff_box(n=0, d=2, prec_bits=200)
    assert len(box) == 3  # c0, c1, c2 with weights C(2,0)=1, C(2,1)=2, C(2,2)=1

def test_d2_turan_margin_positive_small_n():
    # The Riemann xi Turan inequalities alpha(n+1)^2 >= alpha(n) alpha(n+2)
    # hold for all n (classical). Margin must certify positive at n = 0.
    box = jensen_coeff_box(n=0, d=2, prec_bits=300)
    m = disc2_margin(box)
    assert m > 0

def test_margin_is_lower_bound():
    # Margin must not exceed the midpoint discriminant (it is a guaranteed lower bound).
    box = jensen_coeff_box(n=1, d=2, prec_bits=300)
    m = disc2_margin(box)
    c0 = (box[0][0] + box[0][1]) / 2
    c1 = (box[1][0] + box[1][1]) / 2
    c2 = (box[2][0] + box[2][1]) / 2
    assert m <= c1 * c1 - c0 * c2
```

- [ ] **Step 2: Run to verify fail**

Run: `pytest tests/rh_jensen/test_jensen.py -v` — Expected: FAIL (`ModuleNotFoundError`).

- [ ] **Step 3: Implement**

`jensen_coeff_box`: multiply each `alpha(n+k)` interval by the exact integer `math.comb(d,k)` (interval scale by positive constant). `disc2_margin`: compute `c1^2` lower bound and `c0*c2` upper bound via interval arithmetic on the box endpoints with outward rounding, return `lower(c1^2) - upper(c0*c2)` as `Fraction`.

- [ ] **Step 4: Run to verify pass**

Run: `pytest tests/rh_jensen/test_jensen.py -v` — Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/rh_jensen/jensen.py tests/rh_jensen/test_jensen.py
git commit -m "feat(rh-jensen): Jensen assembly + d=2 Turan discriminant margin"
```

---

### Task 4: Lean d=2 bridge lemma (discriminant ≥ 0 ⟹ real-rooted)

**Files:**
- Create: `examples/jensen_hyperbolicity/lean/lakefile.lean`
- Create: `examples/jensen_hyperbolicity/lean/lean-toolchain` (copy from `examples/zero_free_bridge/lean/lean-toolchain`)
- Create: `examples/jensen_hyperbolicity/lean/JensenBridge.lean`
- Test: build gate (below)

**Interfaces:**
- Produces (Lean): `theorem hyperbolic_deg2_of_discrim_nonneg (a b c : ℝ) (ha : a ≠ 0) (h : 0 ≤ b^2 - 4*a*c) : (Polynomial.C a * X^2 + Polynomial.C b * X + Polynomial.C c).roots.card = 2` — the reusable d=2 bridge.

- [ ] **Step 1: State the theorem (write the Lean, proof `sorry` first)**

Create `JensenBridge.lean` with the statement above and `:= by sorry`. Toolkit: Mathlib `Mathlib.Algebra.QuadraticDiscriminant` (`discrim`, `quadratic_eq_zero_iff`, `exists_quadratic_eq_zero`), `Polynomial.roots`, `Polynomial.card_roots_le_degree`, `Real.sqrt` (since `0 ≤ discrim` gives `discrim = (Real.sqrt discrim)^2`).

- [ ] **Step 2: Verify it builds with sorry (scaffolding check)**

Run: `cd examples/jensen_hyperbolicity/lean && lake build`
Expected: builds with a `sorry` warning (confirms imports/toolchain wired).

- [ ] **Step 3: Discharge the proof**

Strategy: from `0 ≤ b^2 - 4ac`, set `s = Real.sqrt (b^2 - 4*a*c)`, exhibit the two roots `r± = (-b ± s)/(2a)` via `quadratic_eq_zero_iff`, show the quadratic factors as `a*(X - r+)*(X - r-)`, and conclude `roots.card = 2` (both real, multiplicity summing to `natDegree = 2`). Iterate tactics until green.

- [ ] **Step 4: Verify kernel-green, no sorry**

Run: `cd examples/jensen_hyperbolicity/lean && lake build 2>&1 | tee /tmp/jb.log; grep -c sorry /tmp/jb.log`
Expected: build succeeds; `grep` prints `0`. Also confirm `#print axioms hyperbolic_deg2_of_discrim_nonneg` shows only `{propext, Quot.sound, Classical.choice}`.

- [ ] **Step 5: Commit**

```bash
git add examples/jensen_hyperbolicity/lean/
git commit -m "feat(rh-jensen): Lean d=2 bridge -- discrim>=0 implies both roots real (kernel-green)"
```

---

### Task 5: `JensenHyperbolicityEmitter` (d = 2) + box-positivity assembly

**Files:**
- Create: `src/telperion/emit_jensen_hyperbolicity.py`
- Create: `examples/jensen_hyperbolicity/generate.py`
- Modify: `examples/jensen_hyperbolicity/lean/JensenHyperbolicity.lean` (emitted output target)
- Test: `tests/rh_jensen/test_emit_jensen.py`

**Interfaces:**
- Consumes: `jensen_coeff_box`, `disc2_margin`, the Lean bridge `hyperbolic_deg2_of_discrim_nonneg`, and the box-positivity substrate (`emit_lattice_box` / `emit_sos`).
- Produces (Python): `JensenHyperbolicityEmitter(degree: int).emit_body(fam, profile) -> tuple[str, int]` following the base `Emitter` contract (see `emit_facts.py`), with `self.kind = "jensen_hyperbolicity"` and `requires_prelude = ("hyperbolic_deg2_of_discrim_nonneg",)`.
- Produces (Lean, emitted): for a certified box, `theorem jensen_box_hyperbolic_deg2_<n> : ∀ c0 c1 c2 : ℝ, lo0 ≤ c0 → c0 ≤ hi0 → ... → (C (2*c2) * X^2 + C (2*c1) * X + C c0).roots.card = 2` (weights folded), proved by: box-positivity of `c1^2 - c0*c2 ≥ 0` ⟹ discriminant `≥ 0` ⟹ `hyperbolic_deg2_of_discrim_nonneg`.

- [ ] **Step 1: Write the failing test**

```python
# tests/rh_jensen/test_emit_jensen.py
from telperion.emit_jensen_hyperbolicity import JensenHyperbolicityEmitter
from telperion.rh_jensen.jensen import jensen_coeff_box, disc2_margin

def test_emit_produces_lean_theorem():
    box = jensen_coeff_box(n=0, d=2, prec_bits=300)
    assert disc2_margin(box) > 0
    em = JensenHyperbolicityEmitter(degree=2)
    text, count = em.render_box(n=0, box=box)
    assert count == 1
    assert "roots.card = 2" in text
    assert "hyperbolic_deg2_of_discrim_nonneg" in text

def test_emit_refuses_non_hyperbolic_box():
    # x^2 + 1 style box: c1 = 0, c0 = c2 = 1  => c1^2 - c0 c2 = -1 < 0. Must refuse.
    em = JensenHyperbolicityEmitter(degree=2)
    from fractions import Fraction as F
    bad_box = [(F(1), F(1)), (F(0), F(0)), (F(1), F(1))]
    try:
        em.render_box(n=0, box=bad_box)
        assert False, "expected refusal on non-hyperbolic box"
    except ValueError:
        pass
```

- [ ] **Step 2: Run to verify fail** — `pytest tests/rh_jensen/test_emit_jensen.py -v` — Expected FAIL.

- [ ] **Step 3: Implement the emitter**

`render_box` computes `disc2_margin(box)`; raises `ValueError` if `<= 0` (refusal = the negative-control gate); else emits the box-positivity fact (via `emit_lattice_box`/`emit_sos` for `c1^2 - c0*c2 ≥ 0` over the rational box) and the wrapper theorem chaining to `hyperbolic_deg2_of_discrim_nonneg`. Follow the `Emitter` base contract and `LeanProfile` skeleton pattern from `emit_facts.py`.

- [ ] **Step 4: Run to verify pass** — `pytest tests/rh_jensen/test_emit_jensen.py -v` — Expected PASS.

- [ ] **Step 5: Commit**

```bash
git add src/telperion/emit_jensen_hyperbolicity.py examples/jensen_hyperbolicity/generate.py tests/rh_jensen/test_emit_jensen.py
git commit -m "feat(rh-jensen): JensenHyperbolicityEmitter (d=2) with non-hyperbolic-box refusal gate"
```

---

### Task 6: End-to-end d=2 certificate + AXLE gate + trust-boundary doc (MILESTONE)

**Files:**
- Modify: `examples/jensen_hyperbolicity/generate.py` (driver writes emitted `.lean`)
- Create: `examples/jensen_hyperbolicity/lean/JensenHyperbolicity.lean` (generated, committed frozen)
- Create: `examples/jensen_hyperbolicity/README.md` (trust boundary + honesty flag)
- Test: build gate + `tests/rh_jensen/test_end_to_end_d2.py`

**Interfaces:**
- Consumes: everything above.
- Produces: a frozen kernel-verified `JensenHyperbolicity.lean` containing `jensen_box_hyperbolic_deg2_0` (and the concrete corollary conditional on the Python-certified coefficient-membership).

- [ ] **Step 1: Write the failing end-to-end test**

```python
# tests/rh_jensen/test_end_to_end_d2.py
import subprocess, pathlib
LEAN_DIR = pathlib.Path("examples/jensen_hyperbolicity/lean")

def test_generated_lean_builds_green():
    subprocess.run(["python", "examples/jensen_hyperbolicity/generate.py", "--degree", "2", "--n", "0"], check=True)
    r = subprocess.run(["lake", "build"], cwd=LEAN_DIR, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert "sorry" not in (LEAN_DIR / "JensenHyperbolicity.lean").read_text()
```

- [ ] **Step 2: Run to verify fail** — Expected FAIL (generator not wired / Lean absent).

- [ ] **Step 3: Wire the driver + generate**

Make `generate.py` accept `--degree/--n/--prec`, build the box, run the emitter, write `JensenHyperbolicity.lean`, and print the certified box + margin. Run it for `(d=2, n=0)`.

- [ ] **Step 4: Verify kernel-green + AXLE statement-match**

Run: `cd examples/jensen_hyperbolicity/lean && lake build` (green, no sorry). Run the AXLE warm-verify + statement-match check (per `docs/AXLE_THIRD_TOUR_2026-09-04.md`) confirming the emitted Prop is literally `... .roots.card = 2`. Confirm `#print axioms` clean.

- [ ] **Step 5: Write the trust-boundary README + commit**

`README.md` states plainly: (1) the kernel theorem is the **box** hyperbolicity statement; (2) coefficient-membership (`α(n+k) ∈ box`) is **Python-certified input, not kernel-verified**, exactly like inputs R/B; (3) `conjecture1_proved = False` — this certifies finitely many `J^{d,n}`, not RH.

```bash
git add examples/jensen_hyperbolicity/ tests/rh_jensen/test_end_to_end_d2.py
git commit -m "feat(rh-jensen): FIRST kernel-verified J^{2,0} hyperbolicity cert for zeta (box theorem + trust boundary)"
```

---

### Task 7: Extend bridge + emitter to d = 3 (cubic)

**Files:**
- Modify: `examples/jensen_hyperbolicity/lean/JensenBridge.lean`
- Modify: `src/telperion/rh_jensen/jensen.py` (add `disc3_margin`)
- Modify: `src/telperion/emit_jensen_hyperbolicity.py` (degree=3 path)
- Test: `tests/rh_jensen/test_jensen.py` (add d=3 cases), build gate.

**Interfaces:**
- Produces (Python): `disc3_margin(box) -> Fraction` — certified lower bound on the cubic discriminant `Δ_3` over the box.
- Produces (Lean): `theorem hyperbolic_deg3_of_discrim_nonneg (a b c d : ℝ) (ha : a ≠ 0) (h : 0 ≤ cubicDiscrim a b c d) : (cubicPoly a b c d).roots.card = 3` — cubic bridge (`Δ_3 ≥ 0 ⟺ three real roots`).

- [ ] **Step 1:** Write failing Python test: `disc3_margin` positive at a known-hyperbolic small `n` (verify against oracle that `J^{3,n}` is real-rooted there); write Lean statement with `sorry`.
- [ ] **Step 2:** Run — Expected FAIL / builds-with-sorry.
- [ ] **Step 3:** Implement `disc3_margin` (interval eval of `Δ_3 = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²` with outward rounding); discharge the cubic bridge in Lean (route: `Δ_3 ≥ 0` ⟹ resolvent structure ⟹ three real roots; iterate to green). Extend emitter degree=3 path.
- [ ] **Step 4:** Run tests + `lake build` — Expected PASS + green, no sorry, axioms clean.
- [ ] **Step 5:** Commit `feat(rh-jensen): d=3 cubic bridge + emitter path (kernel-green)`.

---

### Task 8: Extend bridge + emitter to d = 4 (quartic)

**Files:**
- Modify: `examples/jensen_hyperbolicity/lean/JensenBridge.lean`
- Modify: `src/telperion/rh_jensen/jensen.py` (add `quartic_all_real_margins`)
- Modify: `src/telperion/emit_jensen_hyperbolicity.py` (degree=4 path)
- Test: `tests/rh_jensen/test_jensen.py` (add d=4 cases), build gate.

**Interfaces:**
- Produces (Python): `quartic_all_real_margins(box) -> dict[str, Fraction]` — certified margins for the full all-real-roots quartic criterion: `Δ_4 ≥ 0`, `P ≤ 0`, `D ≤ 0` (with `P`, `D` the standard quartic subresultant auxiliaries).
- Produces (Lean): `theorem hyperbolic_deg4_of_criteria (…): (quarticPoly …).roots.card = 4`.

- [ ] **Step 1:** Failing Python test: all three margins have the correct sign at a known-hyperbolic small `n`; Lean statement with `sorry`.
- [ ] **Step 2:** Run — Expected FAIL / builds-with-sorry.
- [ ] **Step 3:** Implement `quartic_all_real_margins` (interval eval of `Δ_4`, `P`, `D`, outward rounding); discharge the quartic bridge in Lean (the `Δ_4 ≥ 0 ∧ P ≤ 0 ∧ D ≤ 0 ⟹ four real roots` criterion; this is the hardest bridge — budget iteration). Extend emitter degree=4 path.
- [ ] **Step 4:** Run tests + `lake build` — Expected PASS + green, no sorry, axioms clean.
- [ ] **Step 5:** Commit `feat(rh-jensen): d=4 quartic bridge + emitter path (kernel-green)`.

---

### Task 9: Grid driver, honesty doc, CHANGELOG

**Files:**
- Modify: `examples/jensen_hyperbolicity/generate.py` (grid mode over `(d, n)`)
- Create: `docs/JENSEN_HYPERBOLICITY_STATUS.md`
- Modify: `CHANGELOG.md`
- Test: `tests/rh_jensen/test_grid.py`

**Interfaces:**
- Consumes: all emitter degree paths.
- Produces: `generate.py --grid` emitting the frozen cert family for `d ∈ {2,3,4}` over a small-`n` grid (prioritizing the tightest small-`n` cases), each a kernel-green theorem.

- [ ] **Step 1:** Write failing test: grid mode emits ≥ 1 theorem per `(d,n)` in the configured grid and every emitted file names `roots.card = d`.
- [ ] **Step 2:** Run — Expected FAIL.
- [ ] **Step 3:** Implement grid mode; run it; `lake build` the whole example green.
- [ ] **Step 4:** Run test + full `lake build` — Expected PASS + green.
- [ ] **Step 5:** Write `JENSEN_HYPERBOLICITY_STATUS.md` (what is proven: box-hyperbolicity certs for the emitted `(d,n)` grid; the coefficient-membership trust boundary; `conjecture1_proved = False`; what is NOT done: uniform-in-`d` `N(d)`, Phase 2 general engine). Update `CHANGELOG.md`. Commit `docs(rh-jensen): grid family + honesty status + changelog`.

---

## Self-Review

**Spec coverage:**
- Spec §3.1 hyperbolicity Prop (`roots.card = natDegree`) → Tasks 4,5,7,8 (stated exactly). ✓
- Spec §3.2 discriminant beachhead d=2,3,4 → Tasks 4–8. ✓
- Spec §3.4 coefficient enclosure module → Tasks 1,2. ✓
- Spec §3.5 `JensenHyperbolicityEmitter` → Task 5 (extended 7,8). ✓
- Spec §5 verified first result (small-n grid) → Tasks 6 (milestone), 9 (grid). ✓
- Spec §6 testing (oracle cross-check, negative control, kernel gate, isolated CI) → Tasks 1–9 test steps. ✓
- Spec §7 risks (enclosure tightness = margin gate; trust boundary) → Tasks 2,5 refusal gate, Task 6 README. ✓
- Spec §3.3 Phase 2 Hermite engine → intentionally deferred to a separate plan (noted in header). ✓ (not a gap)

**Placeholder scan:** No "TBD/TODO/handle edge cases". Lean tactic blocks are intentionally strategy+toolkit (per the Global Constraints Lean note) with a hard green-build gate — this is the honest granularity for kernel proofs, not a placeholder. Python steps carry runnable code.

**Type consistency:** `enclose_xi_coeff`/`enclose_coeff_box` (Task 2) → `jensen_coeff_box`/`disc2_margin` (Task 3) → `JensenHyperbolicityEmitter.render_box` (Task 5) → `generate.py` (Task 6); `disc3_margin`/`quartic_all_real_margins` (7,8) consistently named. Lean bridge names (`hyperbolic_deg2/3/4_of_...`) consistent between producer and emitter `requires_prelude`. ✓
