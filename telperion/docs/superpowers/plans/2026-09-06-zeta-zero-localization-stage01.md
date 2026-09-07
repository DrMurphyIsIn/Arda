# Zeta Zero Localization — Stage 0 + Stage 1 + Stage-2 Probe — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce the first kernel-verified count of the Riemann completed-zeta (Λ) nontrivial zeros **on the critical line** in an interval — via real sign-changes of Λ(½+it) + IVT — and probe the feasibility of the Stage-2 argument-principle total-count.

**Architecture:** Stage 0 extends the Arb enclosure provider to complex values (Λ(½+it)). Stage 1 is a first-class emitter that, given certified real enclosures of Λ(½+it) at sample points with alternating signs, emits a Lean theorem "Λ has ≥ N zeros on the critical line in [a,b]" — proved by the (kernel-proven) fact that Λ(½+it) is real, plus IVT per sign-change interval. Enclosure membership is Arb-certified non-kernel input. Task 5 probes the Stage-2 winding-number kernel lemma on a toy polynomial.

**Tech Stack:** Python 3.14 (`fractions.Fraction`, `sympy`, `python-flint` Arb, `mpmath` oracle), Telperion emitter framework, Lean 4 + Mathlib v4.32.0 (`completedRiemannZeta`), `lake`, warm-verify.

**Spec:** `docs/superpowers/specs/2026-09-06-zeta-zero-localization-design.md`

## Global Constraints

- **Worktree:** `/Users/peterwmurphy/telperion-zeroloc`, branch `rh/zeta-zero-localization` (off `origin/main`). Do NOT switch branches or touch other worktrees.
- **Python invocation:** from `/Users/peterwmurphy/telperion-zeroloc/telperion`, use `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest …` (3.14.6; python-flint 0.9.0, mpmath 1.3.0, sympy 1.14.0). Bare `python`/`pytest` do NOT work.
- **Object of study = `completedRiemannZeta` (Λ).** Λ's zeros are exactly the nontrivial zeros of ζ (the Γ factor cancels the trivial zeros). Λ(s) = π^{−s/2}·Γ(s/2)·ζ(s); it has simple poles only at s=0 and s=1 (both off the critical line). Build Λ from `acb` as `acb.pi()**(−s/2) * (s/2).gamma() * s.zeta()`.
- **Certificate path exact-rational only** (`Fraction`); `float`/`mpmath`/`flint` only in enclosure computation + test oracles, never in emitted Lean literals.
- **Trust boundary:** enclosure *membership* (true Λ(½+it_i) ∈ box_i) is a documented **non-kernel input** (Arb-certified), carried as Lean *hypotheses*; the kernel proves the *implication* (enclosures + alternating signs ⟹ zeros). `conjecture1_proved = False` on every artifact.
- **First-class emitter pattern** (see `src/telperion/emit_hyperbolicity.py` / `emit_box_robust.py`): dataclass + `certify_<kind>_point` (raises to refuse) + `<Name>Emitter` with `__post_init__` `self.kind` + `emit_body` + `<kind>_family` + register in `certify.py` `_SPECIAL_KINDS`/`_SPECIAL_DISPATCH` + export from `__init__.py`.
- **Lean = local warm verify:** copy `lean-toolchain`+`lakefile.toml`+`lake-manifest.json` from `examples/dvp_atoms/lean` (or another Mathlib example on main), run `/Users/peterwmurphy/.elan/bin/lake exe cache get` FIRST (downloads oleans — SoC-safe), then `lake build`. NEVER a from-scratch Mathlib compile.
- **Kernel bar:** emitted/prelude Lean builds sorry-free, axioms ⊆ `{propext, Classical.choice, Quot.sound}`. Statement-match gate on emitted theorems.
- **No emoji.** Lean-tactic note: exact statements + Mathlib toolkit given; tactic blocks developed against the kernel; a task is done only on a green `lake build`.

---

### Task 1: Stage 0 — complex Arb enclosure of Λ (and general acb)

**Files:**
- Modify: `src/telperion/arb_enclosure.py` (add complex enclosure)
- Test: `tests/test_arb_complex.py`

**Interfaces:**
- Produces: `enclose_acb(spec_or_callable, prec_bits) -> tuple[tuple[Fraction,Fraction], tuple[Fraction,Fraction]]` — rigorous outward-rounded rational boxes `((lo_re,hi_re),(lo_im,hi_im))` for the real and imaginary parts of an `acb` value. Reuse the existing `_arb_ball_to_fractions` on `acb.real` and `acb.imag`.
- Produces: `enclose_lambda(s_re, s_im, prec_bits) -> tuple[tuple[Fraction,Fraction],tuple[Fraction,Fraction]]` — encloses Λ(s) at s = s_re + i·s_im via `acb.pi()**(-s/2) * (s/2).gamma() * s.zeta()`.

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_arb_complex.py
from fractions import Fraction
import mpmath
from telperion.arb_enclosure import enclose_acb, enclose_lambda

def _c(box, val):  # val real float, box=(lo,hi)
    return float(box[0]) <= val <= float(box[1])

def _lambda_oracle(sre, sim):
    mpmath.mp.dps = 60
    s = mpmath.mpf(str(sre)) + 1j*mpmath.mpf(str(sim))
    return mpmath.power(mpmath.pi, -s/2) * mpmath.gamma(s/2) * mpmath.zeta(s)

def test_lambda_on_line_is_real_and_encloses_oracle():
    # Lambda(1/2 + i*14) : known to be near a zero region; imag part must be ~0
    (lo_re,hi_re),(lo_im,hi_im) = enclose_lambda(Fraction(1,2), 14, prec_bits=300)
    o = _lambda_oracle(0.5, 14)
    assert _c((lo_re,hi_re), float(o.real))
    assert lo_im <= 0 <= hi_im   # imaginary part boxes zero on the line
    assert _c((lo_im,hi_im), float(o.imag))

def test_complex_point_encloses_oracle():
    (lo_re,hi_re),(lo_im,hi_im) = enclose_lambda(Fraction(3,5), 20, prec_bits=300)
    o = _lambda_oracle(0.6, 20)
    assert _c((lo_re,hi_re), float(o.real)) and _c((lo_im,hi_im), float(o.imag))

def test_width_shrinks_with_precision():
    b1 = enclose_lambda(Fraction(1,2), 14, prec_bits=120)
    b2 = enclose_lambda(Fraction(1,2), 14, prec_bits=300)
    assert (b2[0][1]-b2[0][0]) < (b1[0][1]-b1[0][0])

def test_returns_fractions():
    (lo_re,hi_re),(lo_im,hi_im) = enclose_lambda(Fraction(1,2), 21, prec_bits=200)
    assert all(isinstance(x, Fraction) for x in (lo_re,hi_re,lo_im,hi_im))
```

- [ ] **Step 2: Run to verify fail** — `PYTHONPATH=src …python3 -m pytest tests/test_arb_complex.py -v` → FAIL (ImportError).

- [ ] **Step 3: Implement** in `arb_enclosure.py`:
  - `enclose_acb`: eval the acb (set `flint.ctx.prec = prec_bits`, save/restore), return `(_arb_ball_to_fractions(a.real), _arb_ball_to_fractions(a.imag))`.
  - `enclose_lambda(s_re, s_im, prec_bits)`: `s = acb(str(s_re)) + acb(0, str(s_im))`; `lam = acb.pi()**(-s/2) * (s/2).gamma() * s.zeta()`; return `enclose_acb`-style boxes for `lam`. (Verify the flint `acb` power/gamma/zeta API with a quick `-c` probe.)
  - Outward rounding via the existing exact-dyadic path; endpoints `Fraction`. Docstring: complex enclosure; Λ zeros = nontrivial ζ zeros; membership is documented non-kernel input; `conjecture1_proved = False`.

- [ ] **Step 4: Run to verify pass** — pytest green. If `test_lambda_on_line_is_real_and_encloses_oracle` fails on the imag box not containing 0, raise prec_bits (on the line the true imag is 0, so the box must contain 0 for adequate precision).

- [ ] **Step 5: Commit**

```bash
git add src/telperion/arb_enclosure.py tests/test_arb_complex.py
git commit -m "feat(zeroloc): complex Arb enclosure of completed-zeta Lambda (Stage 0)"
```

---

### Task 2: Λ-real-on-the-critical-line Lean lemma (the analytic sub-lemma)

**Files:**
- Create: `examples/zeta_zero_localization/lean/{lakefile.toml,lean-toolchain,lake-manifest.json}` (copy from `examples/dvp_atoms/lean`), `examples/zeta_zero_localization/lean/LambdaLineReal.lean`

**Interfaces:**
- Produces (Lean): `theorem completedZeta_im_eq_zero (t : ℝ) : (completedRiemannZeta (1/2 + t * Complex.I)).im = 0`.

- [ ] **Step 1: Check Mathlib support (grep the cached oleans' source).** After `lake exe cache get`, grep `.lake/packages/mathlib` for: `completedRiemannZeta_one_sub` (functional equation Λ(1-s)=Λ(s)), a conjugation lemma (`completedRiemannZeta_conj` or `starRingEnd`/`conj` symmetry), and any existing real-on-line statement. Record what exists. (Mathlib is expected to have the functional equation; conj-symmetry may need deriving.)

- [ ] **Step 2: State the theorem with `sorry`; set up the example dir + `lake exe cache get` + `lake build` (builds with sorry warning — confirms wiring).**

- [ ] **Step 3: Discharge.** Strategy: show `conj (completedRiemannZeta s) = completedRiemannZeta (conj s)` (Λ has real Dirichlet/Mellin coefficients; if not a direct Mathlib lemma, derive from `completedRiemannZeta` real on the real axis + `Complex.conj` analyticity, or from the series). Then at s = ½ + t·I: `conj s = ½ − t·I = 1 − s`, so `conj (Λ s) = Λ (conj s) = Λ (1 − s) = Λ s` (functional equation). Hence `Λ s` is fixed by conj ⟹ `(Λ s).im = 0`. Iterate tactics to green.
  - If conj-symmetry is genuinely unavailable and hard, report BLOCKED with the exact Mathlib gap — the controller will adjudicate (fallback: the Hardy Z-function route, or documenting Λ-real-on-line as an additional non-kernel input with a clear honesty note; do NOT fake the proof).

- [ ] **Step 4: Verify green + clean axioms.** `lake build` green; `grep -c sorry LambdaLineReal.lean` → 0; `#print axioms completedZeta_im_eq_zero` shows only `{propext, Classical.choice, Quot.sound}`.

- [ ] **Step 5: Commit** `feat(zeroloc): Lambda(1/2+it) is real -- kernel lemma (Stage 1 prelude)`.

---

### Task 3: `xi_line_zeros` emitter — sign-change zero count (Stage 1 core)

**Files:**
- Create: `src/telperion/emit_xi_line_zeros.py`
- Modify: `src/telperion/certify.py` (register `"xi_line_zeros"`), `src/telperion/__init__.py` (export)
- Create: `examples/zeta_zero_localization/generate.py`, emitted `examples/zeta_zero_localization/lean/XiLineZeros.lean`
- Test: `tests/test_xi_line_zeros.py`

**Interfaces:**
- Consumes: `enclose_lambda` (Task 1) for the real boxes; `completedZeta_im_eq_zero` (Task 2) in the emitted proof; `statement_match` gate; `box_robust`/`norm_num` for the rational sign facts.
- Produces: `xi_line_zeros_family(name, symbols, grid, lean_name, spec)` where `spec(pt) -> (a, b, samples)` with `samples = [(t_i (Fraction), (lo_i,hi_i) (Fraction real box for Λ(1/2+it_i)))]`.
- Produces: `sign_change_count(samples) -> int` (count of consecutive all-negative→all-positive or all-positive→all-negative box transitions).
- Produces (Lean): a theorem asserting **≥ N zeros of Λ on the critical line in [a,b]**, of the form: given the enclosure hypotheses `(completedRiemannZeta (1/2 + t_i*I)).re ∈ [lo_i,hi_i]` and the alternating signs, `∃` N distinct t in (a,b) with `completedRiemannZeta (1/2 + t*I) = 0`. (Encode "≥ N" as N explicit disjoint sign-change subintervals each yielding a root; or as a lower bound on `(Λ-zero-set ∩ line ∩ [a,b]).ncard`. Pick the cleaner encoding and state it exactly.)

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_xi_line_zeros.py
from fractions import Fraction as F
from telperion.emit_xi_line_zeros import sign_change_count, XiLineZerosEmitter, xi_line_zeros_family
from telperion import certify

def test_sign_change_count_counts_alternations():
    # boxes: +, +, -, +  -> 2 sign changes (+ to -, - to +)
    samples = [(F(10),(F(1),F(2))),(F(11),(F(1),F(2))),(F(12),(F(-2),F(-1))),(F(13),(F(1),F(2)))]
    assert sign_change_count(samples) == 2

def test_refuses_when_no_valid_alternation():
    # all positive -> 0 changes; certify must refuse (nothing to prove)
    import pytest
    fam = xi_line_zeros_family("Z",(),_grid_one(), lambda pt:"z0",
        lambda pt:(F(10),F(13),[(F(10),(F(1),F(2))),(F(11),(F(1),F(2)))]))
    with pytest.raises(Exception):
        certify(fam)

def test_emit_produces_zero_existence_theorem():
    fam = xi_line_zeros_family("Z",(),_grid_one(), lambda pt:"z_demo",
        lambda pt:(F(10),F(13),[(F(10),(F(1),F(2))),(F(12),(F(-2),F(-1))),(F(13),(F(1),F(2)))]))
    text,n = XiLineZerosEmitter().emit_body(certify(fam), _profile())
    assert n == 1 and "completedRiemannZeta" in text and "= 0" in text
```
(`_grid_one`/`_profile` copied from an existing example's generate.py.)

- [ ] **Step 2: Run to verify fail** — FAIL (ImportError).

- [ ] **Step 3: Implement** `emit_xi_line_zeros.py`:
  - `sign_change_count`: a box is "positive" if `lo > 0`, "negative" if `hi < 0`, else "straddling" (ignored for sign purposes). Count transitions positive↔negative between consecutive *sign-definite* boxes.
  - `certify_xi_line_zeros_point`: build samples via the family spec; require ≥ 1 sign change (else `ValueError` refuse); store the sign-change subintervals and their box data.
  - `emit_body`: emit the theorem. Proof skeleton: define `g t := (completedRiemannZeta (1/2 + t*I)).re`; `g` is continuous on [a,b] (completedRiemannZeta continuous off {0,1}; the segment avoids them); by `completedZeta_im_eq_zero`, `completedRiemannZeta (1/2+t*I) = g t` (real). For each sign-change interval `[t_i,t_{i+1}]` with `g t_i ≤ hi_i < 0` and `g t_{i+1} ≥ lo_{i+1} > 0` (from the enclosure hypotheses + rational norm_num sign facts), `intermediate_value_Icc` gives `t* ∈ (t_i,t_{i+1})` with `g t* = 0`, hence `completedRiemannZeta (1/2+t*·I) = 0`. Distinctness from disjoint intervals. The enclosure hypotheses `g t_i ∈ [lo_i,hi_i]` are theorem hypotheses (the non-kernel input). Append the `statement_match` gate.
  - Register `"xi_line_zeros"` in certify.py + export from `__init__.py`.

- [ ] **Step 4: Python tests pass** — pytest green.

- [ ] **Step 5: Example + WARM BUILD.** `generate.py` emits one instance for a small demo interval using `enclose_lambda` at samples straddling a KNOWN zero (t≈14.13 — pick samples t=14 and t=15 whose Λ boxes have opposite signs) into `XiLineZeros.lean` (imports `LambdaLineReal`). `lake exe cache get` + `lake build` → green, sorry-free, axioms clean, gate compiles.

- [ ] **Step 6: Commit**

```bash
git add src/telperion/emit_xi_line_zeros.py src/telperion/certify.py src/telperion/__init__.py examples/zeta_zero_localization/ tests/test_xi_line_zeros.py
git commit -m "feat(zeroloc): xi_line_zeros emitter -- kernel-verified on-line zero count via sign changes + IVT (Stage 1)"
```

---

### Task 4: End-to-end on known zeros + status doc + CI (MILESTONE)

**Files:**
- Modify: `examples/zeta_zero_localization/generate.py` (interval driver), emitted `XiLineZeros.lean` (frozen)
- Create: `examples/zeta_zero_localization/README.md`, `docs/ZETA_ZERO_LOCALIZATION_STATUS.md`
- Modify: `.github/workflows/telperion-lean-e2e.yml` (add `zeta-zero-localization-compiles` job), `CHANGELOG.md`
- Test: `tests/test_zeroloc_end_to_end.py`

**Interfaces:** consumes Task 1/2/3.

- [ ] **Step 1: Write the failing test**

```python
# tests/test_zeroloc_end_to_end.py
from telperion.emit_xi_line_zeros import sign_change_count
from telperion.arb_enclosure import enclose_lambda
from fractions import Fraction as F

def test_sign_changes_match_known_zero_count_10_to_35():
    # First nontrivial zeros (imag parts): 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.
    # Sample densely on [10,35]; sign-change count must be >= 5 (the 5 known zeros in range).
    ts = [F(i,2) for i in range(20, 71)]  # t = 10.0, 10.5, ..., 35.0
    samples = []
    for t in ts:
        (lo_re,hi_re),_ = enclose_lambda(F(1,2), t, prec_bits=300)
        samples.append((t,(lo_re,hi_re)))
    assert sign_change_count(samples) >= 5
```

- [ ] **Step 2: Run to verify fail** — FAIL (until sampling/enclosure wired; expected initially).

- [ ] **Step 3: Extend `generate.py`** to accept `--a --b --n-samples --prec`, enclose Λ(½+it) at the samples, emit the on-line-zero-count theorem for the interval, and print the certified N. Regenerate `XiLineZeros.lean` for a real interval (e.g. [10,35]).

- [ ] **Step 4: Verify** — the Python test passes (sign-change count ≥ known zeros); warm `lake build` green, sorry-free, axioms clean, statement-match gate compiles; `#print axioms` clean.

- [ ] **Step 5: Docs + CI + commit.** `README.md` + `ZETA_ZERO_LOCALIZATION_STATUS.md`: what is kernel-proven (Λ has ≥ N zeros on Re=½ in the interval), the Arb-certified non-kernel-input boundary, `conjecture1_proved = False` (verifies, not proves RH; a lower bound via odd sign-changes; Stages 2–3 deferred pending the probe). Add the CI job (matching the existing per-example pattern; `pip install sympy pytest mpmath "python-flint==0.9.0"`; `generate.py --check`; cache get; build). Update `CHANGELOG.md`. Commit `feat(zeroloc): first kernel-verified on-line nontrivial-zero count for zeta + status/CI (MILESTONE)`.

---

### Task 5: Stage-2 feasibility probe — winding-number kernel lemma on a toy

**Files:**
- Create: `examples/zeta_zero_localization/lean/WindingProbe.lean` (toy attempt; may carry `sorry` if NO-GO)
- Create: `docs/ZEROLOC_STAGE2_PROBE.md` (findings)

**Interfaces:** none downstream (this is a gated probe; its output is a GO/NO-GO recommendation).

- [ ] **Step 1: Survey Mathlib.** Grep `.lake/packages/mathlib` for the argument-principle / zero-count API: `Complex.circleIntegral`, `ValueDistribution`/`LogCounting`, `Polynomial.roots`/`AnalyticOn` winding, `Complex.card_roots`/argument-principle statements. Read the two most relevant files; record what's available for "boundary data ⟹ interior zero count."

- [ ] **Step 2: Toy attempt.** In `WindingProbe.lean`, attempt the lemma for a KNOWN toy: e.g. `f z = z^2 - 1` (2 zeros ±1 in the unit disk of radius 2). State "the number of zeros of f in `closedBall 0 2` = 2" and try to prove it via whatever Mathlib argument-principle/root-count machinery exists (for a polynomial this may reduce to `Polynomial.roots`; for the GENERAL analytic winding certificate, attempt the reduction from a finite boundary-enclosure winding condition). Iterate against `lake build`.

- [ ] **Step 3: Verdict.** Write `ZEROLOC_STAGE2_PROBE.md`: GO (the winding→zero-count kernel lemma is assemblable from Mathlib — sketch the path + effort estimate) or NO-GO (name the exact Mathlib gap / what would need formalizing). If the toy proof closes sorry-free, note it; if not, the findings are the deliverable (a `sorry` in `WindingProbe.lean` is acceptable here ONLY as a probe artifact, clearly labeled, NOT wired into any CI build target).

- [ ] **Step 4: Commit** `docs(zeroloc): Stage-2 argument-principle feasibility probe (GO/NO-GO findings)`.

---

## Self-Review

**Spec coverage:** Stage 0 complex enclosure → Task 1 ✓. Λ-real-on-line prelude → Task 2 ✓. Stage 1 sign-change emitter → Task 3 ✓. First-deliverable milestone on known zeros + honest status + CI → Task 4 ✓. Stage-2 feasibility probe → Task 5 ✓. Trust boundary (enclosure = non-kernel input, carried as hypotheses) → Tasks 1,3 docstrings + Task 4 status ✓. Honest ceiling (`conjecture1_proved = False`, verifies-not-proves) → Tasks 1,3,4 ✓. Stages 2–3 proper are gated (Task 5 output), not built here → consistent with the spec's scope ✓.

**Placeholder scan:** Python steps carry runnable code; Lean steps carry exact statements + Mathlib toolkit + a hard warm-build gate (the honest granularity for kernel proofs). Task 2 explicitly allows a BLOCKED report if the conj-symmetry lemma is a genuine Mathlib gap (not a placeholder — a real escalation path). Task 5's `sorry` is explicitly a probe artifact, unwired from CI.

**Type consistency:** `enclose_lambda`/`enclose_acb` (T1) → consumed by T3/T4 sampling; `completedZeta_im_eq_zero` (T2) consistent between the prelude and the emitted proof's use; `sign_change_count`/`xi_line_zeros_family`/`XiLineZerosEmitter` (T3) → consumed by T4; the emitted theorem's enclosure-hypothesis form is consistent between T3 (definition) and T4 (instantiation). Registration edits (`_SPECIAL_KINDS`, `_SPECIAL_DISPATCH`, `__init__`) named consistently.
