# RH-in-a-Box (Stage 2 + Stage 3) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Kernel-verify that all nontrivial zeros of ζ inside one concrete box lie on the critical line (RH-in-a-box), via a discrete-winding total-count certificate composed with the merged argument-principle atoms and Stage 1's on-line count.

**Architecture:** Build a `winding_count` emitter that reads a concrete integer winding N off Stage-0 boundary enclosures of Λ (2A). Compose the merged atoms (`box_residue_sum`, `rect_winding_shifted`, `rect_argument_principle`) at box B, taking Λ's Blaschke split `Λ'/Λ = Σ divisor/(z−ρ) + E` and `E holomorphic` as hypotheses, to prove total zeros in B = N (2C). Compose with Stage 1's `≥ N_line` on-line count into the localization capstone `N_line = N ⟹ all zeros in B simple + on Re=½` (Stage 3), end-to-end on the [10,35] box. Finally DISCHARGE the split hypothesis by deriving Λ's local Blaschke split with E holomorphic on cl(B) (2B), gated by a feasibility probe. The capstone is reachable at Task 6 with the split as a documented hypothesis (same trust boundary as Stage 1); Task 7 upgrades it to a kernel-derived split.

**Tech Stack:** Python 3.14 (Telperion emitters, sympy, python-flint/Arb, mpmath), Lean 4 + Mathlib (kernel verification), first-class Telperion emitter pattern.

**Spec:** `telperion/docs/superpowers/specs/2026-09-06-zeta-box-localization-stage23-design.md`

## Global Constraints

- Object is `completedRiemannZeta` (Λ), NOT raw ζ. Λ's zeros = nontrivial ζ zeros; Λ real on Re=½; holomorphic away from s=0,1.
- Box B = rational `[σ0,σ1] × [T0,T1]`, `0 < σ0 < 1/2 < σ1 < 1`, `T0 > 0`. Corners rational (exact literals). Concrete capstone box: `[2/5, 3/5] × [10, 35]`.
- Enclosure membership (Λ values in rational boxes) is a documented NON-KERNEL input (Arb ball arithmetic), carried as Lean theorem HYPOTHESES. The kernel proves only implications. `conjecture1_proved = False` in every artifact.
- No emoji anywhere in code (QuantConnect + user global rule).
- Python invocation: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3` (3.14.6; flint 0.9.0, mpmath 1.3.0, sympy 1.14.0). Run from `.../telperion`.
- Lean: `/Users/peterwmurphy/.elan/bin/lake`. Local builds are operator-confirmed safe (2026-09-04); ALWAYS `lake exe cache get` before `lake build`; NEVER a cold Mathlib compile.
- First-class emitter pattern (mirror `emit_xi_line_zeros.py`): dataclass certificate + `certify_<kind>_point` (RAISES to refuse = negative control) + `<Name>Emitter(Emitter)` with `__post_init__` setting `self.kind` + `emit_body` + `<kind>_family` with `special=(kind, spec)`. FIVE registration points: `certify.py` `_SPECIAL_KINDS` + `_SPECIAL_DISPATCH`, `__init__.py` export, `emitter_sensitivity.py` stance (`STRUCTURALLY_NONVACUOUS`), and a `test_certificate_sensitivity`-passing entry.
- Every emitted theorem carries the `statement_match` gate (emit `example : <type> := <name>`).
- Merged atoms available on `origin/main` (import via the `dvp_geom_atoms` example, namespaces `RectWinding`, `BoxResidueSum`, `RectArgumentPrinciple`; disk Blaschke split `DlvpBlaschkeSplitExpand.logDeriv_eq_herglotz_add_entire`).
- Acceptance for every Lean deliverable: sorry-free, `#print axioms` = `{propext, Classical.choice, Quot.sound}` (no `sorryAx`), no `set_option linter.unusedVariables false`, drift-clean (`generate.py --check`).

---

### Task 1: Stage 2B feasibility probe (Λ local Blaschke split)

**Files:**
- Create: `telperion/docs/ZETA_BOX_STAGE2B_PROBE.md` (findings)
- Create (throwaway, may carry a LABELED sorry, NOT CI-wired): `telperion/examples/zeta_zero_localization/lean/BlaschkeBoxProbe.lean`

**Interfaces:**
- Consumes: `DlvpBlaschkeSplitExpand.logDeriv_eq_herglotz_add_entire` (in-repo, `ball 0 R`); Mathlib `MeromorphicOn.divisor`, `MeromorphicNFAt`, `MeromorphicOn`.
- Produces: a GO/NO-GO verdict + the exact Mathlib lemma path for Task 7 (or the NO-GO hypothesis-carrying fallback).

**Goal of the probe:** determine whether `Λ'/Λ z = Σ_{ρ ∈ B} (divisor Λ ρ)/(z−ρ) + E z` with **E holomorphic on cl(B)** is derivable, either by (i) Mathlib's `MeromorphicOn.divisor` giving "logDeriv minus its divisor principal parts is holomorphic on a compact region" directly, or (ii) re-centering/re-regioning the in-repo `logDeriv_eq_herglotz_add_entire` (which is at `ball 0 R`, center 0) to a region containing B. This is the `logDeriv_shift_center` gap the Stage-1 probe named.

- [ ] **Step 1: Read the in-repo disk split and Mathlib divisor API.** Read `telperion/examples/zero_free_bridge/lean/DlvpBlaschkeSplitExpand.lean` (and its dependency `DlvpBlaschkeSplit`, `DlvpCanonicalLogDeriv`). In Mathlib, locate: `MeromorphicOn.divisor`, `MeromorphicOn` on a set, `MeromorphicNFAt`, and any "logDeriv has simple poles at divisor support with residue = order" result (search `Mathlib/Analysis/Meromorphic/` and `Mathlib/Analysis/SpecialFunctions/Complex/`). Record exact lemma names + signatures.

- [ ] **Step 2: Attempt the toy reduction.** On a rational function `f z = (z − a)^2 · (z − b) / (z − c)` with known zeros/poles, attempt in `BlaschkeBoxProbe.lean` to prove `f'/f = Σ_ρ (order ρ)/(z − ρ) + E` with E holomorphic on a box avoiding a,b,c-complements. Use a LABELED `sorry` only where a genuine Mathlib gap blocks. Do NOT wire this file into any lakefile target (verify: not in `defaultTargets`, not imported).

- [ ] **Step 3: Decide GO / NO-GO and write the findings.** Write `ZETA_BOX_STAGE2B_PROBE.md`: verdict (GO if the E-holomorphicity path is concrete and bounded; NO-GO if it requires unbuilt Mathlib machinery), the exact lemma chain for Task 7, the re-centering approach (ball 0 R → region ⊇ B, or a direct box statement), the effort estimate, and the NO-GO fallback (carry the split + E-holomorphicity as documented non-kernel hypotheses). Include `conjecture1_proved = False`.

- [ ] **Step 4: Commit.**
```bash
git add telperion/docs/ZETA_BOX_STAGE2B_PROBE.md telperion/examples/zeta_zero_localization/lean/BlaschkeBoxProbe.lean
git commit -m "docs(zeroloc): Stage-2B local Blaschke split feasibility probe (GO/NO-GO)"
```

**Acceptance:** findings doc with a clear verdict + concrete lemma path (GO) or named obstruction + fallback (NO-GO); probe Lean file NOT CI-wired; `conjecture1_proved = False`.

---

### Task 2: Stage 0 boundary enclosure sampler

**Files:**
- Modify: `telperion/src/telperion/arb_enclosure.py` (add `enclose_lambda_boundary`)
- Test: `telperion/tests/test_arb_complex.py` (add cases)

**Interfaces:**
- Consumes: existing `enclose_lambda(s_re, s_im, prec_bits) -> ((lo_re,hi_re),(lo_im,hi_im))`.
- Produces: `enclose_lambda_boundary(box, n_per_side, prec_bits) -> list[tuple[Fraction, tuple[tuple[Fraction,Fraction], tuple[Fraction,Fraction]]]]` — an ordered CCW cycle of `(param, complex_box)` pairs around ∂B, where `box = (sigma0, sigma1, T0, T1)` are Fractions/ints/strs and each `complex_box = ((lo_re,hi_re),(lo_im,hi_im))` encloses Λ at that boundary point. First and last points coincide (closed cycle).

- [ ] **Step 1: Write the failing test.**
```python
def test_enclose_lambda_boundary_is_closed_cycle_off_zero():
    from fractions import Fraction
    from telperion.arb_enclosure import enclose_lambda_boundary
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    samples = enclose_lambda_boundary(box, n_per_side=4, prec_bits=300)
    # CCW cycle: 4 corners x 4 per side = 16 points + closing repeat
    assert len(samples) == 16 + 1
    # closed: first param==last coordinate-wise (same boundary point)
    assert samples[0][1] == samples[-1][1]
    # no enclosure box contains 0 (Lambda nonzero on this boundary): a box
    # contains 0 iff lo<=0<=hi for BOTH parts
    for _param, ((lo_re, hi_re), (lo_im, hi_im)) in samples[:-1]:
        contains_zero = (lo_re <= 0 <= hi_re) and (lo_im <= 0 <= hi_im)
        assert not contains_zero
```

- [ ] **Step 2: Run it to verify it fails.**
Run: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_arb_complex.py::test_enclose_lambda_boundary_is_closed_cycle_off_zero -v`
Expected: FAIL (function not defined).

- [ ] **Step 3: Implement `enclose_lambda_boundary`.** Traverse ∂B counter-clockwise: bottom edge (σ0→σ1 at T0), right edge (T0→T1 at σ1), top edge (σ1→σ0 at T1), left edge (T1→T0 at σ0), with `n_per_side` interior sample points per edge (exclude the shared corner from the next edge's start to avoid duplicates, then append the starting point once at the end to close). Each sample calls `enclose_lambda(re, im, prec_bits)`. Use a monotone rational parametrization `param in [0,1)` around the perimeter for ordering. Return the list; convert all coordinates to `Fraction`.

- [ ] **Step 4: Run the test to verify it passes.**
Run: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_arb_complex.py::test_enclose_lambda_boundary_is_closed_cycle_off_zero -v`
Expected: PASS.

- [ ] **Step 5: Add a precision-shrink + python-flint-guard test.**
```python
def test_enclose_lambda_boundary_requires_flint():
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_lambda_boundary((0, 1, 10, 11), 2, 100)
```

- [ ] **Step 6: Commit.**
```bash
git add telperion/src/telperion/arb_enclosure.py telperion/tests/test_arb_complex.py
git commit -m "feat(zeroloc): boundary-cycle Lambda enclosure sampler (Stage 0 for winding)"
```

**Acceptance:** returns an ordered closed CCW cycle of complex enclosures around ∂B; on the capstone box none contains 0; python-flint-absent guarded; Fraction-only.

---

### Task 3: winding_count numeric core (certificate + integer N + refusals)

**Files:**
- Create: `telperion/src/telperion/emit_winding_count.py` (certificate + numeric functions only in this task; emitter body in Task 4)
- Test: `telperion/tests/test_winding_count.py`

**Interfaces:**
- Consumes: the boundary-cycle format from Task 2 (`list[(param, ((lo_re,hi_re),(lo_im,hi_im)))]`).
- Produces:
  - `winding_number(samples) -> int` — the integer winding number of the enclosed curve about 0.
  - `_half_plane_witness(box_a, box_b) -> tuple | None` — for consecutive complex boxes, returns a rational witness (a direction from a fixed rational set, or a corner-based cross/dot-product sign pair) proving both boxes lie in a common open half-plane through 0 (so the argument change is < π); None if the step is too coarse.
  - `WindingCountCertificate` dataclass: `box` (4 Fractions), `n` (int winding), `step_witnesses` (tuple).
  - `winding_count_certificate(box, samples) -> WindingCountCertificate` — builds and self-checks; RAISES if any box contains 0 (Λ may vanish on ∂B) or any consecutive step lacks a half-plane witness (winding ambiguous).
  - `certify_winding_count_point(family, pt, name)`.

- [ ] **Step 1: Write failing tests (toy polynomials, known winding).**
```python
def _poly_boundary(box, n_per_side, poly):
    # exact rational complex boxes for poly on the box boundary (degenerate
    # width-0 boxes are fine for the toy: lo==hi==value)
    from fractions import Fraction
    ...  # traverse box like Task 2, evaluate poly at each corner as a point-box
    return samples

def test_winding_number_z_squared_is_two():
    # f(z)=z^2 on a box around 0 winds twice
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z*z)
    from telperion.emit_winding_count import winding_number
    assert winding_number(samples) == 2

def test_winding_number_zero_free_is_zero():
    # f(z)=z-10 on a box near 0 (10 not enclosed) winds zero times
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z - 10)
    from telperion.emit_winding_count import winding_number
    assert winding_number(samples) == 0

def test_winding_count_refuses_box_containing_zero():
    import pytest
    from telperion.emit_winding_count import winding_count_certificate
    box = (0, 1, 0, 1)
    bad = [(0, ((-1, 1), (-1, 1)))]  # straddles 0
    with pytest.raises(ValueError, match="contains 0|straddle"):
        winding_count_certificate(box, bad * 2)
```

- [ ] **Step 2: Run to verify failure.**
Run: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_winding_count.py -v`
Expected: FAIL (module missing).

- [ ] **Step 3: Implement the numeric core.** `winding_number`: accumulate the signed argument increment between consecutive box CENTERS (`atan2` on rational-center floats is fine for the integer result — the certificate's exactness lives in the half-plane witnesses, not this float sum), divide the total by 2π, round to nearest int. `_half_plane_witness`: test the fixed rational directions `{1, -1, i, -i, 1+i, 1-i, -1+i, -1-i}` — for each, check all four corners of BOTH boxes have strictly positive real inner product with that direction (exact Fraction arithmetic); return the first that works, else None. `winding_count_certificate`: RAISE if any box contains 0 (both parts straddle) or any consecutive pair returns None from `_half_plane_witness`; else store `n = winding_number(samples)` and the witnesses.

- [ ] **Step 4: Run tests to verify pass.**
Run: `PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_winding_count.py -v`
Expected: PASS.

- [ ] **Step 5: Commit.**
```bash
git add telperion/src/telperion/emit_winding_count.py telperion/tests/test_winding_count.py
git commit -m "feat(zeroloc): winding_count numeric core + refusals (toy-validated)"
```

**Acceptance:** `winding_number` matches known toy windings (z^2→2, zero-free→0); certificate RAISES on box-containing-0 and on missing half-plane witnesses (negative controls); exact Fraction witnesses.

---

### Task 4: winding_count emitter + kernel Lean proof

**Files:**
- Modify: `telperion/src/telperion/emit_winding_count.py` (add `WindingCountEmitter`, `winding_count_family`)
- Modify: `telperion/src/telperion/certify.py` (`_SPECIAL_KINDS` + `_SPECIAL_DISPATCH`)
- Modify: `telperion/src/telperion/__init__.py` (exports)
- Modify: `telperion/src/telperion/emitter_sensitivity.py` (stance)
- Create: `telperion/examples/zeta_zero_localization/lean/WindingCount.lean` (emitted; toy + Λ instances)
- Modify: `telperion/examples/zeta_zero_localization/generate.py` (emit winding count)
- Test: `telperion/tests/test_winding_count.py` (emit-shape + drift)

**Interfaces:**
- Consumes: `WindingCountCertificate` (Task 3), the boundary format (Task 2).
- Produces: emitted Lean theorem per instance:
  `winding_<name> : (hypotheses: Λ(p_i) ∈ W_i as re/im rational bounds; 0 ∉ W_i; per-step half-plane witnesses) → Bd_∂B(Λ'/Λ) = 2πi · N`, where `Bd_∂B(g)` is the four-segment boundary integral `∫bottom g − ∫top g + I•∫right g − I•∫left g`. Emitted with `statement_match` gate.
- `WindingCountEmitter.kind = "winding_count"`.

- [ ] **Step 1: Write the emit-shape test.**
```python
def test_winding_count_emits_boundary_integral_equals_2pi_i_N():
    from telperion.emit_winding_count import winding_count_family, WindingCountEmitter, certify_winding_count_point
    from telperion.family import GridSpec
    from telperion.lean import LeanProfile
    # toy: f(z)=z^2, N=2 on [-1,1]^2
    fam = winding_count_family("T", GridSpec([("case", [0])]),
        lean_name=lambda pt: "winding_z2", spec=lambda pt: {"box": (-1, 1, -1, 1), "samples": _z2_samples()})
    inst, _ = certify_winding_count_point(fam, {"case": 0}, "winding_z2")
    class V: instances=[inst]
    body, nthm = WindingCountEmitter().emit_body(V(), LeanProfile(namespace=("X",)))
    assert nthm == 1
    assert "2 * " in body and "π" in body and "* I" in body
    assert "clog_real" in body or "Complex.log" in body   # monodromy proof present
```

- [ ] **Step 2: Run to verify failure.** Run the test; expect FAIL (emitter class missing).

- [ ] **Step 3: Implement `WindingCountEmitter.emit_body` + `winding_count_family`.** Emit the theorem stated above. **Proof strategy (name the exact lemmas; RectWinding.lean is the template):** on each of the four boundary segments, `Λ'/Λ = (Complex.log ∘ Λ)'` where the principal branch is valid because the per-step half-plane witnesses keep consecutive Λ-values in a rotated slit plane; `intervalIntegral.integral_eq_sub_of_hasDerivAt` + `HasDerivAt.clog_real` collapse each segment to `log Λ(end) − log Λ(start)`; branch crossings between sub-samples are corrected by the monodromy jumps `RectWinding.log_neg_sub_im_neg` / `log_neg_sub_im_pos` (`log(−x) − log x = ±πi`); the per-step `< π` witnesses bound each correction so the telescoped four-segment sum is exactly `2πi·N`. The enclosure bounds (`Λ(p_i).re ∈ [lo,hi]`, etc.) enter as hypotheses closed by `norm_num` where a sign/half-plane fact is needed. Emit the `statement_match` gate.

- [ ] **Step 4: Register at all five points.** `certify.py`: add `"winding_count"` to `_SPECIAL_KINDS` and `_SPECIAL_DISPATCH` (`("emit_winding_count", "certify_winding_count_point", "WindingCountEmitter")`). `__init__.py`: export `WindingCountEmitter, winding_count_certificate, winding_count_family, certify_winding_count_point`. `emitter_sensitivity.py`: add `"WindingCountEmitter": _S(STRUCTURALLY_NONVACUOUS, "<reason: enclosure boxes are theorem hypotheses = documented Arb non-kernel input; monodromy/FTC telescoping over norm_num-closed half-plane witnesses; no separately-supplied witness. conjecture1_proved = False>")`.

- [ ] **Step 5: Wire generate.py + emit the toy instance and build it.** Add a `winding_count` case to `generate.py` emitting `WindingCount.lean` with the `z^2 → N=2` toy instance FIRST (validates the proof independent of Λ). Build locally:
```bash
cd telperion/examples/zeta_zero_localization/lean && /Users/peterwmurphy/.elan/bin/lake exe cache get && /Users/peterwmurphy/.elan/bin/lake build WindingCount
```
Expected: builds sorry-free. Then `#print axioms winding_z2` = `{propext, Classical.choice, Quot.sound}`.

- [ ] **Step 6: Add the Λ instance for the [10,35] box.** Extend `generate.py` to also emit the winding instance for box `[2/5,3/5]×[10,35]` from `enclose_lambda_boundary` (expected `N = 5`, matching Stage 1's 5 on-line zeros). Rebuild; confirm sorry-free + clean axioms. Assert in `generate.py --check` that the certified N equals 5.

- [ ] **Step 7: Add drift + registration tests, run the emitter suite.**
```bash
PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_winding_count.py tests/test_certificate_sensitivity.py -q
PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 examples/zeta_zero_localization/generate.py --check
```
Expected: all pass; `test_every_emitter_is_classified` green with `WindingCountEmitter` present.

- [ ] **Step 8: Commit.**
```bash
git add telperion/src/telperion/emit_winding_count.py telperion/src/telperion/certify.py telperion/src/telperion/__init__.py telperion/src/telperion/emitter_sensitivity.py telperion/examples/zeta_zero_localization/lean/WindingCount.lean telperion/examples/zeta_zero_localization/generate.py telperion/tests/test_winding_count.py
git commit -m "feat(zeroloc): winding_count emitter -- kernel-verified winding from enclosures (Stage 2A)"
```

**Acceptance:** `WindingCount.lean` builds sorry-free with clean axioms for BOTH the toy (N=2) and the Λ [10,35] instance (N=5); all five registration points present; `test_every_emitter_is_classified` green; drift-clean; negative controls (Task 3) intact.

---

### Task 5: Box argument-principle composition for Λ (Stage 2C, split as hypothesis)

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/BoxArgPrinciple.lean` (hand-written Lean, imports the merged atoms + WindingCount)
- Test: `telperion/tests/test_zeroloc_end_to_end.py` (build assertion)

**Interfaces:**
- Consumes: `RectWinding.rect_winding_shifted` (regenerated at box B corners via the `rect_winding` family), `BoxResidueSum.box_residue_sum_*` (regenerated at B), `RectArgumentPrinciple.rect_arg_principle_*` (regenerated at B), and `WindingCount`'s `Bd(Λ'/Λ) = 2πi·N`.
- Produces: `box_arg_principle_lambda` :
  given (H1) the split `∀ z ∈ ∂B, Λ'/Λ z = (∑ ρ ∈ zeros, (divisor ρ)/(z − ρ)) + E z` as a hypothesis,
  (H2) `DifferentiableOn ℂ E (Icc σ0 σ1 ×ℂ Icc T0 T1)`,
  (H3) each ρ ∈ zeros strictly inside B,
  (H4) `Bd(Λ'/Λ) = 2πi·N` (from WindingCount),
  concludes `(∑ ρ ∈ zeros, (divisor ρ : ℂ)) = N`.

- [ ] **Step 1: Regenerate the three atoms at box B corners.** Extend `generate.py` (or a helper) to emit `rect_winding`, `box_residue_sum`, `rect_argument_principle` instances at `[2/5,3/5]×[10,35]` into the `dvp_geom_atoms` example (or a local Lean file `BoxAtoms.lean` in the zeroloc example importing the same emitter output). Confirm they build locally with warm cache.

- [ ] **Step 2: Write the failing build test.**
```python
def test_box_arg_principle_lambda_builds():
    import subprocess, os
    env = {**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]}
    d = "examples/zeta_zero_localization/lean"
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(["lake", "build", "BoxArgPrinciple"], cwd=d, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
```

- [ ] **Step 2b: Run to verify failure.** Expect FAIL (file missing).

- [ ] **Step 3: Write `BoxArgPrinciple.lean`.** State `box_arg_principle_lambda` as in Interfaces. **Proof:** `Bd` is linear (`intervalIntegral.integral_add`/`integral_sub`, `smul`); rewrite `Bd(Λ'/Λ)` via H1 into `Bd(Σ divisor/(z−ρ)) + Bd(E)`; `Bd(E) = 0` by `rect_arg_principle_*` applied to H2; `Bd(Σ divisor/(z−ρ)) = 2πi·Σ divisor` by `box_residue_sum_*` with each `hwind` discharged by `rect_winding_shifted` (H3 gives the strict-interior side conditions); combine with H4 `Bd(Λ'/Λ) = 2πi·N` and cancel `2πi` (`Complex.two_pi_I_ne_zero` / `field_simp`) to get `Σ divisor = N`. The IntervalIntegrable side-hypotheses of `box_residue_sum` follow from `Continuous.intervalIntegrable` on the zero-free boundary (H3 keeps ρ off ∂B).

- [ ] **Step 4: Build + axiom check.**
```bash
cd telperion/examples/zeta_zero_localization/lean && /Users/peterwmurphy/.elan/bin/lake build BoxArgPrinciple
```
Expected: sorry-free; `#print axioms box_arg_principle_lambda` clean.

- [ ] **Step 5: Run the build test + commit.**
```bash
PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_zeroloc_end_to_end.py::test_box_arg_principle_lambda_builds -q
git add telperion/examples/zeta_zero_localization/lean/BoxArgPrinciple.lean telperion/examples/zeta_zero_localization/generate.py telperion/tests/test_zeroloc_end_to_end.py
git commit -m "feat(zeroloc): box argument principle for Lambda -- total count = winding N (Stage 2C)"
```

**Acceptance:** `box_arg_principle_lambda` builds sorry-free with clean axioms; the split + E-holomorphicity enter ONLY as explicit hypotheses (H1,H2); total count `Σ divisor = N` follows from the merged atoms + WindingCount.

---

### Task 6: RH-in-a-box localization capstone (Stage 3)

**Files:**
- Create: `telperion/src/telperion/emit_box_localization.py` (kind `box_localization`)
- Modify: `certify.py`, `__init__.py`, `emitter_sensitivity.py` (register)
- Create: `telperion/examples/zeta_zero_localization/lean/BoxLocalization.lean` (emitted)
- Modify: `telperion/examples/zeta_zero_localization/generate.py`, `telperion/docs/ZETA_ZERO_LOCALIZATION_STATUS.md`, `telperion/README.md`, `telperion/CHANGELOG.md`, `.github/workflows/telperion-lean-e2e.yml`
- Test: `telperion/tests/test_box_localization.py`

**Interfaces:**
- Consumes: `XiLineZeros` Stage-1 conclusion (`≥ N_line distinct on-line zeros in [T0,T1]`), `BoxArgPrinciple.box_arg_principle_lambda` (`Σ divisor = N`).
- Produces: emitted `box_localization_<name>` :
  given (A) Stage-1's `N_line` distinct on-line zeros in the segment, (B) `Σ_{ρ∈B} divisor Λ ρ = N` (Task 5), (C) `N_line = N`, and (D) each Stage-1 zero lies in B and `divisor ≥ 1` there,
  concludes `∀ ρ, ρ ∈ B → Λ ρ = 0 → ρ.re = 1/2` (and each such zero simple). `statement_match` gate.

- [ ] **Step 1: Write the emit-shape + refusal tests.**
```python
def test_box_localization_emits_all_zeros_on_line():
    from telperion.emit_box_localization import box_localization_family, BoxLocalizationEmitter, certify_box_localization_point
    ...  # build a family instance with n_line == n_total == 5
    body, nthm = BoxLocalizationEmitter().emit_body(V(), LeanProfile(namespace=("X",)))
    assert "re = 1 / 2" in body.replace(" ", " ")
    assert "2 * π * I" not in body  # capstone is real-geometry, integral already discharged

def test_box_localization_refuses_n_line_gt_n_total():
    import pytest
    from telperion.emit_box_localization import box_localization_certificate
    with pytest.raises(ValueError, match="N_line.*N_total|exceeds"):
        box_localization_certificate(n_line=6, n_total=5, ...)  # impossible; refuse
```

- [ ] **Step 2: Run to verify failure.** Expect FAIL (module missing).

- [ ] **Step 3: Implement `emit_box_localization.py`.** Certificate: `box`, `n_line`, `n_total`, refuses unless `n_line == n_total` (equality is the localization hypothesis) and `n_line >= 1`. `emit_body`: emit `box_localization_<name>` per Interfaces. **Proof:** the `N_line` distinct on-line zeros each contribute `≥ 1` to `Σ divisor` (D); since `Σ divisor = N = N_line` (B,C), there is no remaining multiplicity for any other zero in B, so any `ρ ∈ B` with `Λ ρ = 0` must be one of the `N_line` on-line simple zeros — hence `ρ.re = 1/2`. Formalize via a `Finset` cardinality/sum argument: `∑_{ρ∈zerosInB} divisor ρ = N_line` with the on-line zeros already summing to `N_line` and each `divisor ≥ 1`, forcing `zerosInB = {the N_line on-line zeros}`. Emit `statement_match` gate. Register at all five points (`STRUCTURALLY_NONVACUOUS` stance).

- [ ] **Step 4: Wire generate.py + emit the [10,35] capstone.** Emit `BoxLocalization.lean` for box `[2/5,3/5]×[10,35]` with `N_line = N_total = 5`. The emitted theorem's hypotheses (A: Stage-1 zeros; B: Task-5 count) are the load-bearing inputs; wire them to the actual `XiLineZeros.lambda_five_zeros_10_35` and `box_arg_principle_lambda` conclusions where the Lean allows direct reference, else carry as hypotheses.

- [ ] **Step 5: Build + axiom check.**
```bash
cd telperion/examples/zeta_zero_localization/lean && /Users/peterwmurphy/.elan/bin/lake build BoxLocalization
```
Expected: sorry-free; `#print axioms` clean.

- [ ] **Step 6: Negative control.** Add a `generate.py`/test check that a fabricated instance with an off-line zero making `n_total = 6 > n_line = 5` is REFUSED at certification (cannot emit a localization claim).

- [ ] **Step 7: Update docs + CI.** `ZETA_ZERO_LOCALIZATION_STATUS.md`: add the Stage 2/3 result (RH-in-a-box on [10,35], `conjecture1_proved = False`, split-as-hypothesis noted pending Task 7). `README.md` + `CHANGELOG.md`: one honest line each. Add a CI job `zeta-box-localization-compiles` (warm `lake exe cache get` then `lake build BoxArgPrinciple BoxLocalization WindingCount`); validate YAML.

- [ ] **Step 8: Run suites + commit.**
```bash
PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 -m pytest tests/test_box_localization.py tests/test_certificate_sensitivity.py tests/test_zeroloc_end_to_end.py -q
PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 examples/zeta_zero_localization/generate.py --check
git add -A telperion/ .github/
git commit -m "feat(zeroloc): RH-in-a-box localization capstone on [10,35] (Stage 3)"
```

**Acceptance:** `BoxLocalization.lean` builds sorry-free with clean axioms; capstone concludes all Λ-zeros in the [10,35] box are on Re=½; `n_line > n_total` and `n_line != n_total` refused; docs honest (`conjecture1_proved = False`); CI job valid; end-to-end `N_line = 5 = N`.

---

### Task 7: Discharge the Λ Blaschke-split hypothesis (Stage 2B)

**Files:**
- Create: `telperion/examples/zeta_zero_localization/lean/BlaschkeBox.lean` (the derived split + E holomorphic; GATED on Task 1 = GO)
- Modify: `telperion/examples/zeta_zero_localization/lean/BoxArgPrinciple.lean` (add a hypothesis-free corollary instantiating H1,H2 with the derived lemma)
- Modify: `telperion/docs/ZETA_ZERO_LOCALIZATION_STATUS.md` (record the split is now kernel-derived, or the NO-GO gap)
- Test: `telperion/tests/test_zeroloc_end_to_end.py`

**Interfaces:**
- Consumes: Task 1's lemma path; in-repo `logDeriv_eq_herglotz_add_entire`; Mathlib `MeromorphicOn.divisor`.
- Produces: `lambda_blaschke_split_box` : `∀ z ∈ (neighborhood of cl(B) minus zeros), Λ'/Λ z = (∑ ρ ∈ zerosInB, (divisor Λ ρ)/(z − ρ)) + E z` with `E` and the proof that `DifferentiableOn ℂ E (Icc σ0 σ1 ×ℂ Icc T0 T1)`; and a hypothesis-free `box_arg_principle_lambda'` / `box_localization'` corollary.

- [ ] **Step 1: Branch on Task 1's verdict (controller ruling).** If Task 1 = NO-GO: SKIP the derivation; instead update `ZETA_ZERO_LOCALIZATION_STATUS.md` to document the split + E-holomorphicity as a named non-kernel hypothesis (trust boundary identical to Stage 1's enclosures), record the Mathlib-capability gap, commit, and mark the task complete with that ruling. If GO: proceed.

- [ ] **Step 2 (GO): Write the failing build test.**
```python
def test_lambda_blaschke_split_box_builds():
    import subprocess, os
    env = {**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]}
    d = "examples/zeta_zero_localization/lean"
    r = subprocess.run(["lake", "build", "BlaschkeBox"], cwd=d, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
```

- [ ] **Step 3 (GO): Derive the split.** Follow Task 1's lemma path: instantiate/re-center `logDeriv_eq_herglotz_add_entire` (or Mathlib `MeromorphicOn.divisor`) so the divisor is over a region containing B; prove `E = Λ'/Λ − Σ divisor/(z−ρ)` is `DifferentiableOn` on `cl(B)` using that Λ is holomorphic and non-vanishing except at the finitely many zeros in B (pole at 1 and trivial zeros excluded by `T0 > 0`, `σ1 < 1`). If the `log_product_bound` atom (PR #267) is needed to bound the Herglotz tail for well-definedness, import and use it.

- [ ] **Step 4 (GO): Instantiate the capstone hypothesis-free.** In `BoxArgPrinciple.lean` add `box_arg_principle_lambda'` that discharges H1,H2 of `box_arg_principle_lambda` with `lambda_blaschke_split_box`; rebuild `BoxLocalization` against the hypothesis-free version. Confirm sorry-free + clean axioms end-to-end.

- [ ] **Step 5: Update STATUS + commit.**
```bash
cd telperion/examples/zeta_zero_localization/lean && /Users/peterwmurphy/.elan/bin/lake build BlaschkeBox BoxArgPrinciple BoxLocalization
git add -A telperion/
git commit -m "feat(zeroloc): kernel-derive Lambda local Blaschke split over box (Stage 2B); discharge capstone hypothesis"
```

**Acceptance (GO):** `BlaschkeBox.lean` builds sorry-free with clean axioms; the capstone no longer carries the split/E-holomorphicity as hypotheses; end-to-end RH-in-a-box on [10,35] is kernel-derived modulo only the Arb enclosures. **Acceptance (NO-GO):** the gap is documented as a named non-kernel hypothesis; `conjecture1_proved = False`; capstone stands with the split-as-hypothesis trust boundary.

---

## PLAN REVISION (2026-09-06, post-Task-4): rigorous route-beta winding

Task 4's `winding_lambda_five` proved to be the ANALYTIC residue-sum side (assumes 5 poles as a hypothesis) — a valid kernel-clean atom but NOT a from-data count. Jensen upper-bound was empirically REFUSED (Lambda's Gamma-factor exponential decay makes Jensen's log-modulus-variation bound useless for zeta zero-counting: box-disk bound 34.3, even empty small disks give 2.6-4.3). The user chose the UNCONDITIONAL RH-in-a-box via a rigorous argument-principle winding from SEGMENT enclosures. New tasks 8 and 9 supply the from-data count `Bd(Lambda'/Lambda) = 2*pi*i*5`; Task 5's H4 is sourced from Task 9 (not Task 4). Execution order for remaining work: **5, 8, 9, 7, 6.** Task 4's route-alpha atom stays in the tree as a valid atom, off the capstone critical path.

### Task 8: Segment (ball) enclosures + segment winding certificate for Lambda

**Files:**
- Modify: `telperion/src/telperion/arb_enclosure.py` (add `enclose_lambda_segments`)
- Modify: `telperion/src/telperion/emit_winding_count.py` (add a segment-winding certificate: `segment_winding_certificate` / reuse `_half_plane_witness` on segment boxes)
- Test: `telperion/tests/test_arb_complex.py`, `telperion/tests/test_winding_count.py`

**Interfaces:**
- Consumes: existing `enclose_acb`/`_eval_spec` (acb ball arithmetic) and `_half_plane_witness` (Task 3).
- Produces: `enclose_lambda_segments(box, n_per_side, prec_bits) -> list[tuple[Fraction, tuple[tuple[Fraction,Fraction],tuple[Fraction,Fraction]]]]` — an ordered CCW cycle of `(param, complex_box)` where each `complex_box` encloses `Lambda` over the WHOLE sub-segment between consecutive nodes (NOT a point): evaluate `Lambda` at an `acb` BALL centered at the sub-segment midpoint with radius >= half the sub-segment length, so acb ball arithmetic returns an enclosure of `Lambda(sub-segment)` as a set. Same closed-cycle format as `enclose_lambda_boundary`. Plus `segment_winding_certificate(box, segments)` that reuses the Task-3 refusals (RAISE on any segment-box containing 0, or any consecutive pair lacking a `_half_plane_witness`).

- [ ] **Step 1: Write failing tests.** (a) `enclose_lambda_segments` on the capstone box `[2/5,3/5]x[10,35]` returns a closed cycle whose segment-boxes are WIDER than the point-enclosures at the same nodes (a segment encloses a continuum, so its box strictly contains the endpoint value boxes); (b) for a fine-enough `n_per_side`, no segment-box contains 0 and every consecutive pair has a half-plane witness (so `segment_winding_certificate` succeeds and reports `n == 5`); (c) a deliberately-coarse `n_per_side` (e.g. 2) is REFUSED (a segment-box straddles 0 or a step lacks a witness). Use exact Fractions.

- [ ] **Step 2: Run to verify failure.** `PYTHONPATH=src ... -m pytest tests/test_arb_complex.py -k segments tests/test_winding_count.py -k segment -v` — FAIL (functions missing).

- [ ] **Step 3: Implement.** `enclose_lambda_segments`: same CCW traversal as `enclose_lambda_boundary`, but for each sub-segment between consecutive nodes, build an `acb` ball covering that sub-segment (midpoint +- half-length as the ball radius, plus a tiny margin) and call the Lambda spec on that ball via `enclose_acb`, extracting the outward-rounded rational complex box. `segment_winding_certificate`: reuse Task-3 `winding_number` (on segment-box centers) for the candidate `n`, and the Task-3 refusal logic (box-contains-0, per-step half-plane witness) on the segment boxes.

- [ ] **Step 4: Run tests to verify pass.** Same command — PASS. Confirm the capstone box yields `n == 5` with all segment-boxes off 0 and witnessed.

- [ ] **Step 5: Commit.**
```bash
git add telperion/src/telperion/arb_enclosure.py telperion/src/telperion/emit_winding_count.py telperion/tests/
git commit -m "feat(zeroloc): Lambda segment (ball) enclosures + segment winding certificate (rigorous route beta)"
```

**Acceptance:** `enclose_lambda_segments` encloses Lambda over sub-segments (boxes wider than point enclosures); the capstone box certifies `n=5` with no segment-box straddling 0 and every step witnessed; a coarse sampling is refused; Fraction-only; reuses `enclose_acb` and `_half_plane_witness`.

### Task 9: Rigorous winding Lean theorem — Bd(Lambda'/Lambda) = 2*pi*i*5 (the crux)

**Files:**
- Modify: `telperion/src/telperion/emit_winding_count.py` (emit a rigorous-winding theorem variant, or a new emitter kind `segment_winding`)
- Create: `telperion/examples/zeta_zero_localization/lean/RigorousWinding.lean` (emitted)
- Modify: `telperion/examples/zeta_zero_localization/generate.py`
- Test: `telperion/tests/test_winding_count.py`, build assertion in `test_zeroloc_end_to_end.py`

**Interfaces:**
- Consumes: Task 8's segment enclosures/certificate; `differentiableAt_completedZeta` (Mathlib, `RiemannZeta.lean:94`); `RectWinding.lean` monodromy lemmas as the template.
- Produces: `rigorous_winding_lambda_five` : GIVEN, per boundary sub-segment, the Arb-certified hypothesis `forall z on the sub-segment, Lambda z lies in the rational half-plane box W_i` (the documented non-kernel input, `0 notin W_i`), and `Lambda` analytic on a neighborhood of `partial B`, THEN `Bd(Lambda'/Lambda) = 2*pi*i*5`. This is the UNCONDITIONAL (modulo Arb) from-data winding.

- [ ] **Step 1: Write the emit-shape test.** The emitted theorem's conclusion is `Bd(Lambda'/Lambda) = 2*pi*i*5`; hypotheses are per-segment slit-plane-membership facts (NOT a residue-decomposition hypothesis — this is the from-data winding, distinct from Task 4's route-alpha). Assert the body references `differentiableAt_completedZeta` (or a Lambda-analyticity lemma), `clog`, and `integral_eq_sub_of_hasDerivAt`.

- [ ] **Step 2: Run to verify failure.**

- [ ] **Step 3: Implement the emitter + emit `RigorousWinding.lean`.** **Proof strategy (RectWinding.lean is the template):** on each sub-segment, `Lambda(sub-segment)` lies in a half-plane box (hypothesis) => in a ROTATED slit plane (rotate by the witness direction's angle: for a fixed rational direction `d`, `Lambda z` has strictly positive inner product with `d`, so `e^{-i*arg d} * Lambda z` is in the right half-plane => principal `Complex.log` of the rotated value is analytic); `Lambda'/Lambda = (Complex.log o Lambda)'` on the segment via `HasDerivAt.clog` composed with `differentiableAt_completedZeta` (Lambda analytic, nonzero from the off-0 box); `intervalIntegral.integral_eq_sub_of_hasDerivAt` collapses each sub-segment to `log Lambda(end) - log Lambda(start)`; telescoping the sub-segments around the four edges with the monodromy jumps (`RectWinding.log_neg_sub_im_*`) bounded by the per-step half-plane witnesses gives exactly `2*pi*i*5`. Handle the rotated branch: for direction `d`, use `Complex.log (Lambda z) = Complex.log (e^{-i*theta} Lambda z) + i*theta` where `theta = arg d`, OR keep each segment's contribution in terms of a locally-analytic branch and only track the total winding integer. **Build the TOY analogue first** (a known analytic function with winding 1 or 2 whose segment-enclosures are computed from its closed form) to validate the rigorous-segment proof machinery before the Lambda instance.

- [ ] **Step 4: Register (if a new kind) at all five points; else reuse `winding_count` dispatch.** Keep `test_every_emitter_is_classified` green (add a `STRUCTURALLY_NONVACUOUS` stance if a new emitter class).

- [ ] **Step 5: Build locally + axiom check.**
```bash
cd telperion/examples/zeta_zero_localization/lean && /Users/peterwmurphy/.elan/bin/lake exe cache get && /Users/peterwmurphy/.elan/bin/lake build RigorousWinding
```
sorry-free; `#print axioms rigorous_winding_lambda_five` = {propext, Classical.choice, Quot.sound}.

- [ ] **Step 6: Drift + tests + commit.** `generate.py --check`; `test_winding_count.py` + `test_certificate_sensitivity.py` green.
```bash
git add telperion/src/telperion/emit_winding_count.py telperion/examples/zeta_zero_localization/lean/RigorousWinding.lean telperion/examples/zeta_zero_localization/generate.py telperion/tests/ telperion/src/telperion/certify.py telperion/src/telperion/__init__.py telperion/src/telperion/emitter_sensitivity.py
git commit -m "feat(zeroloc): rigorous winding Bd(Lambda'/Lambda)=2*pi*i*5 from segment enclosures (route beta, unconditional)"
```

**Acceptance:** `RigorousWinding.lean` builds sorry-free with clean axioms; the Lambda theorem's hypotheses are ONLY (i) per-segment Arb slit-plane-membership facts (non-kernel input) and (ii) kernel-proved Lambda analyticity — NO residue-decomposition hypothesis (distinct from Task 4's route-alpha); conclusion `Bd(Lambda'/Lambda) = 2*pi*i*5`. If the rotated-branch proof proves intractable after real effort on the toy, report BLOCKED with the exact obstruction (controller falls back to the conditional capstone).

**Note (Task 5 revision):** Task 5's hypothesis H4 (`Bd(Lambda'/Lambda) = 2*pi*i*N`) is now discharged by Task 9's `rigorous_winding_lambda_five` (N=5), making the total-count `Sum divisor = 5` and hence the capstone UNCONDITIONAL (modulo Arb enclosures). Task 6's `n_total = 5` comes from Task 5 composed with Task 9.

---

## Self-Review

**Spec coverage:** Stage 2A → Tasks 2,3,4. Stage 2B → Tasks 1 (probe), 7 (derive/discharge). Stage 2C → Task 5. Stage 3 → Task 6. Trust boundary (enclosures as hypotheses) → Tasks 2,4,5. Honest ceiling (`conjecture1_proved=False`) → every task. Toy validations → Tasks 3,4 (winding), 1 (split). Negative controls → Tasks 3 (box∋0, angle), 6 (n_line>n_total). CI/SoC-safe → Tasks 4,6. All spec sections mapped.

**Placeholder scan:** research-grade Lean proofs (Tasks 4,5,7) are specified by exact theorem STATEMENT + named Mathlib lemmas + the template file (`RectWinding.lean`) + acceptance (sorry-free, clean axioms) rather than full proof text — the honest granularity for kernel proofs whose exact tactic sequence cannot be predicted. Python tasks (2,3) carry full test + implementation detail.

**Type consistency:** `enclose_lambda_boundary` output format (Task 2) is consumed verbatim by `winding_count_certificate` (Task 3) and the emitter (Task 4). `Bd(Λ'/Λ) = 2πi·N` (Task 4) feeds `box_arg_principle_lambda` H4 (Task 5), whose `Σ divisor = N` feeds `box_localization` B (Task 6). `winding_count`/`box_localization` kinds are registered identically at all five points. The [2/5,3/5]×[10,35] box and `N=5` are consistent across Tasks 4,5,6,7.

**Risk note (controller):** Tasks 4 and 7 carry the real difficulty (data-driven monodromy; local Blaschke split). Each is toy-validated / probe-gated first. If Task 4's monodromy proof stalls after the toy, rule on a scoped fallback (coarser fixed-direction winding certificate). Task 7 is explicitly branch-on-probe. The capstone (Task 6) is reachable regardless, with the split-as-hypothesis trust boundary.
