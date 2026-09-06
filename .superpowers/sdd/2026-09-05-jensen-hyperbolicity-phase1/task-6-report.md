# Task 6 Report: End-to-end d=2 certificate MILESTONE

**Status: COMPLETE — all deliverables shipped and verified green.**

conjecture1_proved = False. NOT a proof of RH.

---

## What was wired

### 1. generate.py: Extended arg interface

`examples/jensen_hyperbolicity/generate.py` now accepts:
- `--degree INT` (default 2): Jensen polynomial degree (only 2 supported)
- `--n INT` (default 0): Offset into the alpha sequence
- `--prec INT` (default 300): Arb precision bits for coefficient enclosure
- `--check`: Verify on-disk file matches a fresh render (existing flag, preserved)

Before writing, it prints the certified box and discriminant margin:

```
Certified box for J^{2,0} (prec=300 bits):
  c0 (constant): [0.49712078, 0.49712078]
  ...
  c2 (leading): [0.00012345202, 0.00012345202]
Discriminant lower bound (margin): 0.000282228
  margin = 2575296.../9124881... (exact rational)
```

### 2. AXLE statement-match gate (kernel-enforced)

The emitter (`src/telperion/emit_jensen_polynomial_hyperbolicity.py`) now appends
an `example` immediately after each theorem block in the emitted Lean:

```lean
-- AXLE statement-match gate: the kernel checks that jensen_box_hyperbolic_deg2_0
-- has EXACTLY the intended type. This `example` compiles only if the emitted Prop
-- is literally the box-hyperbolicity statement ending in .roots.card = 2.
example : forall c0 c1 c2 : Real,
      <lo0> <= c0 -> c0 <= <hi0> ->
      <lo1> <= c1 -> c1 <= <hi1> ->
      <lo2> <= c2 -> c2 <= <hi2> ->
      (Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X +
        Polynomial.C c0).roots.card = 2 :=
  jensen_box_hyperbolic_deg2_0
```

The type ascribed is exactly the concrete box-parametric signature (with the
full rational literals). The Lean kernel checks this at build time. Any mismatch
between the emitted theorem Prop and this `example` type causes a BUILD FAILURE.
This is the AXLE statement-match — no string comparison needed.

### 3. Green build output (warm-verified)

```
lake exe cache get         # cache already warm, 0 files downloaded
lake build
  [8657/8658] Built JensenHyperbolicity (24s)
  info: JensenHyperbolicity.lean:49:0: 'jensen_box_hyperbolic_deg2_0' depends on
        axioms: [propext, Classical.choice, Quot.sound]
  Build completed successfully (8658 jobs)
```

No sorry. Axioms: `{propext, Classical.choice, Quot.sound}` only.

### 4. End-to-end test suite

`tests/rh_jensen/test_end_to_end_d2.py` — 5 tests, all PASSING:

```
tests/rh_jensen/test_end_to_end_d2.py::test_generate_writes_lean_no_sorry      PASSED
tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_contains_axle_gate  PASSED
tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_contains_theorem    PASSED
tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_builds_green        PASSED
tests/rh_jensen/test_end_to_end_d2.py::test_check_mode_passes                  PASSED
5 passed in 7.34s
```

`test_generated_lean_builds_green` runs `lake exe cache get` then `lake build`
from pytest (SoC-safe), asserts returncode 0, and confirms the theorem name
appears in the build output.

### 5. Trust-boundary README

`examples/jensen_hyperbolicity/README.md` states plainly:

1. **Kernel theorem**: the box-hyperbolicity statement (for all coefficient
   vectors in the certified rational box, the Jensen polynomial is hyperbolic).
   Fully kernel-verified, axioms `{propext, Classical.choice, Quot.sound}`.

2. **Non-kernel link**: coefficient-membership (`alpha(n+k) in box`) is
   Python-certified via `python-flint`/Arb ball arithmetic at 300-bit precision.
   This is the ONE documented trust boundary, analogous to inputs R/B in the
   zero-free bridge.

3. **conjecture1_proved = False**: certifies J^{2,0} only. NOT a proof of RH.
   RH requires the infinite family for all d and n, plus a uniform-in-d
   threshold argument — both out of scope.

4. How to regenerate and verify (`generate.py` commands + `lake build`).

---

## Files changed / created

| File | Action |
|------|--------|
| `examples/jensen_hyperbolicity/generate.py` | Modified: added --degree/--n/--prec args, box/margin printing |
| `examples/jensen_hyperbolicity/lean/JensenHyperbolicity.lean` | Regenerated: added AXLE gate example |
| `examples/jensen_hyperbolicity/README.md` | Created: trust-boundary doc |
| `src/telperion/emit_jensen_polynomial_hyperbolicity.py` | Modified: AXLE example appended to THEOREM_TEMPLATE |
| `tests/rh_jensen/test_end_to_end_d2.py` | Created: 5-test end-to-end suite |
| `.superpowers/sdd/2026-09-05-jensen-hyperbolicity-phase1/task-6-report.md` | Created: this report |

---

## #print axioms output

```
'jensen_box_hyperbolic_deg2_0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Same for `hyperbolic_deg2_of_discrim_nonneg` (JensenBridge.lean).

---

## Concerns / notes

- The AXLE example type duplicates the full concrete box bounds (all the large
  rational literals). This is intentional: the kernel check is only meaningful
  if the type is fully concrete, not a schematic. The duplication is generated
  by the emitter, not hand-written.
- JensenBridge.lean and the emitter's proof logic were NOT modified (constraint
  respected).
- The non-kernel link (Python coefficient enclosure) is the only trust gap.
  It is explicitly documented and is structurally identical to how the
  zero-free bridge handles its Python-certified inputs.
- conjecture1_proved = False in all new files.
