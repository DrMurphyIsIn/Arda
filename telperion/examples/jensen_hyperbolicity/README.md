# Jensen Hyperbolicity Certificate (d=2)

**conjecture1_proved = False.** This directory contains the FIRST
kernel-verified hyperbolicity certificate for a concrete Jensen polynomial of
the Riemann zeta function, specifically J^{2,0}. It is NOT a proof of the
Riemann Hypothesis.

---

## What is kernel-verified

The theorem `jensen_box_hyperbolic_deg2_0` in `lean/JensenHyperbolicity.lean`
states:

> For all real numbers c0, c1, c2 lying in the certified rational coefficient
> box, the polynomial `C c2 * X^2 + C c1 * X + C c0` has exactly 2 real roots
> (counting multiplicity).

This is the **box-hyperbolicity statement**: for EVERY coefficient vector in
the rational box, the degree-2 Jensen polynomial is hyperbolic. The Lean kernel
verifies this theorem end-to-end. The proof chains a rational lower bound on
the discriminant `c1^2 - 4*c2*c0` (certified by `nlinarith`) into the bridge
lemma `hyperbolic_deg2_of_discrim_nonneg` in `lean/JensenBridge.lean`.

Axioms: `{propext, Classical.choice, Quot.sound}` -- the standard and
unavoidable axioms of Lean/Mathlib. No `sorry`.

### AXLE statement-match gate

Immediately after the theorem, an `example` is emitted with the identical type
ascribed to `jensen_box_hyperbolic_deg2_0`:

```lean
example : forall c0 c1 c2 : Real,
      <lo0> <= c0 -> c0 <= <hi0> -> ... ->
      (Polynomial.C c2 * Polynomial.X^2 + ...).roots.card = 2 :=
  jensen_box_hyperbolic_deg2_0
```

This compiles only if `jensen_box_hyperbolic_deg2_0` has EXACTLY the intended
type. The Lean kernel enforces the match at build time; no string comparison is
needed. A type mismatch in the emitted Prop causes a build failure.

---

## The ONE non-kernel link (documented trust boundary)

**Coefficient-membership is Python-certified input, NOT kernel-verified.**

The rational coefficient box
`[(lo0, hi0), (lo1, hi1), (lo2, hi2)]` is computed by `generate.py` using
`python-flint` / Arb ball arithmetic with 300-bit precision. The computation
verifies that the true Riemann-xi Taylor coefficients `alpha(n+k)` lie in the
box. This Python-side certificate is the analogous non-kernel input to the
inputs `R` and `B` in the zero-free bridge (`RiemannHypothesis`).

The kernel theorem is unconditional over the box: IF a coefficient vector
lies in the box, THEN the Jensen polynomial is hyperbolic. The Python
certificate provides the evidence that `alpha(n+k)` DO lie in the box.
This one link is outside the kernel and is explicitly documented here.

---

## Scope: what this DOES and DOES NOT prove

This certificate proves:
- The degree-2 Jensen polynomial J^{2,0} of the Riemann zeta function is
  hyperbolic (all roots real) for every coefficient vector in the certified box.
- The certified box encloses the true alpha coefficients alpha(0), alpha(1),
  alpha(2) at 300-bit Arb precision.

This does NOT prove:
- Hyperbolicity for all degrees d (only d=2 is handled here).
- Hyperbolicity for all offsets n (only n=0 is certified by this file).
- The Riemann Hypothesis. RH requires the infinite family J^{d,n} to be
  hyperbolic for ALL d and n, plus a uniform-in-d threshold argument. Both
  are out of scope.

**conjecture1_proved = False.** This is a structural building block, not a
proof of RH.

---

## How to regenerate and verify

### Step 1: Regenerate the certificate

```bash
cd telperion
PYTHONPATH=src python examples/jensen_hyperbolicity/generate.py --degree 2 --n 0 --prec 300
```

This prints the certified box and discriminant margin, then writes
`lean/JensenHyperbolicity.lean`.

### Step 2: Verify regeneration matches frozen file

```bash
PYTHONPATH=src python examples/jensen_hyperbolicity/generate.py --check
```

Exits 0 and prints "check: OK" if the on-disk file matches a fresh render.

### Step 3: Build with the Lean kernel (SoC-safe)

```bash
cd lean
lake exe cache get       # always pull cache first -- never compile Mathlib from scratch
lake build
```

Expected output includes:
- `Build completed successfully`
- `'jensen_box_hyperbolic_deg2_0' depends on axioms: [propext, Classical.choice, Quot.sound]`

No `sorry`, no unexpected axioms.

### Step 4: Run the end-to-end test

```bash
cd telperion
PYTHONPATH=src python -m pytest tests/rh_jensen/test_end_to_end_d2.py -v
```

All 5 tests should pass, including `test_generated_lean_builds_green` which
runs `lake build` and asserts returncode 0.

---

## Files

| File | Role |
|------|------|
| `generate.py` | Driver: computes box, calls emitter, writes .lean, prints margin |
| `lean/JensenBridge.lean` | Reusable d=2 bridge: `hyperbolic_deg2_of_discrim_nonneg` |
| `lean/JensenHyperbolicity.lean` | Generated: box-hyperbolicity theorem + AXLE gate |
| `lean/lakefile.toml` | Lake project config |
| `lean/lean-toolchain` | Pinned Lean toolchain |
| `../../tests/rh_jensen/test_end_to_end_d2.py` | End-to-end pytest suite |
| `../../src/telperion/emit_jensen_polynomial_hyperbolicity.py` | Emitter |
| `../../src/telperion/rh_jensen/jensen.py` | Box assembly + discriminant margin |
| `../../src/telperion/rh_jensen/coefficients.py` | Arb coefficient enclosure |
