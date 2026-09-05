# Task 5 Report: Turan-box log-concavity emitter

## Design choice: A (DRY delegation to box_robust)

`turan_box_family` returns a **box_robust-kind** family. The `special` tuple is
`("box_robust", inner_spec)` where `inner_spec` translates
`(a0_box, a1_box, a2_box)` -> `([a0_box, a1_box, a2_box], a1**2 - a0*a2, (a0, a1, a2))`.
No new kind, no dispatch entry, no new emitter class. Everything -- certification,
refusal gate (margin < 0 -> CertificationError), emission, statement-match gate --
flows through the existing #2 (box_robust) path end to end. Design B was not needed.

## Thin delegation

`emit_turan_box.py` is ~75 lines (docstring + `_make_inner_spec` wrapper +
`turan_box_family`). It imports `box_robust_family` and calls it. The inner spec
normalises each of the three box endpoints to `Fraction` (via `sp.Rational`
round-trip, consistent with #2) and returns the fixed sympy target `_a1**2 - _a0*_a2`.

`__init__.py` gains one line: `from .emit_turan_box import turan_box_family`.

No changes to `certify.py` or `_SPECIAL_KINDS`/`_SPECIAL_DISPATCH`.

## Example: green build + axioms clean

`examples/turan_box/generate.py` certifies and emits one theorem for
(a0=1, a1=2, a2=1): `a1^2 - a0*a2 = 4-1 = 3 > 0`. Emitted:

```
theorem turan_triple_1_2_1 : forall a0 a1 a2 : R,
    1 <= a0 -> a0 <= 1 -> 2 <= a1 -> a1 <= 2 -> 1 <= a2 -> a2 <= 1 ->
    (0:R) <= a1 ^ 2 - a0 * a2 := by
  intro ... nlinarith [sq_nonneg ..., mul_nonneg ...]
example : ... := turan_triple_1_2_1   -- statement-match gate
```

`lake exe cache get` + `lake build`: **8656 jobs, Build completed successfully (6.4s)**
`#print axioms TuranBox.turan_triple_1_2_1`: `[propext, Classical.choice, Quot.sound]` -- clean.
Drift check (`--check`): byte-for-byte match.

## TDD evidence

`tests/test_turan_box.py` -- 3 tests, all green:

| Test | Assertion | Result |
|------|-----------|--------|
| `test_log_concave_emits_theorem` | emit produces `(0:R) <=` + `a1` in text, n=1 | PASS |
| `test_log_concave_count_one` | single-point grid -> exactly 1 theorem | PASS |
| `test_non_log_concave_refuses` | (1,1,2) raises CertificationError | PASS |

`pytest tests/test_turan_box.py -v`: 3 passed in 0.34s.

## Files changed

| File | Change |
|------|--------|
| `src/telperion/emit_turan_box.py` | NEW: convenience constructor delegating to box_robust |
| `src/telperion/__init__.py` | +1 line: export `turan_box_family` |
| `tests/test_turan_box.py` | NEW: 3 TDD tests |
| `examples/turan_box/generate.py` | NEW: example script |
| `examples/turan_box/lean/TuranBox.lean` | NEW: generated theorem (1071 bytes) |
| `examples/turan_box/lean/lakefile.toml` | NEW: `name = "TuranBox"`, mathlib v4.32.0 |
| `examples/turan_box/lean/lean-toolchain` | NEW: copied from algebraic_bracket |
| `examples/turan_box/lean/lake-manifest.json` | NEW: copied from algebraic_bracket |

## Concerns

None. Design A works cleanly: `turan_box_family` returns a genuine box_robust-kind
family and the full #2 machinery (certify, emit, gate) applies without modification.
The statement-match gate emits correctly (single-sourced from the theorem type string
in BoxRobustEmitter.emit_body). conjecture1_proved = False.
