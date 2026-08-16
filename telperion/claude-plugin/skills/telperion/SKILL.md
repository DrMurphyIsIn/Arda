---
name: telperion
description: Use when formalizing rational-function inequalities in Lean 4 via Telperion — proving families of "0 ≤ f" or "before ≤ after on a box" claims by sympy certification batch-compiled to Mathlib, when the user mentions Telperion, Polya certificates, positivity batches, or wants many similar inequalities machine-checked at once.
---

# Telperion: sympy-certified inequality families → kernel-checked Lean 4

## The one rule that governs everything

**The generator is untrusted; the Lean kernel is the only trusted component.**
A wrong certificate fails to compile — it can never produce a false theorem.
Corollaries you must respect:

- NEVER hand-edit emitted `.lean` files (they carry `DO NOT EDIT BY HAND`
  headers and an input hash; the regeneration diff will flag you). Fix the
  *family definition* and regenerate.
- NEVER emit without exact-numeric validation. The API and CLI refuse; do not
  work around the refusal — write the validation (`fractions.Fraction` spot
  checks of the claimed inequality; floats never touch a certificate path).
- A `CertificationError` is a *refusal naming the failing (grid point,
  corner)* — treat it as data. Either the inequality is false there (check
  numerically first!) or it needs a different certificate shape (tighter box,
  cleared denominators).

## Workflow (in order, no skipping)

0. **When anything refuses, run `telperion diagnose` FIRST** (or the
   `diagnose` MCP tool): it distinguishes FALSE (returns an exact rational
   counterexample — stop, the claim is wrong) from NOT_POLYA_IN_THIS_FORM
   (with remedy hints naming the negative monomials) from tool misuse. Never
   iterate blindly on a refusal.
1. **Probe** one representative instance before building a family:
   `telperion probe "(1 + u)/(2 + u) - 1/(u + 3)" --symbols u`
   (or the `polya_probe` MCP tool). If a typical instance is not certifiable,
   the family design is wrong — stop and rethink the box/corners.
2. **Define the family** in a Python module: an `InequalityFamily` (symbols
   with `nonnegative=True`, a finite `GridSpec`, `target=` for direct claims
   or `before=`/`after=`/`box=` for bilinear-box claims, `lean_name=` per
   grid point), a `LeanProfile` (namespace, imports, prelude — e.g. the
   `bilinear_corner_nonneg` combinator for box families), and a
   `validation()` function returning a `ValidationReport` from exact-rational
   spot checks. Copy the shape of `examples/toy_box/family.py`.
3. **Certify**: `telperion certify family.py:factory` — all self-checks
   (bilinear decomposition identity, all-nonneg numerators, positive-factored
   denominators) must pass.
4. **Emit + freeze**: `telperion emit family.py:factory -o frozen/` (or the
   `emit_family` MCP tool). Output is provenance-stamped, deterministic, and
   byte-stable across sympy versions.
5. **Compile in CI** — never locally assume success: `lake build` against the
   pinned Mathlib is the actual verification. Budget `maxHeartbeats` via the
   profile for large batches; shard >40-theorem families across files.
6. **Diff on every subsequent change**: `telperion verify` (reads
   `telperion.toml`, runs every family's regeneration diff, and FAILS if any
   generate script is not listed in the manifest). After changing the tool
   itself or any family: regenerate, re-freeze, and re-run verify — the
   manifest is the drift net.

## Reading the mathematics back out

- `telperion margins family.py:factory` (MCP: `margins`): where is the family
  tight? Exact tie faces per certificate, constant-term floors, sample minima
  with argmin — the extremal structure, sorted tight-first. Run it after
  certification: the ties are where the interesting mathematics lives.
- `telperion ties "expr"` (MCP: `ties`): exact equality cases of one claim.
- Structural fact worth internalizing: a CERTIFIED instance can only be tight
  on coordinate faces (nonneg-coefficient numerators cannot vanish at interior
  points without vanishing identically). An interior tie means no Polya
  certificate exists at that point — subdivide around it and treat the tie
  arithmetically; do not fight the refusal.

## The spelling rules (why emitted proofs compile first-try)

- Every denominator is rendered in **positive-factored form**
  (`2 * (2 + u) * (2 + v)`), with one `have hdN : factor ≠ 0 := by positivity`
  per distinct factor — because `field_simp` matches `≠ 0` hypotheses
  syntactically.
- Identity proofs end `field_simp; try ring` (`try` because `field_simp`
  sometimes closes the goal; a trailing `ring` on no goals is an error).
- Assemblies spell the statement from a template with an axis hole so each
  `interval_cases` branch's `hkey` matches the post-`push_cast` goal exactly.
- Full tactic assumptions: `docs/TACTIC_CONTRACT.md` (also exposed as the
  `telperion://tactic-contract` MCP resource).

## What Telperion cannot do (name it, don't force it)

Rational-function certificates only: transcendental bounds (log/exp) live in
the *validation* layer (`telperion.validate`: `VerifiedConstant`,
`Log1pUpper`, `certify_floor` bisection) and are never emitted. Genuinely
non-Polya inequalities (irremovable negative numerator coefficients) are
refused — the correct response is a different decomposition, not a template
hack. When only part of a proof fits, use Telperion for that part; the tool is
designed to be partially adopted.
