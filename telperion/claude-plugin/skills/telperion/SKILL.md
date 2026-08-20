---
name: telperion
description: Use when formalizing polynomial/rational-function facts in Lean 4 via Telperion — proving families of "0 ≤ f" or "before ≤ after on a box" inequalities, and also polynomial EQUALITIES (ideal membership / equational consequence), INFEASIBILITY (a system has no solution), and Positivstellensatz certificates (Handelman, SOS refutation, real Nullstellensatz) — by sympy certification batch-compiled to Mathlib. Use when the user mentions Telperion, Polya/Positivstellensatz certificates, positivity batches, ideal membership, infeasibility, or wants many similar polynomial facts machine-checked at once.
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

## Beyond positivity: equalities, infeasibility, Positivstellensatz

Telperion is no longer positivity-only. Six emitters extend the same
untrusted-generator / kernel-checked discipline to the full algebraic
hierarchy — each is the *certifier* (the checker), and a wrong certificate is
refused or fails to compile, never a false theorem. All are frozen families
compiled in CI (the `audit-compiles` `lake build`); the README shape table is
the authoritative per-emitter reference.

- **Equalities from an ideal.** `NullstellensatzEmitter` — `p = 0` on the
  variety `V(g₁..gₘ)` via ideal membership `p = Σ hᵢ gᵢ` (Gröbner cofactors,
  auto-computed). `ConsequenceEmitter` — `lhs = rhs` from equational
  hypotheses `{aᵢ = bᵢ}` (the everyday "these equations force this identity").
  Both emit a single `linear_combination`.
- **Infeasibility (no common solution).** `InfeasibilityEmitter` — a
  polynomial system has no common zero, via `1 ∈ ⟨gⱼ⟩` (undetermined-
  coefficient auto-search up to `max_deg`, default 3) → `1 = 0` → `False`.
  Covers *complex* infeasibility; it REFUSES real-only cases (e.g. `x²+1=0`,
  which has complex roots) and points you to `SOSRefutationEmitter`.
- **Positivstellensatz / real cases.** `HandelmanEmitter` — `0 ≤ p` on a
  polytope `{ℓᵢ ≥ 0}` via a nonneg combination of constraint products (LP, no
  SDP). `SOSRefutationEmitter` — a real semialgebraic system `{gᵢ≥0, hⱼ=0}` is
  unsatisfiable via `−1 = σ₀ + Σσᵢgᵢ + Σλⱼhⱼ` (closes the real-only gap
  Infeasibility leaves — this is where `x²+1=0` succeeds). `RealNullstellensatz-
  Emitter` — `p = 0` on the REAL variety via `p^{2m} + s ∈ ⟨gₖ⟩`.
- **Supply vs. auto:** Nullstellensatz / Consequence / Infeasibility
  auto-compute their cofactors/refutation; `SOSRefutationEmitter` and
  `RealNullstellensatzEmitter` take the SOS multipliers / exponent `m` as
  INPUT — Telperion checks the certificate, it does not run an SDP solver to
  find it. Supply the certificate; the kernel checks it.

**The nonvacuity gate (runs inside `emit()`).** Emitting `X = X`, `0 ≤ 0`, or
a claim that holds regardless of its certificate is REFUSED: a structural
check rejects reflexive conclusions, a semantic check requires that corrupting
the certificate breaks the claim, and a corpus drift-net scans every frozen
`.lean`. A kernel-green build of a *vacuous* statement is the one failure a
green build cannot catch — so the gate catches it before emission. Do not
satisfy an emitter with a trivially-true restatement; that is a defect, not a
shortcut.

## What Telperion cannot do (name it, don't force it)

Algebraic certificates only: transcendental bounds (log/exp) live in the
*validation* layer (`telperion.validate`: `VerifiedConstant`, `Log1pUpper`,
`certify_floor` bisection) and are never emitted. Within the algebraic world,
pick the right member of the hierarchy rather than forcing one: a genuinely
non-Polya inequality wants a different decomposition (or `Handelman`/
constrained-SOS), a polynomial vanishing on the real variety but not the ideal
wants `RealNullstellensatz` (not `Nullstellensatz`), and a real-only
infeasibility wants `SOSRefutation` (not `Infeasibility`). When only part of a
proof fits, use Telperion for that part; the tool is designed to be partially
adopted.
