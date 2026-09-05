# AXLE Telperion suite — applied to the Riemann Hypothesis (2026-09-04)

Survey + review of the AXLE-ported Telperion capabilities, then a concrete
application to the RH zero-free-region thread (`zeta_log_bound` + `ZeroFreePolylog`).
Companion to `AXLE_SECOND_TOUR_2026-09-03.md` / `AXLE_THIRD_TOUR_2026-09-04.md`
(the capability tours) and `scratch/bg_axle_apply.py` (the validated BG driver).
`conjecture1_proved = False` (RH is NOT proved; this is tooling applied to the
formalization).

## 1. What the AXLE suite is (survey)

AXLE (Axiom Math, arXiv:2606.26442) is a cloud Lean-4 verification-utility layer.
Rounds 1–3 ported its primitives into `telperion/src/telperion/`:

| module | AXLE origin | capability |
|---|---|---|
| `verify.py` | `verify_proof`/`check` | structured Lean verify; compile-vs-trusted(sorry-reject) split |
| `gap_fill.py` | `sorry2lemma` + `environment` | extract `:= by sorry` goals; route-match + fill |
| `repair.py` | `repair_proofs` | mechanical Mathlib-drift repair + re-verify |
| `negative_control.py` | `disprove` | **kernel-gated** disprove — the trust primitive |
| `cert_meta.py` | `extract_decls` | type/proof hash, tactic counts, heartbeats; `CertIndex` |
| `bundle.py` | `merge` | cert-bundle assembly, dedup, name-conflict guard |
| `normalize.py` | `normalize`/`theorem2sorry` | canonical form; blank→regenerate |
| `emit_transcendental_enclosure.py` | AxiomMath/ZetaZeros | rational `L ≤ log(1+x) ≤ U` bracket |
| `emit_curvature_boundary.py` | AxiomMath/ZetaZeros | sign-definite `f''` ⇒ extremum on boundary |

**The two design lessons (third tour), both RH-relevant:**
- **Two trust tiers.** A cheap warm-env check (no `sorry`, axioms ⊆ whitelist,
  signature matches intended statement) as the inner dev loop; the cold full build
  + Comparator judge only at the final gate. AXLE's fast path is 0.97s vs 95.7s.
- **Structural beats textual.** merge/dedup/deps keyed on `type_hash`
  (α-equivalence), not normalized text.

## 2. Application to RH (`scratch/rh_axle_apply.py`)

A driver mirroring `bg_axle_apply.py`, pointed at
`examples/zero_free_bridge/lean` and RH-shaped specs. **Two-tier by construction:**

- **Python/sympy tier (runs locally, zero Lean, proves the math in exact
  arithmetic).** Ran green this session — all four capabilities.
- **Kernel tier (`RH_AXLE_RUN_LEAN=1`, GATED OFF by default).** The RH example has
  **no `.lake` build**, so a local `verify_lean` would trigger a full Mathlib
  compile == the SoC-watchdog hazard flagged in memory. The forged/true Lean is
  generated and staged for CI (the `rh-research-artifacts` jobs), not run locally.

| # | capability | RH instance | result |
|---|---|---|---|
| 1 | negative_control | FALSE tangent `log(1+x) ≤ x − 1/10` (x≥0); TRUE control `log(1+x) ≤ x` | Layer-1 refuses at witness x=0 (LHS−RHS=+1/10); Layer-2 forged proof staged (linarith cannot close the shifted goal ⇒ kernel rejects in CI) |
| 2 | emit_transcendental_enclosure | log-face atom; its `_upper` theorem `log(1+x) ≤ x` **IS** the tangent bound under the RH harmonic bound (`harmonic_le_one_add_log → norm_partial_sum_le → zeta_log_bound`) | cert self-checked exact; Lean emitted |
| 3 | gap_fill.extract_gaps | RH sorry-skeleton (`norm_partial_sum_le`, `zeta_log_bound` as `:= by sorry`) — the actual workflow the RH thread was filled from | recovers both goals as standalone lemmas |
| 4 | cert_meta + bundle | RH atom family (tangent bound + rational fact) | type_hash index, dedup (3→2), name-conflict guard fires |

### The honest connection point (#2)
The enclosure emitter's Front-2 was the Montgomery–Taylor extremal constant
`C₀ = 3/2 − (1/√2)cot(1/√2)`, but its **trig face is DEFERRED** (needs √2 +
cos/sin Taylor bounds). So the direct C₀ enclosure is NOT available. The genuine
RH-load-bearing piece the log face DOES ship is the tangent bound `log(1+x) ≤ x`
(via `Real.log_le_sub_one_of_pos`) — the atom the harmonic bound is a sum of. The
boxed rational lower bound is BG-flavored; stated honestly in the driver.

### Honest non-fit (#3)
`gap_fill.match_log_enclosure`/`pick_route` are **FSTAR-parametrized** (BG
log-combination router); RH log goals carry no FSTAR term, so the router correctly
declines. The RH-relevant half of `gap_fill` is the **generic goal extraction**,
not the BG route-picker.

## 3. RH-driven fix to the shared suite

Applying `extract_gaps` to the RH skeleton exposed a real bug: its theorem regex
skipped only **parenthesized** `(...)` binders, so RH/Mathlib-idiom lemmas that
lead with **implicit** `{s : ℂ}` or **instance** `[...]` binders matched zero gaps
— silently. The BG atoms used only `(...)` binders, so it was never exercised.

**Fix** (`gap_fill.py`, `_SORRY_THM`): generalized the binder-skip to
`(...)`, `{...}`, `[...]`, `⦃...⦄`. Backward-compatible — the 8 existing gap_fill
tests still pass; added `test_extract_gaps_handles_implicit_and_instance_binders`
pinning the RH case (9 pass total). This is the "build reusable capability into
Telperion" standing order: a cross-front (RH) exercise hardened a shared primitive.

## 4. Signature/statement-match gate (third-tour #1) — BUILT + kernel-verified

The **positive half of the trust boundary** is now shipped: `signature_gate.py`
(`check_signatures`, `forall_type`, `build_sig_guards`). It asserts an emitted RH
theorem states the *intended* proposition, not merely that it compiles. Mechanism
(kernel-checked, no metaprogramming): for each `{decl -> intended full type}` it
appends a guard `theorem <decl>__sig_guard : <intended> := <decl>` — which
elaborates iff `<decl> : <intended>` is defeq. A weaker/different true claim is not
defeq to the intended type, so the kernel rejects it.

Kernel-verified locally against the `zero_free_bridge` env on the RH tangent atom:
- CORRECT `log(1+x) ≤ x` → **MATCH**
- WEAKER `log(1+x) ≤ x + 1` (silent restatement) → **MISMATCH** (kernel "Type mismatch")
- EXISTS-C `∃ C, ∀ x, 0≤x → log(1+x) ≤ C·x` (∃C-vs-explicit — the exact class the
  RH thread fixed `zeta_log_bound` by hand for) → **MISMATCH**

This closes the untrusted-generator/trusted-kernel boundary: `negative_control`
kills a FALSE claim; `signature_gate` kills a WEAKER/DIFFERENT true claim. Driver
capability #5; CI job `rh-signature-gate`; unit tests `tests/test_signature_gate.py`
(6 offline) + kernel demo in the driver.

### Applied to the REAL `zeta_log_bound` (not just the tangent demo)
`scratch/rh_zeta_log_bound_signature.py` builds the `ZetaLogBound` module and runs
the gate against the actual `ZeroFreeBridge.zeta_log_bound`. Kernel-verified locally:
- EXPLICIT **C=6** (intended) → **MATCH**, axioms clean — the kernel confirms the
  region's growth bound is the explicit-constant statement.
- EXPLICIT **C=7** (a true but weaker bound) → **MISMATCH** — the gate pins the
  *exact* constant, not just "some bound".
- **∃C** form → **MISMATCH** — the exact restatement the RH thread fixed by hand.

CI job `rh-zeta-log-bound-signature` (builds `ZetaLogBound`, runs the assertion)
makes this a permanent, machine-enforced guarantee.

### Remaining follow-ons (third tour, lower priority)
Fast warm-env verify tier (#2), bundle topo+type_hash (#4), per-cert deps (#5),
Environment registry (#3), mechanical simplify (#6).

## Reproduce

```
cd telperion
PYTHONPATH=src python3 scratch/rh_axle_apply.py        # Python/sympy tier (safe)
PYTHONPATH=src python3 -m pytest tests/test_gap_fill.py -q   # 9 pass
# Kernel tier — CI or a machine cleared for local Lean ONLY:
RH_AXLE_RUN_LEAN=1 PATH=$HOME/.elan/bin:$PATH PYTHONPATH=src python3 scratch/rh_axle_apply.py
```
