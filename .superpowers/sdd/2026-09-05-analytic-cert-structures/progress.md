# SDD ledger — plan: /Users/peterwmurphy/telperion-analytic/telperion/docs/superpowers/plans/2026-09-05-analytic-cert-structures.md

Spec: telperion/docs/superpowers/specs/2026-09-05-analytic-cert-structures-design.md (binding authority)
Worktree: /Users/peterwmurphy/telperion-analytic, branch telperion/analytic-cert-structures (off origin/main). Repo root: /Users/peterwmurphy/telperion-analytic. Commands run from .../telperion.
Env: PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 (3.14.6; flint 0.9.0, mpmath 1.3.0, sympy 1.14.0; telperion imports from THIS worktree src). Lean: /Users/peterwmurphy/.elan/bin/lake, warm verify (cache get first).

## Pre-flight conflict scan
| Rows | Producer -> Consumer | Found |
|------|----------------------|-------|
| T1->T2 | arb_enclosure.enclose_constant/EnclosureRecord -> box_robust example | OK, names match |
| T2->T4 | emit_box_robust.box_min_lower_bound -> hyperbolicity discriminant margin | OK |
| T2->T5 | box_min_lower_bound + BoxRobustEmitter -> turan_box delegates | OK |
| T3->T4,T5 | statement_match_example/Emitter.emit_gate -> gates in hyperbolicity/turan | OK |
| T2,T4,T5 | all edit certify.py (_SPECIAL_KINDS@114,_SPECIAL_DISPATCH@204) + __init__.py | Sequential + ADDITIVE (each appends one kind); reviewer must confirm append-not-replace |
| T6 | consumes all example dirs -> CI jobs | OK |
| Self T1 | test_returns_fractions_outward assertion awkward | plan Step 4 says use _contains form; minor |
| Self T2 | "separable quadratic" target decomposition unspecified | Ruling below |
| Self T4 | d=2 bridge = Jensen's, not in this worktree | Ruling below |

Ruling: T2 target handling = MONOMIAL-WISE interval bounds (not affine-square decomposition). box_min_lower_bound iterates target.as_poly(*syms) monomials and lower-bounds each over the box: var^2 -> square lower bound (0 if straddling, else min(lo^2,hi^2)); var_i*var_j -> extremal of 4 corner products (sign-aware); var -> endpoint; const -> itself; sum as exact Fraction. This generalizes disc2_margin (proven in Jensen). emit nlinarith hints per-monomial (sq_nonneg for squares, 4-corner mul_nonneg for bilinears, norm_num margin). Cost if wrong: margin loose/unsound -> caught by refusal tests + kernel build.

Ruling: Lean example copy source = examples/algebraic_bracket/lean (mathlib lakefile+manifest+toolchain v4.32.0 present on origin/main). Copy its 3 files for T2/T4/T5 lean dirs. Cost if wrong: cache get fails; pick another example/*/lean.

Ruling: Jensen d=2 bridge (hyperbolic_deg2_of_discrim_nonneg) is NOT in this worktree (off origin/main; PR #227 unmerged). T4 re-proves it fresh -- proven-doable in Jensen via Real.sqrt(discrim) + factor + roots_mul/roots_X_sub_C. Cost if wrong: T4 harder than expected; it's a known-provable lemma.

Scan otherwise clean. Proceeding to Task 1.

## Task log
Task 1: complete (commits cc7f8f9..3348883, review clean). Arb enclosure provider; outward dyadic mid+/-rad rigor confirmed live (zeta(1/2)<0 sign correct). Non-kernel-input docstring present.
Task 1: minor (deferred): redundant _FLINT_AVAILABLE guard in enclose_constant (arb_enclosure.py:204-208).
Task 1: minor (deferred): test_returns_fractions_outward uses float oracle (won't catch prec_bits ignored); width-shrink test partially covers.
Task 2: complete (commits 3348883..e7d2f61, review clean). box-robust emitter; margin rigor verified adversarially (sign-aware monomial-wise lower bound); registration additive; Lean green axioms clean; #1->#2 composition (box from enclose_constant). Sensitivity-gate failure confirmed pre-existing (6 dVP atoms from sibling tasks, not box_robust).
Task 2: minor (deferred): test_box_min_refuses_negative tests box_min_lower_bound<0 but not that certify_box_robust_point raises ValueError (the refusal gate); code path correct (emit_box_robust.py:576-581).
Task 2: minor (deferred, pre-existing): _SPECIAL_KINDS (67) > _SPECIAL_DISPATCH (64) asymmetry -- not introduced by us.
Task 3: complete (commits e7d2f61..12cb398, review clean). statement-match gate; single-sourced type string verified (crux); emit_statement_gate default True; box_robust example rebuilt green axioms clean.
Task 3: minor (deferred): emit_statement_gate field placed mid-class-body (layout); `if gate:` style; conjecture1_proved only in fn docstrings not workflow.py module docstring.
SIDE-FIX (not this plan): PR #227 unit-job regression fixed on branch merge/jensen-to-main (commit f84cdc3, pushed): guarded tests/rh_jensen/{coefficients,jensen,emit_jensen,grid,end_to_end_d2} with pytest.importorskip("flint") + lake skipif; local suite 29 green. r47-regen-diff CI failure confirmed PRE-EXISTING on origin/main (merge touched zero r47 files), not ours.
Task 4: review APPROVED (bridge statement exact + sorry-free axioms clean; emitted roots.card=2 chains bridge a=a2; refusal gates disc<=0 + leading-straddle + d!=2 all tested; registration additive; 2 non-zeta families; gates single-sourced). Important (cosmetic): emit_body "".join has no inter-theorem blank line (builds green, nothing appends to file). Ruling: cosmetic/not-load-bearing but fix in round 1 (trivial) bundled with tightening refusal-gate tests from bare-except to pytest.raises(ValueError) (load-bearing soundness gates deserve precise tests).
Task 4: fix round 1/5 (2 addressed, 0 open — theorem spacing + refusal tests now pytest.raises(CertificationError, match=gate-specific-reason); commit 5529ad3). Re-review: both ADDRESSED, no breakage.
Task 4: complete (commits 12cb398..5529ad3, review clean). hyperbolicity emitter (#3 d=2) + bridge lemma; refusal path raises ValueError inside certify_hyperbolicity_point, wrapped as CertificationError by certify().
Task 4: minor (deferred): redundant Fraction(str(sp.Rational(l))) round-trip; unused h2a in bridge lemma.
Task 5: complete. turan-box log-concavity emitter (#5) -- Design A (box_robust delegation); no new kind/dispatch; 3 TDD tests green; Lean warm build green (8656 jobs); axioms [propext, Classical.choice, Quot.sound]; drift check byte-for-byte.
