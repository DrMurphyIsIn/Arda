# Independent review brief — R3Cert bridge (2026-08-14)

You are an independent, adversarial reviewer of a Lean 4 formalization. The kernel already
checks the PROOFS; your job is the STATEMENTS and DEFINITIONS: do they say what the
mathematics claims? Work from the files fresh; do not trust docstrings or commit messages.
Your deliverable is a written report; a "pass" you cannot defend is worse than a fail.

Repo worktree: /Users/peterwmurphy/arda-wt-edit
Formalization root: proof/formalization (Lean lib R3Cert)
Python ground truth: proof/verification/phibound.py (DEC recursion),
raw_amplitude_seam.py (S1/S2/V3/S3 statements), branch_multiplicativity.py.

## Claimed machine-checked chain (verify each statement's semantics)

1. `Reach.lean`: `Branch`, `cav`, `cavSum`, `zc`, `ac`, `eroot`, `logPhi` — must match the
   DEC recursion: cav = 3/(3+3k+4c+3S), z(d,c)=3/(3d+c), a(d,c)=(3/2)^c (1+c/(3d))/rhoB^(1+2c),
   logPhi = sum children + log a + log(1+zS), rhoB = (621/64)^(1/11).
2. `phi_le_one` (PotentialFinal.lean or assembly): logPhi b ≤ 0 for EVERY Branch b —
   check there is no hidden hypothesis and the universal quantifier is real.
3. `BridgeStep4c`: `litRealize`/`litCherry`/`dB`/`Vb`/`Wb`,
   `Ztot_lit_eq_Wb`, `exp_logPhi_mul_rhoB_pow : exp (logPhi b) * rhoB^(Vb b) = Ztot (litRealize b)`
   — cross-check the weight and degree conventions against raw_amplitude_seam.py (S1/S2).
4. `BridgeStep4d`: `litHub` (TRUE root degree c+#ch, no phantom), `Ztot_litHub`,
   `amplitude_bridge`, `amplitude_bridge_logPhi` (hub limit).
5. `Matching.lean` + `BridgeStep3d`: `lapl` (real Laplacian? diagonal degree, -1 on edges),
   `Matrix.permanent` usage, `IsEdgeEnum`, `pi_eq_msum : per(lapl G)/prod deg = msum E`.
6. `BridgeStep3e/3f/4e/4f/4g/4h`: `aGraph` (adjacency = recorded unordered key), `liftEdges`,
   `msum_liftEdges`, degree = touching count, `GoodTree`, `realize_weights`.
7. `BridgeStep4i/4j`: `pi_litHub'` and `amplitude_bridge_real'` — THE CAPSTONES. Verify:
   the graph is `aGraph (realize (litHub c ch))` (the real competitor tree), the LHS is a
   genuine Laplacian-permanent ratio over ALL vertices of that graph, the limit is
   exp(logPhi b) * rhoB^(Vb b), and `aGraph_realize_isAcyclic` has no hidden hypotheses.

## Mandatory checks

A. Global stub scan at HEAD: grep every R3Cert/*.lean for `sorry`, `axiom`, `native_decide`,
   `Prop := True`, `admit`, `partial def`, `unsafe`, `@[implemented_by]`. Report every hit
   with context (docstring mentions are fine; code uses are failures).
B. Semantic spot-checks BY HAND (do the arithmetic yourself):
   - cav of the bare leaf = 1; cav of the arm (node 0 [leaf]) = 3/7? (compute from the def);
   - Ztot (litRealize (node 1 [])) should equal 7/4 = (3/2)(7/6) = Wb; check via the defs;
   - dB (node c ch) = ch.length + 1 + c; Vb = 1 + 2c + sum; childCount (litRealize K) + 1 = dB K.
   - lapl diagonal = degree, off-diagonal -1 exactly on Adj.
C. Degenerate instantiations: what do the capstones say when the vertex type is empty or
   the tree is a single leaf? Is anything vacuously true in a way that undermines the claim?
   (e.g. does `realize (litHub 0 [])` produce an empty edge list / empty graph — and if so,
   is `pi_litHub'` still meaningful there or merely 1 = 1? Note: harmless if the statement
   is still literally true and the interesting instances are nonempty.)
D. Quantifier structure of `amplitude_bridge_real'`: the Tendsto is over p with EVERYTHING
   else fixed; confirm the graphs inside genuinely depend on p and the limit constant does not.
E. Import DAG: confirm no file imports anything that would make a capstone circular
   (e.g. nothing in the Potential* chain imports Bridge* files).
F. Check `conjecture1_proved` ledger claims in file docstrings are honest (they must all
   say False / review pending).

## Report format (write to formalization/REVIEW_2026-08-14.md)

- Verdict per numbered item (PASS / FAIL / CONCERN) with one-paragraph justification each.
- Every stub-scan hit listed.
- The hand-computed spot checks shown.
- A final section "What the machine-checked results do NOT establish" (scope honesty:
  R4-R7 reduction layer, near-star competitor restriction, etc.).
- Overall verdict: the strongest claim the formalization supports, stated in one sentence.

Do NOT run `lake`/`lean` locally (machine constraint). Read-only + the report file.
