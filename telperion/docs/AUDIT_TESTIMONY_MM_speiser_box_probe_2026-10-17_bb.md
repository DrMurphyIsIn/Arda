# Audit testimony: MM_speiser_box_probe (bb), 2026-10-17

**Who.**
- Claude, bb session (Riemann Auditor): identity claude-ai-readback+bb-session@anthropic-ai.invalid, session session_01HosT9Zt8q86r49TvoLukmr.
- This is an AI read-back, NOT an operator read-back. It is given under the owner's 2026-10-12 decision accepting AI read-backs.
- bb grants nothing. The grant, under the owner's identity, and the PR are the lead's steps, on the owner's word ("Proceed my friend").

**Independence.**
- The proof's author is session_01TeEsdE4SroprJqfYm9qcKc. That is the Claude-Session trailer of every commit touching
  SpeiserDerivCore.lean, SpeiserDerivBox.lean, AxiomGuardSpeiserDeriv.lean and arbecon/gen_speiser_box.py.
- The auditing session appears in no commit of the repository, and it wrote no file of this proof.
- The statement file predates the proof: 2026-09-16, session_019cyX7BF96LemLVmVEnL62Q.
- The node has no [author] block, so the tool records independence as "unverified". The basis above is the auditor's statement of it.

**What was checked.** All of it in the auditor's own detached worktree, ~/arda-bb-speiser, at main 8f5c830c8.
- The formal statement, rendered from Statements/MM_speiser_box_probe.lean: for every complex s with 1/4 ≤ Re s ≤ 3/8 and
  6 ≤ Im s ≤ 10, deriv riemannZeta s ≠ 0.
- **Build:** the three targets were built (3227 jobs, exit 0). All 11 axiom-guard lines print exactly [propext, Classical.choice,
  Quot.sound].
- **Statement match:** statement_matches is True, and six tampered statements are False.
- **Semantic check:** in a root-namespace file with no `open`, speiser_box_probe closes the statement, and the ζ variant (without deriv)
  is rejected.
- **Controls:** check0_neg and check0_corrupt exercise the budget clause and the derivative test respectively.
- **Disc cover:** it is a proved lemma, dist_le_of_row, plus a case split. It is not an assumption.
- **Generator:** reproduces the box file byte-identically.
- **CI:** zeta-reflection-compiles passed on the #753 head 31caf3276, with identical files.
- **Tools:** mission verify --strict-provenance OK; judge --check OK.
- **Numerics:** an independent mpmath sanity check agrees: min |ζ′| on the box is about 0.19.
- **Not run:** Comparator. The node is not yet in the judge bundle.

**Verdict.** PASS.

**Scope.** One finitely-checkable box. It is NOT the Speiser wall (Speiser 1935: ζ′ zero-free on the whole open strip 0 < Re s < 1/2 is
equivalent to RH), and it is not a step toward RH. conjecture1_proved = False.

Full record: ~/e9-research/review_speiser/READBACK_GRANT_2026-10-17.md.
