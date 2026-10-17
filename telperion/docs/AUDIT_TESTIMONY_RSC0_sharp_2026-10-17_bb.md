# RSC0 registry read-back for the grant: bb (AI read-back, NOT an operator read-back), 2026-10-17

Nodes: telperion/missions/anduril/nodes/AND_rs_remainder_c0_sharp.toml and AND_rs_remainder_c0_seam_sharp.toml, at commit
2c6950d1b (branch registry/rsc0-nits-readback-grant, off main d612435cb; amended from 101a42b42; not pushed at the time of reading).
Requested by the lead, who reports the user's word in the lead's session: "The contrarian's nits, then a read-back and your grant
on the two sharp-constant nodes." bb supplies the audit text only. `mission audit`, the grant (under the user's identity) and the PR
are the lead's steps on the user's word. bb grants nothing. conjecture1_proved = False.
Pre-edit copy (the 101a42b42 draft, never sent): READBACK_GRANT_2026-10-17_pre_2c6950d1b.md.

## What bb checked (logs in grant_readback/ for 101a42b42, grant_readback/at_2c6950d1b/ for 2c6950d1b)
- **Diff d612435cb..2c6950d1b:** four files. The two node titles; the lakefile comment (39 -> 49); and the new tests in
  tests/test_missions_mirror_drift.py. No .lean file differs from 8efa32574 (bb's Phase 4 read-back head) or from main.
  Between 101a42b42 and 2c6950d1b the Lean files and the island lakefile are identical. Only N4 changed: the standalone mirror
  script and its test were replaced by two tests on the existing name-keyed checker, and the titles now name that test.
- **The new titles** state each inequality exactly, with its hypotheses and the old constant, and carry the "NOT by itself a bound on
  zeta" scope.
- **Build and guards (at 101a42b42, and again at 2c6950d1b).** `lake build --no-build` of the nine RSC0 targets: all 8790 jobs up to date. Both guards
  CI-style: 71 and 49 lines, standard three axioms only, no sorryAx. Both theorems depend on exactly {propext, Classical.choice,
  Quot.sound}. Both statement files and ANDDefsRS elaborate, with only the `sorry` warning.
- **Statements.** statement_matches is True at both commits, and 5 tamper controls per node are False.
- **Mirror (at 2c6950d1b).** telperion.missions.mirrors finds all nine names, each in exactly one island file (RS_B3, RS_Kernel,
  RS_Strip), all in sync. tests/test_missions_mirror_drift.py: 8 passed, including the rsAlpha tamper control. It runs in
  telperion-test, which is path-filtered and, per the lead's branch-protection note of 2026-10-17, NOT a required check.
- **Tools (at 2c6950d1b).** verify --strict-provenance OK; judge --check OK (10 challenges).
- **Name resolution.** Each of the nine vocabulary names is defined once in the island, so nothing is shadowed inside RSSeam.

## Correction to READBACK_PHASE4 item 5
It names the seam theorem "RSInt.rs_remainder_C0_seam'". The theorem is RSSeam.rs_remainder_C0_seam' (RS_B3Sharp.lean:1153, inside
namespace RSSeam with open RSInt). The statement's names resolve to the RSInt definitions, and the judge's challenge uses
RSSeam.rs_remainder_C0_seam'. No conclusion changes.

## Nits on N4 (non-blocking)
- The checker compares names present in both files. A definition added to ANDDefsRS with no island counterpart would go unchecked,
  although the nine-name floor in the test does catch a missing one.
- It compares declaration text only, not the surrounding namespace, opens or notation, which the mirror header asserts.
- The textual link remains; a defs hash at grant would close it (Phase 4 design note).
- The test does not run on every PR. Making the unit job required, or running this one test in a required job, would make the gate
  binding.

## The texts (paste verbatim)

### AND_rs_remainder_c0_sharp
auditor = AI read-back by Claude (bb session, Riemann Auditor), NOT an operator read-back; under the owner 2026-10-12 decision accepting AI read-backs; second reading by the Riemann contrarian session (session_01226mK3JtJ3FbUCTnaHwXWj), textual and CI-log only
auditor_identity = claude-ai-readback+bb-session@anthropic-ai.invalid
auditor_session = session_01HosT9Zt8q86r49TvoLukmr
independence basis = independent: rebuilt and re-checked in the auditor's own detached worktree ~/arda-bb-rsc0 (build at 8efa32574; every check re-run at 2c6950d1b; Lean content identical throughout); auditing session session_01HosT9Zt8q86r49TvoLukmr (local 5d5c89fb-b1b7-4c86-83eb-814246e667ba) is not the author's session_01TeEsdE4SroprJqfYm9qcKc, and the auditor wrote no RSC0 file
text =
Formal statement, rendered by the auditor from the statement file and the nine definitions of Statements/ANDDefsRS.lean (not from the title): for every real t >= 4250 with p := rsFrac t = sqrt(t/(2 pi)) - N > 0 and cos(2 pi p) != 0, and every real phi with |phi - thetaMain t| <= 1/t, |2 Re(e^(i phi) rsRem t) - (-1)^(N+1) (t/(2 pi))^(-1/4) Psi(p)| <= (3/5) t^(-3/4), where N = floor(sqrt(t/(2 pi))), Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p), thetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8, and rsRem t = -(integral over real v of G(z) z^(-1/2 - i t) (1 + i)) with z = N + 1/2 + v (1 + i) and G(x) = e^(pi i x^2) / (e^(pi i x) - e^(-pi i x)) (principal complex power; Lean Bochner integral). Excluded: p = 0 and p in {1/4, 3/4}. It bounds the Riemann-Siegel contour-integral remainder rsRem only and is NOT by itself a bound on zeta or Hardy's Z: the link is RSInt.rs_Z_C0' in RS_BridgeSharp, which is not a registry node. Artifact theorem RSInt.rs_remainder_C0' in RS_B3Sharp.lean (constant was 2, for t >= 10000). Checked by the auditor, in the auditor's own detached worktree ~/arda-bb-rsc0: the nine RSC0 lake targets rebuilt at 8efa32574 (8790 jobs, exit 0, 2026-10-16); at 101a42b42 and at 2c6950d1b, whose Lean files and island lakefile match 8efa32574 except a lakefile comment, and whose Lean matches main d612435cb, lake build --no-build reports all 8790 jobs up to date (2026-10-17); RS_AxiomGuardSharp (71 lines) and RS5_AxiomGuardSharp (49) print only propext, Classical.choice and Quot.sound, no sorryAx, and RSInt.rs_remainder_C0' depends on exactly those three; statement_matches against RS_B3Sharp.lean is True, and tampered copies (threshold, constant, phase ball 1/t to 2/t, exponent -3/4 to -1/2, 0 < p to 0 <= p) are all False; the statement and ANDDefsRS elaborate against the island's Mathlib v4.32.0 with only the expected sorry warning; the nine definitions are verbatim copies of the island's (tests/test_missions_mirror_drift.py, telperion.missions.mirrors, 8 tests pass including an rsAlpha tamper control; it runs in the path-filtered unit job, which is not a required check), each defined once in the island, so no name is shadowed; ANDDefs.lean is byte-identical to pre-PR main; at 2c6950d1b mission verify anduril --strict-provenance OK and judge --check OK (10 challenges). Not run by the auditor: Comparator (the lead's PASS used a reduced bridge, 7 of the judge's 14 AxiomGuard imports). Second reading: the Riemann contrarian session's textual and CI-log read-back, READBACK_RSC0_PR751_contrarian_2026-10-16.md (PASS).

### AND_rs_remainder_c0_seam_sharp
auditor = AI read-back by Claude (bb session, Riemann Auditor), NOT an operator read-back; under the owner 2026-10-12 decision accepting AI read-backs; second reading by the Riemann contrarian session (session_01226mK3JtJ3FbUCTnaHwXWj), textual and CI-log only
auditor_identity = claude-ai-readback+bb-session@anthropic-ai.invalid
auditor_session = session_01HosT9Zt8q86r49TvoLukmr
independence basis = independent: rebuilt and re-checked in the auditor's own detached worktree ~/arda-bb-rsc0 (build at 8efa32574; every check re-run at 2c6950d1b; Lean content identical throughout); auditing session session_01HosT9Zt8q86r49TvoLukmr (local 5d5c89fb-b1b7-4c86-83eb-814246e667ba) is not the author's session_01TeEsdE4SroprJqfYm9qcKc, and the auditor wrote no RSC0 file
text =
Formal statement, rendered by the auditor from the statement file and the nine definitions of Statements/ANDDefsRS.lean (not from the title): for every real t >= 509 with p := rsFrac t = sqrt(t/(2 pi)) - N > 0 and cos(2 pi p) != 0, and every real phi with |phi - thetaMain t| <= 1/t, |2 Re(e^(i phi) rsRem t) - (-1)^(N+1) (t/(2 pi))^(-1/4) Psi(p)| <= (21/25) t^(-3/4), where N = floor(sqrt(t/(2 pi))), Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p), thetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8, and rsRem t = -(integral over real v of G(z) z^(-1/2 - i t) (1 + i)) with z = N + 1/2 + v (1 + i) and G(x) = e^(pi i x^2) / (e^(pi i x) - e^(-pi i x)) (principal complex power; Lean Bochner integral). Excluded: p = 0 and p in {1/4, 3/4}. It bounds the Riemann-Siegel contour-integral remainder rsRem only and is NOT by itself a bound on zeta or Hardy's Z: the link is RSSeam.rs_Z_C0_seam' in RS_BridgeSharp, which is not a registry node. Artifact theorem RSSeam.rs_remainder_C0_seam' (inside namespace RSSeam with open RSInt, so every name resolves to the RSInt definition) in RS_B3Sharp.lean (constant was 13/5). Checked by the auditor, in the auditor's own detached worktree ~/arda-bb-rsc0: the nine RSC0 lake targets rebuilt at 8efa32574 (8790 jobs, exit 0, 2026-10-16); at 101a42b42 and at 2c6950d1b, whose Lean files and island lakefile match 8efa32574 except a lakefile comment, and whose Lean matches main d612435cb, lake build --no-build reports all 8790 jobs up to date (2026-10-17); RS_AxiomGuardSharp (71 lines) and RS5_AxiomGuardSharp (49) print only propext, Classical.choice and Quot.sound, no sorryAx, and RSSeam.rs_remainder_C0_seam' depends on exactly those three; statement_matches against RS_B3Sharp.lean is True, and tampered copies (threshold, constant, phase ball 1/t to 2/t, exponent -3/4 to -1/2, 0 < p to 0 <= p) are all False; the statement and ANDDefsRS elaborate against the island's Mathlib v4.32.0 with only the expected sorry warning; the nine definitions are verbatim copies of the island's (tests/test_missions_mirror_drift.py, telperion.missions.mirrors, 8 tests pass including an rsAlpha tamper control; it runs in the path-filtered unit job, which is not a required check), each defined once in the island, so no name is shadowed; ANDDefs.lean is byte-identical to pre-PR main; at 2c6950d1b mission verify anduril --strict-provenance OK and judge --check OK (10 challenges). Not run by the auditor: Comparator (the lead's PASS used a reduced bridge, 7 of the judge's 14 AxiomGuard imports). Second reading: the Riemann contrarian session's textual and CI-log read-back, READBACK_RSC0_PR751_contrarian_2026-10-16.md (PASS).
