# Conventions for the archimedean conceptual-proof stage branches (2026-10-11)

Plan: telperion/docs/ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md (section 4 is the stage table; read sections 0, 2, 4).
Island: telperion/examples/rvm_bridge/lean (Lean v4.33.0-rc2, Mathlib 51e6992e; .lake already built, 3754 jobs).

Module naming (avoids collisions with E6Bridge*, KWin*, KWin2* owned by other sessions):
  ArchS1_*.lean, ArchS2_*.lean, ArchS5_*.lean, ArchS9_*.lean, ... (stage number in the prefix).
Each stage adds its own [[lean_lib]] stanza(s) to lakefile.toml at the END of the file, and does NOT edit
defaultTargets or AxiomGuardRvMBridge.lean (the coordinator wires those at merge to avoid conflicts).
Each stage keeps its own guard file ArchSn_Guard.lean containing `#print axioms` for every top-level theorem;
the required output is exactly [propext, Classical.choice, Quot.sound] (no sorryAx, no new axioms).

Build: `cd telperion/examples/rvm_bridge/lean && lake build <YourModule>` (never bare `lake build`; never wrap in
`timeout`, it does not exist on this macOS). Check the guard with `lake env lean ArchSn_Guard.lean`.
Machine is shared and loaded (load ~20): build one module at a time. Pin *_NUM_THREADS=1 for any Python.

Honesty rules: no `sorry` in committed code; no `axiom`; if a lemma cannot be closed, leave it out and record it as
an open item in the stage's notes file telperion/docs/ARCH_Sn_NOTES.md (what is proved, what is open, Lean footguns).
Statements must use the project's existing definitions (WeilExplicit.weilForm / autocorr / IsWeilTest, RvMBridge
psiR machinery, E6Bridge30-34 lemmas) wherever they apply; do not redefine them.

Git: commit locally on your stage branch as you complete each lemma group; DO NOT push, DO NOT open PRs, DO NOT
touch registry nodes. Commit trailer:
  Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01GdU4sR3VVeEfVS1Dtg5pEt
conjecture1_proved = False. Nothing here is RH progress.
