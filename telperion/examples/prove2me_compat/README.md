# prove2me_compat — Lean 4.33.1 compatibility smoke test

## Purpose

The bridge submits Telperion-emitted Lean proofs to prove2.me.  The platform
accepts only specific Lean toolchain versions (4.33.1, 4.30.0, 4.29.0-rc3),
while Telperion's own examples pin v4.32.0.

This example proves that the emitted tactic cores — `ring`, `positivity`,
`norm_num`, `linarith` — survive under Lean 4.33.1 before any bridge code is
written.  It re-uses the known-good Bernoulli family (k=2..6 instances) as the
test corpus.

## Discovered platform pins

These were discovered from the official prove2.me workspace and skill files on
2026-09-11:

- Workspace repo: <https://github.com/prove2me/prove2me_workspace>
- Source files checked: `SKILL.md`, `references/lean-setup.md`

| Pin | Value |
|-----|-------|
| Lean toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib commit | `0df444a360eaa60ab8c11dca51a86af692955474` |

The Mathlib commit is the prove2.me **default environment** rev (the single
env most theorems target).  The v4.30.0 environment uses
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

These values are needed by Task 4 (workspace.py) when constructing the correct
`lakefile` for local verification.

## Commands

```bash
# 1. Emit the Lean file (run from examples/prove2me_compat/)
python3 generate.py

# 2. Fetch prebuilt Mathlib cache and build
cd lean
lake exe cache get
lake build
```

## Result

`lake build` exits 0 under Lean 4.33.1.  5 theorems compiled.  One linter
warning (`hx` unused variable — style-only, not an error).

The emitted tactic cores are forward-compatible with Lean 4.33.1.  The bridge
may safely target this toolchain.
