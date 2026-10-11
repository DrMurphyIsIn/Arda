# Archimedean rung: registry notes

This file records how the archimedean rung's results enter the missions registry, and what
local evidence exists for each before an operator read-back and a grant. Nothing here grants
anything. conjecture1_proved = False.

## MM_cc_cor_2_3 (Connes-Consani Corollary 2.3), registered 2026-10-11 as a DRAFT

### What the node says

The registered statement, verbatim from
`missions/mirrormere/lean/Statements/MM_cc_cor_2_3.lean`:

```lean
theorem cc_cor_2_3 (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    0 ≤ ArchS3.archW g + ArchS3.Dfun g
```

In words: for every Weil test function g (smooth, compactly supported, with no restriction on
the width of the support and no vanishing condition), the archimedean Weil functional on
g * g^* plus Connes and Consani's explicit delta-correction is non-negative. Here
`archW g = (1/2pi) ∫ |ĝ(r)|^2 (Re digamma(1/4 + ir/2) - log pi) dr` and
`Dfun g = Re ∫ (g * g^*)(u) delta(e^{|u|}) du`, with delta the kernel of CC (48) written in the
sinc closed form (49).

This is not Weil positivity. There is no prime side, and the delta-correction is added rather
than bounded. It is not RH and does not imply it. It is new relative to
`MM_weil_positivity_prime_free_window`, which is about `weilForm` on a window of width log 2.

### Vocabulary

The statement needs six definitions that MMDefs did not have. They are mirrored verbatim, each
inside its source namespace with the source file's `open` lines restored:

| registry name | island source |
|---|---|
| `RvMBridge11.psiR` | `examples/rvm_bridge/lean/E6Bridge11.lean:728` |
| `RvMBridge31.hsq` | `examples/rvm_bridge/lean/E6Bridge31.lean:236` |
| `ArchS3.sincInt` | `examples/rvm_bridge/lean/ArchS3_Delta.lean:101` |
| `ArchS3.deltaK` | `examples/rvm_bridge/lean/ArchS3_Delta.lean:109` |
| `ArchS3.archW` | `examples/rvm_bridge/lean/ArchS3_Delta.lean:483` |
| `ArchS3.Dfun` | `examples/rvm_bridge/lean/ArchS3_Delta.lean:486` |

The drift test pairs declarations by bare name across every island. All six pair with their
source and are in sync. One collision needed an exemption in `missions/mirrors.py`:
`ArchS4.Dfun` in `ArchS4_Rung.lean` is a different object with the same bare name. It is
complex-valued and applies D to a test directly, with kernel deltaE. The existing
`test_every_exemption_is_still_needed` pins that the two texts still differ.

The MMDefs additions plus the statement elaborate cleanly under both Mathlib v4.32.0, the
statements package pin, and the island's v4.33.0-rc2.

### Artifact

`examples/rvm_bridge/lean/ArchRegistry_CCCor23.lean` states the registered statement character
for character and proves it as `ArchS3.cc_cor_2_3 hg`, since `Lfun g` is by definition
`archW g + Dfun g`. It is in `defaultTargets`, and `AxiomGuardRvMBridge` prints its axioms:
`[propext, Classical.choice, Quot.sound]`. `lake build AxiomGuardRvMBridge` completes
successfully. The grant gate's text match (`statement_matches`) accepts the artifact, and it
refuses a variant whose conclusion is weakened with `∨ True`.

### Pre-grant Comparator judge (local, 2026-10-11)

This is pre-grant evidence only. The node is a draft, so `mission comparator-record` cannot
record it, and the bundle was written to a scratch directory and not committed.

Setup:

- The bundle came from `python -m telperion.missions.judge --island rvm_bridge --pending --only MM_cc_cor_2_3`.
  The stock judge aborts in pending mode because of an unrelated pre-existing draft,
  `MM_weil_positivity_window_tenth`. Its artifact (`E6Bridge34.lean`) writes the statement
  with unqualified names, so the theorem cannot be resolved. The pending anchor scan resolves
  every draft on the island before `--only` is applied. A scratch driver re-ran the stock judge
  with the `--only` filter moved inside the anchor scan. Everything else was the stock code.
- Comparator and lean4export were built from leanprover/comparator tag `v4.33.0-rc2`
  (commit 75c730e), matching the island toolchain as CI does. nanoda was taken from
  `~/e9-tools/nanoda` (commit 3a24072). The landrun pass-through shim means the run was
  not sandboxed.
- The bundle path-required the island at its absolute path and reused the island's
  `.lake/packages`, so nothing was re-cloned or rebuilt.
- Repo head was 730201183 plus the uncommitted registration. The artifact sha256 was
  215931fac0e2ccded8b5bdcecb0b96db858197b031f75781ed9077fcbc6eccc0.

| run | challenge type | verdict | wall time | peak RSS |
|---|---|---|---|---|
| positive | registered statement, proof `cc_cor_2_3` | ACCEPT: nanoda accepts, Lean kernel accepts | 158 s | 6.1 GB |
| tamper 1 | `archW` inlined with `Real.log 2` in place of `Real.log Real.pi`, same proof | REJECT: type mismatch, challenge does not build, exit 1 | 35 s | 5.8 GB |
| tamper 2 | same tampered type, proof `by sorry` | REJECT: "Illegal axiom detected: 'sorryAx'", exit 1 | 80 s | 5.9 GB |

The challenge's type resolves `ArchS3.archW` in the island, not in MMDefs. A tamper of the
registry's own mirrored copy is therefore caught by the drift test rather than by Comparator.
That was checked as well: a scratch copy of MMDefs with `Real.log 2` in `archW` makes
`check_mirrors` report `archW` against `ArchS3_Delta.lean` as drifted.

### What remains

- Operator read-back under an independent identity (`mission audit`). Not run here.
- Grant (`mission grant`) and a CI Comparator pass recorded with `mission comparator-record`
  on a proved node. Neither was run here.
- Separately, `MM_weil_positivity_window_tenth`'s statement/artifact drift blocks
  `judge --pending` for the whole rvm_bridge island. It needs either a qualified restatement
  in `E6Bridge34.lean` or a judge change that applies `--only` before theorem resolution.
