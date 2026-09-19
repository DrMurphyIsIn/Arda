# MM_offline_disjoint_discs -- the E4b isolation lemma, closed (and given a certificate kind)

**Date** 2026-09-18 - **Branch** `mm/offline-disjoint-discs` (base `origin/rh/million-turing`, not pushed)
**Worktree** `/Users/peterwmurphy/arda-mm-offline-disjoint-discs`
**Island** `telperion/examples/quasicrystal/lean` (Lean 4.32.0, Mathlib v4.32.0)

**conjecture1_proved = False.** Nothing here is progress on the Riemann Hypothesis. The lemma proved
below is elementary metric topology about an arbitrary finite set of points; the instances emitted
below take their points as INPUT and assert nothing about where zeta vanishes.

## 1. What the node asked for

Registry node `MM_offline_disjoint_discs` (kind `lemma`, `depends_on = []`, status `open`, blind
read-back by `blind-auditor-2` on 2026-09-16 with no flags). It is the Routes-roadmap E4b isolation
lemma from `QC_RECURRENCE_MEMO.md` section 4.3: the geometric substrate for counting off-line zeros
by disjoint recurrence-deficit discs -- the Rouche-template leg of the finite-grade interderivability
E5.

The statement in `missions/mirrormere/lean/Statements/MM_offline_disjoint_discs.lean`
(node sha256 `bac57ccef7c3f828`):

```lean
theorem offline_disjoint_discs (S : Finset ℂ)
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → Disjoint (Metric.closedBall z r) (Metric.closedBall w r)) ∧
      (∀ z ∈ S, Metric.closedBall z r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) := by sorry
```

## 2. What was delivered

### 2a. The lemma, proved sorry-free

`telperion/examples/quasicrystal/lean/OfflineDiscs.lean` (new `lean_lib` + `defaultTarget`) states
the node's theorem VERBATIM in the island's `Quasicrystal` namespace and proves it. The `diff`
between the node statement and the island statement is empty modulo the stripped `:= by sorry`.

The route avoids `Finset.inf'` and its non-emptiness bookkeeping entirely -- which is where the work
item flagged the only friction -- by proving a one-line-idea helper first:

```lean
theorem exists_pos_lower_bound_of_finset (T : Finset ℝ) (hT : ∀ x ∈ T, 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ T, ε ≤ x
```

by `Finset.induction_on` (`min` at each step; the empty set takes `ε = 1`). Applying it to

* the image of `S.offDiag` under `fun p => dist p.1 p.2` (positive by `dist_pos.mpr` on the
  `mem_offDiag` distinctness witness) gives a separation scale `ε₁`, and
* the image of `S` under `fun z => min z.re (1 - z.re)` (positive by `hstrip`) gives a margin `ε₂`,

the radius is `r := min (ε₁ / 3) (ε₂ / 2)`. Both degenerate cases fall out for free: an empty
`offDiag` makes the pair clause vacuous, an empty `S` makes both clauses vacuous, and the helper
still returns a positive `ε`, so no case split is written anywhere in the proof.

Disjointness is `Metric.closedBall_disjoint_closedBall (h : δ + ε < dist x y)` with
`r + r ≤ 2ε₁/3 < ε₁ ≤ dist z w` closed by `linarith`. Strip containment goes through the second
helper,

```lean
theorem abs_re_sub_le_dist (s z : ℂ) : |s.re - z.re| ≤ dist s z
```

(`Complex.abs_re_le_norm` on `s - z`, `Complex.sub_re`, `dist_eq_norm`) -- the real part is
1-Lipschitz -- so `|s.re - z.re| ≤ r ≤ ε₂/2 < min z.re (1 - z.re)` and `linarith` closes both sides
of the strip.

### 2b. The missing certificate kind, built: `DisjointDiscsEmitter`

The work item asked for exactly this and it is the honest gap: the general lemma is a lemma-pack
entry with NO certificate (there are no numbers in it), but what E5 actually consumes is the
INSTANCE -- a concrete certified point list turned into concrete Rouche discs with an explicit
radius. No existing Telperion kind fit; the nearest geometric shape, `two_scale_separation`, carries
two radii about one centre and has no multi-point or containment content. So a new kind was minted:

| piece | path |
|---|---|
| emitter (kind `disjoint_discs`) | `telperion/src/telperion/emit_disjoint_discs.py` |
| dispatch wiring | `certify.py` `_SPECIAL_KINDS` + `_SPECIAL_DISPATCH`, `__init__.py` exports |
| sensitivity registry stance | `emitter_sensitivity.py` -> `DisjointDiscsEmitter`, `CERTIFICATE_SENSITIVE` + `NEG_CONTROL_ADAPTER` |
| two-sided kernel negative control | `telperion/src/telperion/negctrl_adapters/adapter_disjoint_discs.py` |
| unit tests | `telperion/tests/test_emit_disjoint_discs.py` (8 tests) |
| example + drift gate | `telperion/examples/disjoint_discs/generate.py`, listed in `telperion.toml` as check `disjoint_discs` (group `quick`) |
| emitted island lib | `telperion/examples/quasicrystal/lean/OfflineDiscsInstances.lean` |
| CI job | `.github/workflows/telperion-lean-e2e.yml` -> `disjoint-discs-compiles` |

**Certificate.** Gaussian-rational points `((re_i, im_i))` plus an explicit positive rational radius
`r`. The Layer-1 self-check is exact rational arithmetic, never a float:

* pairwise STRICT separation `(2r)^2 < (re_i - re_j)^2 + (im_i - im_j)^2`;
* strict strip margins `0 < re_i - r` and `re_i + r < 1`.

**Emitted Lean.** Per instance: the point defs, the concrete `Finset`, one disjointness theorem per
pair, one strip-containment theorem per point, and an assembly theorem whose statement is the
registry node's own conclusion with `S` instantiated to that `Finset` -- so the instance literally
witnesses the general lemma's existential at explicit data -- followed by a `statement_match` gate
`example` against the same type string. Squaring is what keeps the pair proof rational: after
`Complex.dist_eq`, `Complex.norm_def` and `Real.lt_sqrt` the square root is GONE before any
arithmetic happens, and `norm_num` finishes on rationals. No root is ever approximated.

**Stance: `CERTIFICATE_SENSITIVE`, with an adapter.** The radius `r` is a supplied number that
appears in the statement AND is what the kernel arithmetic must clear, so inflating it produces a
theorem that is genuinely FALSE, not merely unprovable -- the discs really do intersect. That is a
falsifiable seam, so this kind gets a real Layer-2 control rather than a `not_applicable`.

**Negative controls.** Refused at certify (Layer 1): an overlapping/touching pair `(2r)^2 >= dist^2`;
a radius reaching the strip boundary `r >= min(re, 1 - re)`; a point ON or outside the boundary
(`re = 0`, `re = 1`); a duplicate point; `r <= 0`; non-rational input. Kernel-rejected (Layer 2,
`adapter_disjoint_discs`, bypassing Layer 1 by minting the frozen dataclass by hand): two points
exactly `1/10` apart with a forged `r = 1/10`, so `(2r)^2 = 1/25` is four times the true
`dist^2 = 1/100`. Run against the quasicrystal env:

```
[DisjointDiscsEmitter] negative[kernel REJECTED the forged FALSE proof] | positive[TRUE twin compiled clean]
okay: True
```

The TRUE twin (same points, honest `r = 1/50`) compiles clean -- both bytes of truth, so the control
is valid and not a compile-error artefact. The adapter carries `abs_re_sub_le_dist` in its Lean
`prelude` (a two-line consequence of `Complex.abs_re_le_norm`) so it still runs against a bare
Mathlib env.

### 2c. The instances

`examples/disjoint_discs/generate.py` emits two, both at radius `1/50`:

* `offline_discs_online_pair` -- two centre-line points (`re = 1/2`) at heights `7067/500` and
  `10511/500`;
* `offline_discs_offline_bank` -- the E5-shaped case: those two PLUS a symmetric OFF-LINE pair
  (`re = 2/5` and `re = 3/5`) at height `12505/500`. The off-line pair is `1/5` apart, the tight
  constraint, and `(2r)^2 = 1/625 < 1/25`.

15 theorems, byte-for-byte reproducible (`generate.py --check` is a `quick`-group manifest gate).
**The points are input.** Choosing heights that resemble familiar ordinates makes the instance look
like the object E5 wants to count; it asserts nothing about zeta.

## 3. Guard output (verbatim, new lines only)

Full run is `lake env lean AxiomGuardQC.lean` in `telperion/examples/quasicrystal/lean`; every
pre-existing line is unchanged; all 51 printed declarations carry the three standard axioms, 0 `sorryAx`.

```
'Quasicrystal.exists_pos_lower_bound_of_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.abs_re_sub_le_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.offline_disjoint_discs' depends on axioms: [propext, Classical.choice, Quot.sound]
'OfflineDiscsInstances.offline_discs_online_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'OfflineDiscsInstances.offline_discs_offline_bank' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Registry

`telperion mission link MM_offline_disjoint_discs --artifact ../../examples/quasicrystal/lean/OfflineDiscs.lean
--kind lean_module --via direct` and a `Stalled` attempt recorded in `attempts.jsonl` (the campaign
convention for "proved on a branch, GRANT after reconcile to main"). `telperion mission verify`
reports `verify [mirrormere]: OK`. **The node is NOT granted here** -- the grant gate belongs on
`main` after the reconcile, exactly as `MM_rect_trace_reading` and `MM_spectral_cooked_control` were
handled. Nothing was edited under `missions/` except through the CLI.

## 5. What is NOT closed

* The node is proved but still `open` in the registry pending the reconcile-then-grant.
* E5 itself is untouched. This is the isolation substrate only: no Rouche count, no winding number,
  no argument-principle assembly is claimed. Wiring `offline_discs_offline_bank`-shaped disc banks
  into `WindingCountEmitter` / `AnnulusCountEmitter` is the next joint, and it is not done.
* The general lemma gives SOME radius, not a good one (`min (ε₁/3) (ε₂/2)` is deliberately lossy).
  If a downstream argument ever needs a near-optimal radius, the `disjoint_discs` instance shape --
  where the radius is chosen by hand and only checked -- is the place to put it.
* `conjecture1_proved = False`, unchanged.
