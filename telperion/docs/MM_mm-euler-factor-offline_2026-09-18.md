# MM_euler_factor_section_offline -- the p = 2 Euler-factor section is NOT real-rooted

**conjecture1_proved = False.**  This closes ONE registry node: a finite, unconditional
*negative control*.  It is not RH progress, not a step toward RH, and by construction it is the
statement that a per-rung line-membership claim FAILS.

Date: 2026-09-18.  Branch `mm/mm-euler-factor-offline` (base `origin/rh/million-turing`).
Island: `telperion/examples/quasicrystal/lean` (Mathlib v4.32.0).
Node: `MM_euler_factor_section_offline` (MIRRORMERE, torus-section ladder rung T2).

## 1. What was proved

The p-th Euler factor `1 - p^{-s}`, read on the critical line `s = 1/2 + i x`, is the
two-frequency section `twoFreq(1, -(1/sqrt p); 0, -log p)`.  For p = 2 the registry statement is

```lean
theorem euler_factor_section_offline :
    ¬ (∀ x : ℂ,
        twoFreq 1 ((-(1 / Real.sqrt 2) : ℝ) : ℂ) 0 (-(Real.log 2)) x = 0 → x.im = 0)
```

proved sorry-free in `telperion/examples/quasicrystal/lean/EulerFactorOffline.lean`
(namespace `TorusSectionLadder`).  Route: the `.mp` direction of the island's R3(n=2) rigidity
theorem `Quasicrystal.twoFreq_realRooted_iff` turns real-rootedness into `‖c₁‖ = ‖c₂‖`, i.e.
`1 = 1/sqrt 2`, refuted by `Real.one_lt_sqrt_two` through `div_lt_one`.  The two side facts the
kernel needs are `-(1/sqrt 2) ≠ 0` and `0 ≠ -log 2` (from `Real.log_pos`), each its own lemma.

Three companion theorems in the same file (NOT nodes):

* `euler_factor_section_witness` -- the EXPLICIT off-line zero `x = i/2`:
  `e^{-i (log 2)(i/2)} = e^{(log 2)/2} = sqrt 2` (via `Real.exp_half` + `Real.exp_log`), so
  `1 - (1/sqrt 2)·sqrt 2 = 0`.  The negative control therefore carries a witness, not merely a
  refuted universal.
* `euler_factor_section_witness_im` -- `Im (i/2) = 1/2`, the uniform off-line displacement
  (the zeros are `s = 2 pi i k / log 2`, i.e. `Re s = 0`).
* `euler_factor_section_offline_of_witness` -- the SAME node statement re-derived directly from
  the witness, an independent second route that does not use the iff at all.

`statement_match_check` (telperion/src/telperion/statement_match.py) reports `all_match=True`
against the registry statement text for the node theorem and for the emitted `_node` form below.

## 2. New certificate shape: selfinversive_rigidity `mode="offline"`

The natural shape here is a certificate, so rather than leave it hand-written the existing
`SelfInversiveRigidityEmitter` gained a second MODE (the item's tool request
`tool-selfinversive-offline-mode`).  `telperion/src/telperion/emit_selfinversive_rigidity.py`:

* **Coefficients** may now be radicals `r·sqrt(q)` (r, q rational, r ≠ 0, q > 0), so the modulus
  `|c|² = r²·q` stays EXACT rational arithmetic -- the `1/sqrt p` of an Euler factor is expressible
  without leaving exact arithmetic.
* **Frequencies** may be rational or `r·log q` (q an integer ≥ 2).
* **Verdict** `|c₁|² ≠ |c₂|²` emits `¬ real-rooted` through the `.mp` direction; the kernel
  re-derives `‖c‖² = r²·q` (`Complex.norm_real`, `sq_abs`, `Real.sq_sqrt`) and closes the
  inequality by `norm_num`, so a corrupted normSq breaks the emitted rewrite rather than
  silently weakening the statement.
* **Euler-factor shape** `twoFreq(1, -(1/sqrt p); 0, -log p)` is detected, and the emitter
  additionally ships the `x = i/2` witness, the witness-route refutation, the two coefficient
  normalisation lemmas, and `…_node`: the SAME refutation restated with the coefficients spelled
  `1` and `-(1/sqrt p)` -- i.e. the mission-registry statement VERBATIM, emitted.
* **NEGATIVE CONTROL of the offline mode** (mirror of the default mode's): EQUAL modulus is
  REFUSED -- equal modulus forces real-rootedness, so there is no off-line zero to certify.  Also
  refused: a zero coefficient, a non-positive radicand, and any frequency pair whose distinctness
  is not kernel-certifiable (a nonzero rational against `r·log q`, or two logs of different bases,
  would need transcendence / independence of logarithms -- refused, not faked).

Dogfood: `telperion/examples/selfinversive_rigidity/generate.py` now also emits
`SelfInversiveOfflineInstances.lean` into the island, with p = 2, 3, 5 (18 theorems; p = 3 and 5
are free extras and are NOT nodes).  The existing `[[check]] selfinversive_rigidity` in
`telperion/telperion.toml` covers both libs, because it runs the same generator with `--check`;
drift check passes byte-for-byte.  The frozen `SelfInversiveRigidityInstances.lean` changed only
in its input-hash header line (the hash covers the emitter source).

Sensitivity registry (`emitter_sensitivity.py`) stance text extended to document the mode.  Tests:
`telperion/tests/test_emit_selfinversive_rigidity.py`, 13 passed (6 new, covering the positive
certificate, the equal-modulus refusal, zero/negative-radicand refusal, the uncertifiable
frequency pairs, the accepted distinctness cases, the emitted refutation/witness/node forms, the
witness-free generic instance, and an unknown mode).

## 3. Registration

* `lakefile.toml`: `EulerFactorOffline` and `SelfInversiveOfflineInstances` added as `lean_lib`s
  and to `defaultTargets`.
* `AxiomGuardQC.lean`: 6 + 12 new `#print axioms` lines; all report
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `ofReduceBool`.
* CI (`.github/workflows/telperion-lean-e2e.yml`, job `selfinversive-rigidity-compiles`): builds
  the offline lib and the node module, then runs the axiom guard.
* Registry: `telperion mission link` (artifact `EulerFactorOffline.lean`, `lean_module`, `direct`)
  and `telperion mission attempt` (verdict `Proved`).  Status left `open`; the grant is deferred
  to the branch reconcile, as for the island's other million-turing artifacts.
  `telperion mission verify mirrormere` -> `verify [mirrormere]: OK`.

## 4. Footgun found (island-wide)

Worktrees that symlink the same built `.lake` share one olean build directory.  A module built
under a name a teammate also uses is silently CLOBBERED: my first `TorusSectionLadder.lean`
guarded clean, then a teammate's same-named module replaced the olean and `import
TorusSectionLadder` stopped resolving my declarations, surfacing as "unknown namespace", not as a
build error.  The module was renamed `EulerFactorOffline.lean` (namespace kept as
`TorusSectionLadder`, so it merges with the T1 ladder file at reconcile).  Rule of thumb: one
module name per agent per shared cache, and re-run `lake build` immediately before any guard or
statement-match run.

## 5. Scope

The content is the `.mp` direction of an existing island iff plus one exact norm inequality
(`1 ≠ 1/sqrt 2`, needing `1 < sqrt 2`) and one `log 2 ≠ 0` fact -- deliberately small, and not
simp-trivial.  Its value is as a CERTIFIED negative control: it pins down that the torus-section
ladder's per-rung sections are uniformly off-line at displacement 1/2, so critical-line membership
cannot be read off any finite rung (the Turan/Montgomery obstruction, in-house).  Nothing here
bears on RH.  conjecture1_proved = False.
