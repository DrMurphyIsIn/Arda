# MM_recurrence_deficit_eq_excess — the Face 4 ⟷ Face 1 dictionary row, discharged

> **`conjecture1_proved = False`.** What is proved below is a ONE-RELATION ring
> identity in `Real.exp` plus a two-factor positivity. It is a *dictionary row*
> between two finite instruments — the Bagchi recurrence clearance (Face 4) and
> the Bragg/Weil amplification excess (Face 1) — and says nothing about zeta.
> Certifying one recurrence instance is not progress toward RH; the UNIFORM
> Bagchi recurrence **is** RH and is untouched here.

**Agent:** `mm-recurrence-deficit` (MIRRORMERE prover).
**Branch:** `mm/recurrence-deficit` (worktree `/Users/peterwmurphy/arda-mm-recurrence-deficit`),
base `origin/rh/million-turing`. **Not pushed; no PR.**
**Island:** `telperion/examples/zeta_zero_localization` (v4.32.0, shard `zzl_aux`),
`.lake` symlinked to the built cache at
`/Users/peterwmurphy/arda-million/telperion/examples/zeta_zero_localization/lean/.lake`
(and `zzl_aux/.lake` to the matching shard cache). No `lake exe cache get` was run.

---

## 1. What was proved

`telperion/examples/zeta_zero_localization/lean/RecurrenceDeficit.lean`, namespace
`Quasicrystal`, sorry-free:

```lean
theorem recurrence_deficit_eq_excess :
    recurrenceDeficit (1 / 10) = excess ∧
    ∀ δ : ℝ, 0 < δ → 0 < recurrenceDeficit δ
```

stated VERBATIM from the registry statement file
`telperion/missions/mirrormere/lean/Statements/MM_recurrence_deficit_eq_excess.lean`
(the grant gate's normalized containment check was pre-flighted in-session and
MATCHES). `excess` is verbatim island vocabulary (`BraggDefect.lean`:
`excess = Aoff - Aon = e^(1/10) + e^(-1/10) - 2`); `recurrenceDeficit` is AUTHORED
in the registry's vocabulary mirror `Statements/MMDefs.lean` (lines 61–62) and is
mirrored into the artifact **byte-identically**, in the same namespace
`Quasicrystal`, as the `rvm_bridge` `E6Bridge*.lean` modules do (verified in-session
by substring equality against MMDefs, so a drift would be caught before the gate).

A companion, explicitly NOT a registry node (QC_RECURRENCE §4 item 2 names it):

```lean
theorem recurrence_deficit_sq_eq_abs_defect :
    recurrenceDeficit (1 / 10) ^ 2 = |defectFunctional excess|
```

— the second-order (Weil-energy) reading of the same row: the squared *linear*
clearance is the magnitude of the *quadratic* defect witness.

### The mathematics, stated plainly

For displacement `δ` the two one-sided clearances of the modelled off-line pair are
`g₊(δ) = e^δ − 1` (outer mirror factor) and `g₋(δ) = 1 − e^(−δ)` (inner
transported-zero factor). Their PRODUCT telescopes against the single relation
`e^δ · e^(−δ) = 1`:

```
(e^δ − 1)(1 − e^(−δ)) = e^δ + e^(−δ) − 1 − e^δ e^(−δ) = e^δ + e^(−δ) − 2 .
```

At `δ = 1/10` the right side is exactly `BraggDefect.excess`
(`0.01000833611160719797…`, re-checked numerically against the memo). Positivity is
the product of two strictly positive factors (`Real.one_lt_exp_iff`,
`Real.exp_lt_one_iff`).

**Adversarial note (kept from the brief, and endorsed):** the content is one ring
relation. It is legitimately a lemma and a legitimate dictionary row; it is *not*
evidence, and must not be sold as more. The memo's own §4 item 2 grades it exactly
this way ("kernel-ready now"), and its §4 item 5 marks the RH-hard wall it does not
approach.

---

## 2. The new certificate kind — `exp_laurent_identity`

The brief flagged this shape as lacking a certificate type. It now has one, built
and dogfooded here rather than hand-written.

**Emitter:** `telperion/src/telperion/emit_exp_laurent_identity.py`
(`ExpLaurentIdentityEmitter`, kind `exp_laurent_identity`).

**The shape.** Many "exp bookkeeping" rows in this corpus are Laurent polynomials
in the single transcendental `y = e^d` with `z = e^(−d)` its formal inverse:
amplitude sums `y + z` (a `2 cosh` channel), one-sided clearances `y − 1`, `1 − z`,
their products and squares. Every TRUE identity among them is a polynomial identity
in `ℚ[y, z]` modulo the one relation `y·z − 1`; every FALSE one leaves a nonzero
remainder.

```
claim     lhs = rhs
certify   lhs − rhs = cofactor · (y·z − 1)   in ℚ[y, z]   (sympy, exact; re-multiplied and re-checked)
emit      have hrel : Real.exp d * Real.exp (-d) = 1 := by rw [← Real.exp_add]; norm_num
          linear_combination (cofactor : ℝ) * hrel
```

The **cofactor is the load-bearing certificate**: `linear_combination` re-derives
the goal from it by `ring`, so a corrupted cofactor — or a corrupted side — leaves
a residue the kernel will not close. Stance declared in
`emitter_sensitivity.REGISTRY` as `CERTIFICATE_SENSITIVE` with
`NEG_CONTROL_ADAPTER`.

**Two Layer-1 refusals** (both unit-tested, both re-run by the generator before it
writes anything):

1. **Non-identity** — nonzero remainder. The motivating instance is the mistake
   QC_RECURRENCE §6 caught in ITSELF and corrected: the clearances' **SUM**,
   `(e^d − 1) + (1 − e^(−d)) = 2d + O(d³)`, is **not** the excess; only the product
   is. Residue `2 − 2e^(−d)`; REFUSED.
2. **Relation not load-bearing** — cofactor `0`, i.e. the claim never uses
   `e^d · e^(−d) = 1`. That is an ordinary ring identity and belongs to
   `IdentityEmitter`; emitting it here would advertise a certificate carrying no
   information. REFUSED.

Plus two contract refusals (symbols outside the two generators; a non-polynomial
side).

**Negative control (kernel-gated, two-sided).**
`telperion/src/telperion/negctrl_adapters/adapter_exp_laurent_identity.py` forges the
SUM-for-PRODUCT twin *while keeping the true row's cofactor* `−1`, bypassing Layer 1
so that Layer 2 decides. Run in-session against the built v4.32 env:

```
[ExpLaurentIdentityEmitter] negative[kernel REJECTED the forged FALSE proof] | positive[TRUE twin compiled clean]
kernel_rejects: True   true_compiles: True   okay: True
```

It is picked up automatically by the existing parametrized gate
`tests/test_certificate_sensitivity.py::test_generic_negative_control_holds`.

**Generator / drift gate.** `telperion/examples/exp_laurent_deficit/generate.py`
emits both rows INTO the zzl island as
`examples/zeta_zero_localization/lean/ExpLaurentDeficit.lean` (same toolchain pin,
same `zzl_aux` lakefile, next to its consumer). It is listed in `telperion.toml` as
`[[check]] name = "exp_laurent_deficit"`, group `quick`
(`telperion verify` manifest-completeness: green; `--check` drift: byte-for-byte
green). Emitted theorems:

```lean
theorem expLaurent_recurrence_deficit (d : ℝ) :
    (Real.exp d - 1) * (1 - Real.exp (-d)) = Real.exp d + Real.exp (-d) - 2
theorem expLaurent_recurrence_deficit_sq (d : ℝ) :
    (Real.exp d - 1) ^ 2 * (1 - Real.exp (-d)) ^ 2 = (Real.exp d + Real.exp (-d) - 2) ^ 2
```

`RecurrenceDeficit.lean` consumes the first one at `δ = 1/10` after unfolding
`recurrenceDeficit`, `excess`, `Aoff`, `Aon` — so the node's algebraic core is the
emitted certificate, not hand-rolled tactics.

Renderer note (a real footgun, handled): sympy canonicalizes `Mul`/`Add` argument
order and Lean multiplication is **not** definitionally commutative, so the emitter
reassembles each side in a fixed channel order (`e^d` before `e^(−d)` before
constants). Without that, the emitted statement would read
`(1 − e^(−d)) * (e^d − 1)` and the consumer's `exact` would fail.

---

## 3. Island wiring and the guard

* `zzl_aux/lakefile.toml`: `ExpLaurentDeficit` and `RecurrenceDeficit` added as
  `lean_lib`s and to `defaultTargets`.
* `AxiomGuardBragg.lean`: imports both modules, documents the new anchors, and adds
  four `#print axioms` lines. CI already runs this guard after `lake build` in
  `telperion-lean-e2e.yml` (the `for g in AxiomGuardBragg AxiomGuardDefect
  AxiomGuardZoo` loop), so no workflow change was needed.
* `lake build` in `zzl_aux`: `Build completed successfully (8775 jobs)`.

Guard output (verbatim, run exactly as CI runs it):

```
== AxiomGuardBragg
'CosEnclosure.cos_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.cos_base_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.cos_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.cos_double_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.cos_encl' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.cos_encl_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'CosEnclosure.add_encl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHInBoxCore.support_eq_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'RHInBoxCore.sum_over_box_zeros_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraggSupport.sum_cos_over_zero_support_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpLaurentDeficit.expLaurent_recurrence_deficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpLaurentDeficit.expLaurent_recurrence_deficit_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.recurrence_deficit_eq_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.recurrence_deficit_sq_eq_abs_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraggH100.bragg_amplitude_h100' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraggH100.bragg_amplitude_h100_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `ofReduceBool`, no `error:`.


### Python test status

`pytest tests` (full suite, 39m): **2224 passed, 109 skipped, 14 failed**. Every
failure is in `tests/test_rhinbox.py` / `tests/test_zeroloc_end_to_end.py` and is
ENVIRONMENTAL, not a regression: those tests call `lake exe cache get` inside the
zzl island, which in this worktree has its `.lake` symlinked to the shared built
cache whose mathlib `cache` executable is not built
(`could not execute external process .../mathlib/.lake/build/bin/cache`, exit 255).
They touch nothing this change introduces. The gates that DO cover this work all
pass: `tests/test_emit_exp_laurent_identity.py` (9 tests),
`tests/test_certificate_sensitivity.py` (including the parametrized kernel-gated
`test_generic_negative_control_holds`), `tests/test_emitter_registry.py`,
`tests/test_missions_registry.py`, and `telperion verify` (manifest completeness +
the new `--check` drift gate).

---

## 4. Registry

Through the mission CLI only (no hand edits under `telperion/missions/`):

* `mission link MM_recurrence_deficit_eq_excess --artifact
  ../../examples/zeta_zero_localization/lean/RecurrenceDeficit.lean --kind lean_module
  --via direct` — recorded; **status unchanged (`open`)**.
* `mission attempt … --verdict Proved` — ledger row appended to
  `missions/mirrormere/attempts.jsonl`.
* `mission verify mirrormere` — `verify [mirrormere]: OK`.
* **`mission grant` NOT run.** Per `mission.toml` design §9 the artifact lives on
  the `rh/million-turing` line, and grants are deferred to the branch reconcile —
  the same discipline the `MM_bragg_defect_witness` and `MM_offline_pairs_le_defect`
  ledger rows record. The gate's containment check was pre-flighted and passes, so
  the grant is a mechanical step at reconcile time.

---

## 5. What is NOT claimed

* No RH progress. `conjecture1_proved = False`.
* The node is a dictionary row between two *finite, synthetic* instruments: the
  `BraggDefect` configuration is a planted off-line pair, not a zero of ζ.
* The `ε₀ = d` identification is exact only for the rank-1 pair-block model of
  QC_RECURRENCE §2 row (a); the conversion of the dimensionless deficit into a
  genuine `sup_K |ζ(·+iτ) − ζ|` tolerance is leading-order in `|ζ′|` and remains
  open (memo §4 item 4), as does the disjoint-disc/deficit-count row (§4 item 3).
* The new emitter certifies *identities*, not positivity; the strict-positivity leg
  of the node is proved directly (`mul_pos` over the two clearances) and is not a
  certificate shape.

## 6. Follow-on the new kind unlocks (not done here)

`exp_laurent_identity` is the natural certifier for the rest of the `2 cosh`
bookkeeping on this island — `Aoff`/`Aon` channel algebra, the `defect_eq_two`
two-channel excesses `d₁, d₂`, and any future `e^{kδ}` ladder rows — each of which
is currently hand-written or inline. Migrating those to the emitter would put the
same kernel-gated cofactor control under all of them.
