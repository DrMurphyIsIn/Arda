# Audit testimony A1 -- RH_dbn_rh_iff_real_zeros_nonneg_t (rh)

Blind auditor A1, no author context. conjecture1_proved = False.

- pass: true
- axioms_clean: true
- statement_byte_identical: true
- conjecture1_proved = False

## (1) Own read-back (before reading the artifact)

Registry file `missions/rh/lean/Statements/RH_dbn_rh_iff_real_zeros_nonneg_t.lean`: strip-form RH over
Mathlib `riemannZeta` (every zero with 0 < Re < 1 has Re = 1/2) is equivalent to: for every t >= 0, every
zero of `DBN.H t` is real. `DBN.H t z = ∫_{(0,∞)} e^{t u^2} Φ(u) cos(z u) du` with the standard de
Bruijn-Newman Φ (RHDefs mirror equals examples/dbn/lean/DBNDefs.lean lines 40-41, 211-214, 408-413).
Classically the right side is Λ <= 0, i.e. RH itself. Expected proof shape: C4 (RH <-> H_0 real zeros)
plus the de Bruijn up-set; converse by t = 0.

## (2) Canonical gate

- `R.load_campaign(Path('missions/rh'))` finds the node (status draft, depends_on C4 + upset).
- `V.statement_matches(DBNM1RHIff.lean, V._normalized_statement(node, root))` = True.
- `V.artifact_incompleteness_markers`: [] on the artifact and on each of the 19 modules of its dbn-island
  import closure (DBNDefs ... DBNXiRiemann).

## (3) Build and axioms

- `lake build --no-build`: "All targets up-to-date (8807 jobs)", exit 0.
- Own probe: `#print axioms dbn_rh_iff_real_zeros_nonneg_t` = [propext, Classical.choice, Quot.sound];
  likewise for `dbn_rh_iff_H0_real_zeros` and `dbn_real_zeros_upset`. An `example` restating the
  registry statement verbatim elaborated against the theorem. Probe file deleted afterwards.

## (4) Left side and non-circularity

- Left side is character-identical to the left side of the C4 registry node
  `RH_dbn_rh_iff_H0_real_zeros` and of the island theorem `dbn_rh_iff_H0_real_zeros`.
- Proof: `rw [dbn_rh_iff_H0_real_zeros]`; forward via `dbn_real_zeros_upset 0 t ht`; backward `h 0 le_rfl`.
  No hypothesis; no `RiemannHypothesis`, no `axiom`, no RH-strength input anywhere in the import closure
  (grep; only benign implicit `variable`s). It proves neither side.

## (5) Establishes / does not

Establishes: strip-RH <-> (∀ t >= 0, all zeros of H_t real), unconditionally, axiom-clean.
Does not: prove RH, prove either side, define or bound Λ. conjecture1_proved = False.
