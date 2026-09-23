# Audit testimony: AND_height_floor_kernel (anduril), auditor A1 (blind), 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (identical modulo whitespace; artifact declares it inside `namespace HeightFloor`)
- conjecture1_proved = False

## 1. Read-back (written before reading the artifact)
For every real H and every complex rho: if riemannZeta rho = 0, 0 < Im rho, and Im rho <= H, then
55/16 <= |Im rho|. H is inert, since the extra hypothesis only weakens the claim. The statement quantifies
over all of C, not only the critical strip, so Re <= 0 and Re >= 1 have to be handled. It is true: the first
nontrivial zero is at Im = 14.1347...

## 2. Statement gate (canonical path)
- `R.load_campaign(Path('telperion/missions/anduril'))`, node `AND_height_floor_kernel` (status draft).
- `V.statement_matches(HeightFloor.lean, V._normalized_statement(node, root))` = True.
- Independent whitespace-normalized extraction of `theorem height_floor (H` ... `:=` from both files: equal.
- Lean probe restating the registry text verbatim, `:= HeightFloor.height_floor H`, typechecks.
- `V.artifact_incompleteness_markers` = [] on HeightFloor, HeightFloorBoxes, HeightFloorEM, HeightFloorTrig,
  HeightFloorCheck, ZetaEMSum, EMZetaTail, EMZeta, EMZetaComplex, ZetaZeroConfinement, DlvpZetaSymmetry,
  DlvpZetaZeroFree.

## 3. Build and axioms
- `leanlock.sh lake build HeightFloor`: Build completed successfully (8732 jobs), exit 0. Only deprecation
  warnings, and no `sorry` warnings.
- Probe `#print axioms`: HeightFloor.height_floor, the verbatim-restated probe theorem, and strip_clear_low
  each depend on [propext, Classical.choice, Quot.sound]. The probe file has been deleted.

## 4. Hidden hypotheses
- `#check` shows height_floor, strip_clear_low, G2_norm_le_of_zero, Boxes.G2_norm_gt and
  no_low_zeros_of_strip_clear with no Arb/oracle/membership binders. The only premise of
  no_low_zeros_of_strip_clear (hclear_low) is supplied by the proved strip_clear_low.
- grep for hmem/hArb/hLine/oracle in the closure: none. grep for native_decide/ofReduceBool/axiom/opaque/
  implemented_by in the closure files (including the Dlvp* modules): none. The #print axioms result confirms
  the transitive closure independently.

## 5. Mathematics and coverage
- mpmath: first zero 0.5 + 14.13472514173469i, which is above 55/16 = 3.4375. On a 121x121 grid over
  [1/2,1]x[0,55/16], min |(s-1)zeta(s)| = 0.7302 at (1/2, 0), which matches the memo's 0.730. min |G2| = 0.7301.
  The EM order-3 N=2 tail bound used in G2_norm_le_of_zero has max 0.189 <= 23/100. |G2 - (s-1)zeta| <= tail was
  checked numerically at every interior grid point.
- Re >= 1 and Re <= 0 are excluded by ZetaZeroConfinement.zeta_zero_re_mem_strip (Mathlib
  riemannZeta_ne_zero_of_one_le_re, plus reflection of 1-rho for Re <= 0).
- 0 < Re < 1/2 folds onto the right half through rho -> 1 - conj rho (ZeroFreeBridge.riemannZeta_reflect_line_eq_zero,
  which preserves Im).
- 1/2 <= Re < 1, 0 < Im <= 55/16: G2_norm_le_of_zero (<= 23/100) contradicts G2_norm_gt (> 1/4). G2_norm_gt is
  proved on the CLOSED rectangle [1/2,1]x[0,55/16].
- Boxes: 32 in total, as sigma slabs [1/2,3/4] and [3/4,1], each with 16 closed t-slabs [55j/256, 55(j+1)/256].
  A script check confirms the endpoints are contiguous from 0 to 55/16. The dispatch in slab_0/slab_1/G2_norm_gt
  uses le_total, so there are no gaps at box boundaries. Per-box checks use kernel `decide`, not native_decide.

## 6. What this does and does not establish
It establishes a finite, low-height zero-free statement: there is no zeta zero with 0 < Im rho < 55/16, at every
height H. This discharges the hgamma binder of the ladder capstones. It does NOT establish RH or anything about
zeros on or off the line at larger heights. conjecture1_proved = False.
