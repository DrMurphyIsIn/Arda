# BG / `hwh` consolidated summary (branch `bg/multihub-hnorm`, PR #488)

Definitive index of the refutation -> salvage -> reduction -> certificate arc. Everything below is either
**kernel-checked** (`[propext, Classical.choice, Quot.sound]`, guarded in `AxiomGuard.lean`, built in CI via
`proof-lean.yml`) or **exhaustively verified** in exact `fractions.Fraction`. `conjecture1_proved = False`
throughout -- no completeness is claimed.

## Objective

`Aobj(t) = per(L(t)) / prod_v deg(v) = sum over matchings M of prod_{(u,v) in M} 1/(deg u * deg v)` -- the
Brualdi-Goldwasser Laplacian ratio, whose per-size maximizer over trees is OPEN (Pant 2026 refuted the
Wu-Dong-Lai subdivided-star conjecture). The repo's sorry-free conditional capstone
`conjecture1_of_layers_fixedN` reduces conjecture 1 to `Hnorm` (tree -> hub-backbone) + `Hdom` (done).

## 1. Refutation of the single-hub `Hnorm` at aligned n=52  (commits 0bcc06dc, 583de7d4)

`T(6,6,6,6)` (4-hub caterpillar, n=52) has `Aobj = 1180837892027061/26306674688 ~= 44887.39`, exceeding the
best Balanced+Capped hub `tieArgmax(52) = 4695479375868117/104857600000 ~= 44779.58`. Min hub size 46 =>
the size-52 Balanced+Capped class is exactly the 4 single hubs, so `T` beats them all: the single-hub
`Hnorm` is FALSE.
- Verified: 4 independent exact engines + adversarial skeptic AIRTIGHT (`BG_HNORM_REFUTATION_2026-09-11.md`,
  `_engineA/B/C`, `indep_verify_engineD.py`, `_verify52.py`).
- Kernel: `R47HnormFalse52.lean` -- `aobj_T52_eq`, `tieArgmax_52_lt_T52`, `r47_hnorm_false_at_52`,
  `hnorm_capstone_false` (the precise negation of the capstone's `Hnorm` hypothesis).

## 2. Salvage: broadened capstone + the correction  (commits 58ce894c, 0122b794)

`R47HnormMulti.lean`: broaden the normal form from Balanced+Capped single hub to ANY multi-hub
cherry-backbone `backboneU s`. `conjecture1_of_HnormMulti` (the `Balanced+Capped`-free capstone),
`hnormMulti_holds_at_T52` (the refutation dissolves -- `T52` is itself a backbone),
`singleHub_refuted_but_multiHub_open`. **Correction**: the n=52 refutation killed the SEPARATE
general->Balanced+Capped normalization, NOT `hwh`; `hnorm_of_wholehub` produces the general-backbone
`Hnorm`, so `conjecture1_of_HnormMulti_of_wholehub` shows `hwh` (unrefuted) discharges the broadened capstone.

## 3. Reduction: `hwh` = the tree->backbone straightening  (empirical + `R47HwhStatus`)

`hwh` <=> every tree is `Aobj`-dominated by a hub-backbone of its size <=> the per-size maximizer is a
multi-hub cherry-backbone. Empirically the straightening move always exists (`viable_all`, exhaustive
**n <= 15**, 1793 defective trees, 0 failures) but is ADAPTIVE.

## 4. Exact decomposition grid  (commits 73d27fa0, fcb312d7, 9ed961bc, 1473c05e)

For any piece relocation (leaf/cherry/arm/sub-star; `p,w` adjacent or not), the exact `Aobj` change:
`R47HwhLeafDecomp` (leaf, `B1/B2`), `R47HwhPieceDecomp` (general piece via cavity scalars `Z, rho`),
`R47HwhAdjDecomp` (adjacent leaf, `B2adj`), `R47HwhAdjPieceDecomp` (adjacent general piece). All exact
identities verified (0 mismatches), all `field_simp; ring` kernel-clean.

## 5. `B2` proven from an actual matching theory  (commits 2a1d40d1, 4392d8cf)

`R47MatchingSum.lean`: self-contained weighted matching-sum theory. `ZsumAvoid_antitone` (deletion
monotonicity -- the `B2` crux), `B2_termwise` (`Z(H-q-r) <= Z(H)`), `B2_bound` (`P11 <= card * P00`). The
`B2` hypothesis is now a THEOREM.

## 6. The `B1` kernel: slices + g-dominance  (commits db180c0c, c5d55ef4, 8f1b8751)

`B1 = avg_{q~p} g(q) - avg_{r~w} g(r)`, `g(v) = Z(H-v)/deg_v`. Proven slices (`R47HwhB1Partial.lean`):
`B1_nonneg_of_P01_zero`, `cherry_forming_monotone`, and `B1_nonneg_of_gdominance` (g-dominance =>
`B1 >= 0`; covers ~98%). Every degree/rule/averaging certificate for full `B1` was tried and FALSIFIED
(`B1 existence -- every natural certificate FAILS`).

## 7. UNIFORM certificate for the symmetric multi-star obstruction  (commits f74768e8, b207a488, 28e5939f)

The localized open core -- the multi-star (centre + hubs) family that broke every certificate -- is CLOSED
uniformly by the de-branching move (detach a hub -> pendant path via leaf-leaf edge):
- `R47HwhSymStarCert.symstar_move_certificate` -- balanced `ST(k,m)`, all `k>=3, m>=2` (linear-in-k, two
  shifted cubics).
- `R47HwhSymStar3Cert.symstar3_move_certificate` -- general 3-hub, arbitrary `m_i>=2`.
- `R47HwhSymStarGenCert` -- **k-uniform, arbitrary hub sizes, any spectators**: `Aobj` change is LINEAR in
  the spectator symmetric functions `S, S1`; `coeff_S1 >= 0`, `alpha_j <= 2` gives `S1 >= S(k-2)/2`, and
  `G = coeff_S + (k-2)/2 coeff_S1 >= 0` (both via the all-nonneg-coefficient shift). So the move is
  `Aobj`-monotone (and defect-reducing, size-preserving) on the ENTIRE symmetric multi-star family.
General closed form (verified): `Aobj(multi-star) = (2/k) sum_i prod_{j!=i} alpha_j`, `alpha_i=(2m_i+1)/(m_i+1)`.

## 8. Assembly + the open kernel  (commits a1d7a6c6, 3756c030)

`R47HwhAssembly.hwh_of_extended_coverage`: `hwh` follows from the proven move-class interfaces + `Hcoverage`
(every defective tree lies in a handled class). **`Hcoverage` for all `n` is the SOLE open obligation** and
IS the open BG exhaustiveness. Demonstrated NOT closeable by a fixed finite class-set: the classification
"uncovered => symmetric multi-star" holds at n<=14 but FAILS at n=15 (radius-3 residual needing large-
component moves); the hard-tree residual grows uncleanly.

## Honest status

- `hwh` is TRUE on every tree tested (exhaustive n <= 15, 0 failures).
- Everything provable is proven and kernel-clean; the symmetric obstruction -- the hard heart -- is closed
  uniformly for all `k` and hub sizes.
- The remaining gap is `Hcoverage` for all `n` = the open Brualdi-Goldwasser structural problem; it is
  provably not a mechanical merge (no fixed class-set is exhaustive). `conjecture1_proved = False`.

## File index

Lean (`proof/formalization/R3Cert/`): `R47HnormFalse52`, `R47HnormMulti`, `R47HwhLeafDecomp`,
`R47HwhPieceDecomp`, `R47HwhAdjDecomp`, `R47HwhAdjPieceDecomp`, `R47MatchingSum`, `R47HwhB1Partial`,
`R47HwhSymStarCert`, `R47HwhSymStar3Cert`, `R47HwhSymStarGenCert`, `R47HwhAssembly`. All guarded in
`AxiomGuard.lean`, built in `.github/workflows/proof-lean.yml`.
Verification (`proof/verification/`): `_verify52.py`, `_engineA/B/C`, `indep_verify_engineD.py` (in
telperion/scratch), `bg_maximizer_family.py`, `hwh_viability.py`, `hwh_leaf/piece/adj_decomposition.py`,
`symstar_uniform_cert.py`.
Docs (`proof/docs/`): `BG_HNORM_REFUTATION_2026-09-11`, `BG_HNORM_MULTIHUB_SALVAGE_2026-09-11`,
`BG_HWH_STATUS_2026-09-11`, `BG_HWH_RESEARCH_NOTE_2026-09-11`, and this file.
