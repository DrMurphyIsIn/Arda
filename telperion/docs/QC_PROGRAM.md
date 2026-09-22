# PROGRAM MIRRORMERE — the reverse-Dyson program (charter + Wave A/B results)

*Kheled-zâram: ANDÚRIL climbs the zeros; MIRRORMERE asks what their reflection
classifies.* Chartered 2026-09-13; Waves A+B executed 2026-09-13/14 by a
six-agent team. `conjecture1_proved = False` — nothing here proves or claims
RH; the program builds the finite, unconditional instruments of Dyson's
reverse proposal (classify 1-D quasicrystals → locate the zeta point set →
extract zero-localization) and maps honestly where the difficulty lives.

## The three pillars (analysis)

- **Pillar 1 (axiomatization):** the zeta comb escapes every classified FQ
  class (gaps → 0, log density, dense multiplicative spectrum). Candidate
  "log-lattice FQ" axioms drafted at four strengths (`QC_AXIOMS_DRAFT.md`);
  the discriminating clause against Davenport–Heilbronn is **weight
  positivity** (Euler product), confirmed mechanically by the zoo.
- **Pillar 2 (classification):** the tame 1-D case is CLOSED in the
  literature loop KS20 → OU20 → ACV24 (Cor 1.4: ℕ-valued FQ ⟺ zero set of a
  Lee–Yang exponential polynomial) — see `QC_LITERATURE.md` for exact
  statements and the where-zeta-escapes table. The needed extension (log
  density, infinitely generated spectrum) is open but not obviously RH-hard.
- **Pillar 3 (the wedge):** the entrance ticket cannot be direct membership
  (RH-equivalent). Two wedge candidates now have formal instruments: partial
  Weil positivity (defect-k, via the Alpöge–Furman inertia arithmetic) and
  complex-supported rigidity (`QC_RIGIDITY_MEMO.md`: R1 ⟺ RH with the
  hardness relocated into ONE temperedness clause; R2 defect-k is the
  publishable rung; R3 finite cases now partially THEOREMS).

## What was built (all merged on rh/million-turing, all independently
re-verified in the canonical worktree)

| Deliverable | Where | Trust grade |
|---|---|---|
| Literature ground truth + zeta-escape table | `telperion/docs/QC_LITERATURE.md` | survey (2 corrections applied post-hoc, see below) |
| Axiom variants A–D + falsification matrix + mechanization contract | `telperion/docs/QC_AXIOMS_DRAFT.md` | draft axioms |
| Rigidity ladder R1/R2/R3 + difficulty map | `telperion/docs/QC_RIGIDITY_MEMO.md` | memo + proofs |
| Rigorous DH driver (`acb_dirichlet_hurwitz`, surd-only κ) | `telperion/src/telperion/arb_dh.py` | Arb |
| Certified DH inventory T≤300: 204 on-line + 4 off-line | `telperion/examples/quasicrystal/zoo_data/dh_zeros.json` | Arb (winding=1 boxes) |
| Certified DH diffraction + off-line cosh signature | zeta island `ZooDH.lean` (5 anchors) | **kernel** |
| Falsification harness (matrix + 7 forged-input controls) | `telperion/examples/quasicrystal/zoo.py` + tests | mechanized |
| QC-1 island: Lee–Yang core, KS construction, boundary lemmas, characterization Props, **TwoFreqRigidity**, RationalFreqReduction | `telperion/examples/quasicrystal/lean/` (26 anchors) | **kernel** |
| Defect dictionary (inertia ↔ defect-k) on verbatim RHLinalg port | zeta island `DefectDictionary.lean` | **kernel** |
| Certified off-line perturbation: defect 0 vs −1.00167·10⁻⁴ < 0 | zeta island `BraggDefect.lean` (13 anchors w/ dictionary) | **kernel** (+1 Arb exp hyp) |

All kernel claims: axioms exactly {propext, Classical.choice, Quot.sound},
0 sorryAx, guards `AxiomGuardQC` / `AxiomGuardZoo` / `AxiomGuardDefect`.

## Headline results

1. **First rigidity theorem** (`twoFreq_realRooted_iff`, kernel): a
   two-frequency exponential sum is real-rooted **iff** its coefficients have
   equal modulus; all zeros lie on one horizontal line regardless. R3(rational)
   is wired end-to-end: Lee–Yang-on-the-circle ⇒ real-rooted.
2. **The zoo verdict** (mechanized, certified inputs): DH dies on the
   predicted clause of every live axiom variant — positivity is the killer —
   and survives the deliberately-dead control C; zeta's unconditional clauses
   pass; 7 forged-input negative controls all flip. No A2 prediction was
   contradicted.
3. **The defect instrument** (kernel): one synthetic off-line pair produces a
   kernel-observable negative defect (−1.00167·10⁻⁴) against the on-line
   configuration's 0 — the Alpöge–Furman signature-(1,1) leakage as a measured
   theorem object, connected to the defect-k dictionary.
4. **Boundary theorems** (kernel): `primeLogSpectrum_dense` (unconditional —
   the prime-log spectrum is not Bohr-discrete) + the pigeonhole gaps→0 driver:
   "zeta escapes the tame class" is now a theorem, not folklore.
5. **Two literature corrections from certified winding integers**: the
   published DH off-line zero at γ≈166.5 has true β≈0.60 (tabulated 0.785
   winds to 0); the tabulated off-line zero at γ≈243.1 is a phantom.

## Corrections ledger (referee-grade honesty)

- "Adve" 1-D characterization attribution: FALSE (arXiv 2203.06733 is
  Favorov, sole author). Corrected in `QC_LITERATURE.md`.
- Strip-FQ prior art EXISTS: Favorov–Değer (2605.10766, 2408.09563) — a
  growth dichotomy, NOT reality-forcing; R1/R2 are positioned as their
  arithmetic-spectrum + defect-graded specialization. (An automated PDF
  summary claiming reality-forcing was caught and discarded against the
  verbatim abstract.)

## The difficulty map (program conclusion, Wave A+B)

RH-hardness enters at exactly ONE place, twice disguised: the FQ-grade
temperedness of the dual comb (arithmetic side), and the rationally-dependent
→ rationally-independent frequency transition (finite side). Everything else
— positivity, multiplicativity, density, the defect arithmetic — is
unconditional and now partly kernel-checked. Wave-2 candidates (decision at
QC-M3): the R2 defect-k rigidity theorem proper; a lightweight in-kernel
N(T) lower-bound brick to discharge BoundaryLemmas' counting hypothesis;
de Branges/Hermite–Biehler is flagged as the deep home of R1 and explicitly
NOT attempted.

**UPDATE 2026-09-21 (PR #593, merged).** The "one place" is now a *theorem*, not an
identification. The goal node's placeholder (`RiemannHypothesis` by fiat, via the
opaque-variable `zeta_FQ_iff_RH`) was replaced by the concrete regularized statement —
Weil positivity of the E8 primes-side functional `weilForm` on Hermitian autocorrelations
`autocorr g` over the smooth compactly supported class — and Weil's criterion was
formalized in both directions on the rvm_bridge island: `zeta_comb_membership_iff_rh`
(forward: RH ⇒ positivity via `limit_explicit_formula` + `paperFT_weilTest`; converse:
positivity ⇒ RH via the Gaussian dominance lemma O2 for an arbitrary off-line zero and the
Gaussian approximation lemma O1′ for the test class, both unconditional and RH-free).
Registry: `MM_rh_implies_weil_positivity`, `MM_weil_positivity_implies_rh`,
`MM_gaussian_dominance`, `MM_gaussian_approx`, `MM_gaussian_transfer`,
`MM_zeta_comb_membership_iff_rh` all `proved` after four blind audits. The goal node
`MM_zeta_comb_membership` remains `draft`: it is RH, and the difficulty map's single wall is
exactly the `∀ g` quantifier of that statement. `conjecture1_proved = False`.
