# Publication Ledger

A running, deliberately conservative tally of results from this research program. The point of this
file is to keep us honest: "publication-worthy" here means *a result that could plausibly stand up in a
venue after a literature check and peer review* — not a result we are certain is novel. Novelty
assessments below are **provisional** and made without an exhaustive literature search; several
candidates are very likely already known. Nothing here is peer-reviewed. Update as status changes.

Status legend: **PROVED** (complete argument, machine-verified where noted) · **PARTIAL** (rigorous
sub-result of an open problem) · **OPEN** (conjecture, not proved) · **TOOL** (methodological).
Novelty legend: **likely-known** · **novelty-uncertain (needs lit check)** · **plausibly-novel**.

| # | Result | Status | Scope | Novelty (provisional) | Location |
|---|--------|--------|-------|-----------------------|----------|
| 1 | Permanental dominance `per(L) ≥ imm_λ(L)/χ_λ(1)` for **tree/forest Laplacians**, all λ | PROVED (verified n≤8) | trees/forests only — **not** general PSD | **likely-known** (immanants of trees: Merris–Watkins &c.; normalized-char argument is standard) | `telperion/docs/permanental_dominance_trees.md`, `telperion/src/telperion/perm_dominance.py` |
| 2 | Lieb permanental dominance for **general PSD Hermitian** matrices | **OPEN** | all PSD — famous open conjecture (1966) | n/a | — |
| 3 | Brualdi–Goldwasser `Φ ≤ 1` on the **near-star family** `N(c,k)`, equality iff `c+k=5`, via 23-adic integrality | PARTIAL (rigorous sub-result) | near-star family only (full BG since solved, see entry 4) | **plausibly-novel** as an integrality-based proof of this sub-case — *needs lit check* | `proof/verification/near_star_arithmetic_proof.py` |
| 4 | Brualdi–Goldwasser maximizer (all trees, every n ≥ 4): an explicit spider of cherry arms; growth constant (621/64)^(1/11); uniqueness up to isomorphism except n = 21 | **PROVED** (Lean kernel-checked, standard axioms only; maximum and maximizer also accepted by a second kernel, nanoda, via Comparator; uniqueness kernel-checked, statement-matched by Comparator but no second-kernel verdict). **Not yet refereed.** | the 1984 question itself | answers the open question (Pant 2026 refuted the earlier Wu–Dong–Lai answer); a paper is in preparation | [brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser) (doi:10.5281/zenodo.22983412); `proof/formalization/R3Cert/BGMaximizerAll.lean` |
| 5 | Gauge-tower / benchmark-factor / product-telescope decomposition localizing the BG crux to one benchmark constant + one integer identity | TOOL + PARTIAL | framing/machinery (BG itself was later solved by a different route, entry 4) | **plausibly-novel** framing — *needs lit check* | `telperion/src/telperion/{gauge_lift,benchmark_factor,telescope_product}.py` |
| 6 | Telperion: sympy→Lean kernel-checked certificate pipeline (untrusted generator / trusted kernel) | TOOL | methodology | **novelty-uncertain** (proof-producing pipelines exist; specific design may be presentable) | `telperion/` |
| 7 | Spider↔star extremal sweep of immanant ratios of trees; curvature "turn-on" sharp at the bosonic (permanent) vertex | (exploratory, verified n≤8) | trees; interpretive | **likely-known** (immanantal graph theory) | session notes / memory |
| 8 | Kernel-checked symbolic-n SOS lower bound for Grigoriev knapsack: rank-one collapse of harmonic blocks, g_k = ∏(n−2j)/(2(n−2j−1)), uniform in degree (51 Lean theorems, axioms clean) | PROVED (machine-verified; scalar layer + d=4 Gram bridge; harmonic-completeness layer Python-pinned) | knapsack system, all odd n, all degrees | math **likely-known** (Grigoriev 2001, Laurent; KLM 2020 rank-one symmetry technique); *formalization* **plausibly-novel** (first kernel-checked asymptotic proof-complexity lower bound — needs formalization-lit check) | `telperion/examples/knapsack_sos/WRITEUP.md`, `telperion/examples/g1_floors/lean/{KnapsackSOS,BridgeD4,SumEqProd}.lean` |
| 9 | 3XOR per-instance certified SOS lower bound machinery: closure-consistency ⟹ block-rank-one PSD, with Tseitin-on-Petersen (refutation width exactly 6) as canonical certified instance | PARTIAL (exact prototype green; Lean structure theorem in progress) | per-instance; asymptotic expansion layer not formalized | structure **likely-known** (Grigoriev/Schoenebeck); certified per-instance pipeline **novelty-uncertain** | `telperion/examples/knapsack_sos/xor3_pseudoexpectation.py` |
| 10 | Capped-joint g-step arc: achievability correction (unconstrained Case-2 false on `μ∈(1/2,1)`; non-leaf messages `μ≤1/2`) + kernel-checked closure of the config g-step at every arity via the abstract cavity g-lemma `gV_le` | PARTIAL (kernel-checked sub-result of BG, open at the time; closure `gstep_le_one_achievable` landed via PR #20) | single-hub wiring of the ≤-half (BG itself was later solved by a different route, entry 4) | **novelty-uncertain** — *needs lit check* | `proof/formalization/R3Cert/CappedJointAchievable.lean`, `telperion/examples/g1_floors/lean/GLemma.lean` |
| 11 | Chvátal–Gomory integer-rounding certificate emitter (VIPR-style, `omega`-discharged) + the kernel-checked near-star integer-window theorem where every continuous certificate provably fails | TOOL + PARTIAL (window fragment only) | integer linear arithmetic emitter; BG window `s∈[4,6]` | **novelty-uncertain** (VIPR checking is known; a Lean-kernel CG pipeline may be presentable) — *needs lit check* | `telperion/src/telperion/emit_cg_round.py`, `telperion/examples/cg_round/NearStarWindow.lean` |
| 12 | Two-frequency rigidity: all zeros of c₁e^{iλ₁x}+c₂e^{iλ₂x} on one horizontal line; real-rooted ⟺ \|c₁\|=\|c₂\| (kernel, both directions) + rational-frequency Lee–Yang reduction | PROVED (machine-verified) | finite exponential sums; the R3 base cases of the MIRRORMERE rigidity ladder | **likely-known** as classical fact; *kernel formalization + reverse-Dyson framing* novelty-uncertain — needs lit check | `telperion/examples/quasicrystal/lean/{TwoFreqRigidity,RationalFreqReduction}.lean` |
| 13 | Certified control zoo: rigorous DH zero inventory (T≤300, winding boxes) with TWO literature corrections (γ≈166.5 true β≈0.60; γ≈243.1 phantom) + kernel-certified DH diffraction with off-line cosh signature + mechanized axiom-falsification harness | TOOL + PARTIAL | Davenport–Heilbronn control object | corrections **plausibly-novel** (contradict published tables; Arb-grade evidence); harness methodology novelty-uncertain | `telperion/src/telperion/arb_dh.py`, `ZooDH.lean`, `telperion/examples/quasicrystal/zoo.py` |
| 14 | Defect dictionary (Weil-compression negative index ↔ off-line pairs, defect-k language) + first certified off-line perturbation experiment (kernel-observable leakage gap −1.00167e-4 < 0) | PARTIAL (kernel; RH-hard half carried as named hyp) | finite compressions; instrument for the defect-k rigidity rung | dictionary framing **plausibly-novel**; underlying inertia arithmetic is Alpöge–Furman | `DefectDictionary.lean`, `BraggDefect.lean` |
| 15 | Kernel boundary theorems: prime-log spectrum dense (not Bohr-discrete, unconditional) + pigeonhole gaps→0 driver — "zeta escapes the tame FQ classification" as theorems | PROVED (machine-verified; counting input as explicit hyp on the space side) | boundary of the ACV/KS/OU classification | facts **likely-known**; kernel form + program role plausibly-novel | `telperion/examples/quasicrystal/lean/BoundaryLemmas.lean` |

## Honest notes

- **Entry 1** is real and machine-checked but almost certainly not new; treat as an exposition/verification
  contribution at most, pending a literature check (Merris, Brualdi, Grone, Chan–Lam on immanants of trees).
- **Entry 3** was the strongest genuinely-partial contribution while the problem was open; it is a *sub-case*
  of Brualdi–Goldwasser, now subsumed by entry 4.
- **Entry 4** (full BG) is now **PROVED** in the sense that matters for this ledger: a complete argument,
  checked end to end by the Lean kernel, with the main statement also accepted by a second, independent kernel.
  It has **not** been peer-reviewed, and human scrutiny of the statement and definitions is still the open step.
  (The repository flag `conjecture1_proved = False` refers to the campaign's own first, conditional route, not to
  this result.)
- **Entry 2** (Lieb, general PSD) remains **OPEN**. Do not record it as proved unless a complete,
  independently-checked argument exists.
- Before any submission: (a) full literature search per entry, (b) independent proof-checking (Lean CI green
  for the formalized parts), (c) explicit scope statement so a special case is never presented as the general
  conjecture.
