# Route C synthesis, frontier report (workflow wf_0568fe15-630, 2026-09-23)

Raw input to ROUTE_C_SYNTHESIS_2026-09-23.md, committed so that its unanchored estimates are traceable. conjecture1_proved = False.

Route C literature frontier and ranked next milestones (2026-09-23)

conjecture1_proved = False. Nothing below proves RH or moves Route C's wall. Every upper bound Λ ≤ c with c > 0 is strictly weaker than RH.

## 0. Corrections found this session

1. **Wrong path in the brief.** `/Users/peterwmurphy/arda-routec-syn/telperion/docs/RH_CRUX_RESEARCH_2026-09-22.md` does not exist. The document is at `/Users/peterwmurphy/arda-crux2/telperion/docs/RH_CRUX_RESEARCH_2026-09-22.md`, with an identical copy (both 927 lines) under `arda-cl-crux`.
2. **The wall map is stale on Route C.** `WALL_BACKLOG_MAP_2026-09-18.md:48-50` still lists the dbn nodes as BLOCKED with no readback, and `:274-277` says "Route C currently has *zero* workable nodes". On the current branch, all four dbn nodes are `status = "proved"` with two blind readbacks each: `missions/rh/nodes/RH_dbn_{H0_eq_xi,H0_zero_strip,rh_iff_H0_real_zeros,debruijn_real_zeros}.toml`, the last granted 2026-09-23 in commit b524f7e7d.
3. **Platt–Trudgian states Λ ≤ 0.2 themselves.** `RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md:29` says their abstract does not mention Λ. That is true of the abstract, but the paper body does: arXiv:2004.09765v1 §3.4, "Corollary 2. We have Λ ≤ 0.2", obtained from P15 Table 1 row 2 once H > 2.51·10^12.
4. **A web summary invented a result.** It gave Platt–Trudgian "Theorem 1: Λ ≤ 0.2" and "4×10^12 flops". Both are wrong. The PDF text says Theorem 1 is RH up to 3,000,175,332,800, and the compute was about 7.5 million core-hours.

## 1. Citations checked (Crossref metadata plus arXiv full text)

| Result | Citation (verified) | Method |
|---|---|---|
| Λ ≤ 1/2 | de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17(3) (1950) 197–226 | Heat-flow strip contraction: if every zero of H_{t0} has \|Im\| ≤ y0, then zeros of H_t have y² ≤ max(y0² − 2(t−t0), 0) (P15 Thm 3.2, citing [5, Thm 13]). Combined with the ξ strip. |
| −∞ < Λ ≤ 1/2; conjecture Λ ≥ 0 | Newman, *Fourier transforms with only real zeros*, Proc. AMS 61(2) (1976) 245–251 | Existence of the threshold constant |
| Λ < 1/2 | Ki, Kim, Lee, *On the de Bruijn–Newman constant*, Adv. Math. 222(1) (2009) 281–306 | Asymptotics of H_t for fixed t > 0: large-x zeros are real and simple, with t-dependent, ineffective constants and o(1) errors (P15 p.10, text lines 420-423). The paper is paywalled and its exact deduction of strictness was not read. |
| Lower bounds (Rodgers–Tao Table 1) | −50 Csordas–Norfolk–Varga 1988 (Numer. Math. 52); −5 te Riele 1991 (Numer. Math. 58); −0.385 Norfolk–Ruttan–Varga 1992; −0.0991 Csordas–Ruttan–Varga 1991 (Numer. Algorithms 1); −4.379e-6 Csordas–Smith–Varga 1994 (Constr. Approx. 10); −5.895e-9 Csordas–Odlyzko–Smith–Varga 1993 (ETNA 1); −2.63e-9 Odlyzko 2000 (Numer. Algorithms 25); −1.15e-11 Saouter–Gourdon–Demichel, Math. Comp. 80 (2011) 2281–2287 | The last four use Lehmer pairs of zeros via the Csordas–Smith–Varga repulsion criterion; Csordas–Ruttan–Varga uses Laguerre inequalities (RT pp.2-3). |
| Λ ≥ 0 | Rodgers, Tao, Forum Math. Pi 8 (2020) e6, doi 10.1017/fmp.2020.6 (arXiv v5, 61 pp.) | Assume Λ < 0. Zero dynamics for Λ < t ≤ 0 (after CSV) push the zeros of H_0 into local equilibrium, an approximate arithmetic progression. That contradicts Montgomery's pair correlation. |
| Λ ≥ 0, second proof | Dobner, *A proof of Newman's conjecture for the extended Selberg class*, Acta Arith. 201 (2021) 29–62 | Approximates ξ_t for t < 0 by a Dirichlet series with off-line zeros. Uses no information about zeta zeros. |
| Λ ≤ 0.22 | D.H.J. Polymath, Res. Math. Sci. 6(3) (2019) art. 31, doi 10.1007/s40687-019-0193-1, arXiv:1904.12438 (68 pp.) | Thm 1.2 barrier criterion with t0 = y0 = 0.2, X = 6·10^10 + 83952 − 0.5; hypothesis (i) from Platt, Math. Comp. 86 (2017) 2449–2467 (RH to 3.06·10^10) |
| Λ ≤ 0.2 | Platt, Trudgian, Bull. LMS 53(3) (2021) 792–797, doi 10.1112/blms.12460 | RH to 3·10^12 fed into P15 Table 1 row 2 (X = 5·10^12 + 194858, t0 = 0.186, y0 = 0.16733) |

The 2026 unreviewed claims (Gomila Λ ≤ 0.1787854; Gordon Λ < 0.158) come from `RH_ROUTES_ROADMAP_2026-09-16.md:198-202` and were not re-checked this session because the web-search budget was exhausted. They are not anchors.

**P15's criterion as the paper states it.** Theorem 1.2 and Proposition 3.3 (pp.2, 15) conclude Λ ≤ t0 + y0²/2 from three conditions:
- **(i)** H_0 has no zeros with 0 ≤ x ≤ X and y ≥ √(y0² + 2t0). Proposition 3.3 needs only this zero-free rectangle, not full RH to height X/2. Theorem 1.2(i) uses the stronger σ ≥ (1+y0)/2.
- **(ii)** H_{t0} has no zeros in the canopy x ≥ X + √(1−y0²), y0 ≤ y ≤ √(1−2t0).
- **(iii)** A barrier at X ≤ x ≤ X+1 holds for every 0 ≤ t ≤ t0.

The analytic engine is Theorem 1.3, an effective Riemann–Siegel-type approximation H_t ≈ A + B − C with explicit errors, valid for 0 < t ≤ 1/2, 0 ≤ y ≤ 1, x ≥ 200 (text lines 145-231).

**Barrier compute in P15.** 785,052 (t, s) pairs over 152 values of t, with N = 69,098 terms each. Direct evaluation took 78.5 h; Taylor multi-evaluation cut it to about 0.025 h (§7).

**P15 §10.** "if one has numerically verified the Riemann hypothesis up to a large height T, this should soon lead to a bound of the form Λ ≤ O(1/log T)." Table 1 extends to Λ ≤ 0.10 at X ≈ 9·10^21.

## 2. What round 1 says about the wall, reconciled with the current state

- **Crux doc** (`arda-crux2/.../RH_CRUX_RESEARCH_2026-09-22.md:72`): "(II) C10: Λ_dBN ≤ 0 … a margin statement on an infimum. It is not formalized here." This is still true. No registry node states `∀ t ≥ 0, ∀ z, H t z = 0 → z.im = 0`.
- **Roadmap** (`RH_ROUTES_ROADMAP_2026-09-16.md:185-231`): C10 is an "rh-hard-wall" with exp(C/ε) height per rung (`:225`), and "P(route proves RH) ≈ 0" (`:230`). P15 §10 and Table 1 support this: better upper bounds are an F4 instance factory, on the wrong side of the quantifier as `WALL_BACKLOG_MAP:30` defines it. Going from 0.22 to 0.10 needs T ≈ 4.5·10^21, and c → 0 needs T → ∞.
- **R3 withdrawal** (`WALL_BACKLOG_MAP:141-145`): the C4 equivalence is F4-workable and is not the wall. This is now discharged (`DBNRealZerosIffFinal.lean`).
- **Salvage items in the crux doc** (`:239, :257, :865`): the "local de Bruijn lemma" and the "edge band" remain unrefereed against de Bruijn 1950 and P15. Treat them as unverified.

## 3. Program assets (file:line)

**dbn island** (`telperion/examples/dbn/lean`, Lean v4.34.0-rc1, 6,140 lines including the 465-line guard):
- `H`: `DBNDefs.lean:413`.
- `Φ`: `DBNDefs.lean:211`.
- The C2 representation `dbn_H0_eq_xi`: `DBNXi.lean`.
- The strip `H0_zero_strip`: `DBNStrip.lean:482`.
- The generic discrete de Bruijn step `shiftAvg_zero_im_sq_le`: `DBNStep.lean:401`.
- Its iterate `zero_im_sq_le_of_shiftAvg_iterate`: `DBNStep.lean:459`. It is generic in the function family F and the initial strip Δ2.
- Approximants `Gδ = (shiftAvg δ)^[N] (H 0)`: `DBNHeatApprox.lean:123,202`.
- Hurwitz: `DBNHurwitz.lean:116`.
- Contraction from H_0 only, with Δ2 = 1 hardcoded through `H0ZeroFreeOffStrip`: `DBNDeBruijnReduction.lean:41,94`.
- Capstone `H_zero_im_sq_le` (t ≥ 0 ⇒ y² ≤ max(1−2t, 0)) and `dbn_debruijn_real_zeros`: `DBNHadamardApprox.lean:83,97`.

The de Bruijn part itself (Step, StepControls, HeatApprox, Hurwitz, Hadamard*, Reduction, Approx) is about 3,200 lines. That is the calibration for the estimates below.

**Other assets:**
- Λ is deliberately not defined, to avoid the sInf trap: `DBN_FOUNDATIONS_C2C4_2026-09-17.md` §5. Non-emptiness is now done (C3); the up-set property and a lower bound are still missing.
- Hypothesis-free height floor, no zeta zero with 0 < Im < 55/16: `missions/anduril/nodes/AND_height_floor_kernel.toml` (proved). G2 companion: `AND_g2_reflected_band_kernel.toml` (proved).
- Zero ladder: Arb-conditional to 640000, carrying 20,758 Arb binders (`CAMPAIGN_REMAINDER_2026-09-22.md:30-31`).
- EM evaluator cost:
  - 227–297 µs per term (`ANDURIL_ARB_DISCHARGE_2026-09-23.md:205-212`).
  - With order-13 EM, h280000 takes about 6.2 days and 10^6 about 79 days (`:259-262`).
  - The RS remainder is estimated at 5,000–11,000 lines (`:48-51`).
  - Per-point RS cannot reach 10^13 (`CAMPAIGN_REMAINDER:33`).
- Effective dVP region: `riemannZeta_ne_zero_region` (`examples/zero_free_bridge/lean/DlvpZetaZeroFree.lean:57`), but dlvpRateC ≈ 7.3e-6 (`li_positivity/lean/DlvpZetaRateEffective.lean:28,282`). Used for P15(i) at T ≈ 10^6, this only yields c > 0.4999989, so it is useless for Route C.
- Mathlib has `riemannZeta_ne_zero_of_one_le_re` (`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411`).
- Zeta23 (`rvm_bridge`, Lean v4.33.0-rc2): unconditional Riemann–von Mangoldt, a 2/3 proportion of zeros on the line, and the Weil explicit formula. These are relevant to Rodgers–Tao but sit on a different toolchain pin from the dbn island.

## 4. Assessments

**(a) Ki–Kim–Lee, Λ < 1/2.**
- **Method:** qualitative large-x asymptotics of H_t at fixed t > 0 (KKL Thms 1.3–1.4 as summarised by P15), then a de Bruijn-type step.
- **The gap:** getting strictness from "finitely many nonreal zeros at t0" needs a strict per-zero form of the contraction. The supremum of \|Im\| over the zeros of H_0 may equal 1, so the open strip alone does not give it. KKL's exact argument was not read.
- **Cost:** about 6k–12k lines. Almost all of it is the asymptotic saddle-point and Stirling analysis, which is the same object class as P15 Thm 1.3. No compute.
- **Verdict:** do not staff it on its own. It produces no numeral, which fails the F2 test (effective constants compose, existential ones do not). The effective route (M6 below) costs about the same and yields an explicit c0 < 1/2.

**(b) Λ ≤ 0.22 by the P15 method.**
- **Analysis:**
  - Thm 1.2 / Prop 3.3 needs zero dynamics via Prop 3.1 (motion of simple zeros through the Hadamard product, repeated zeros, minimal time, Rouché): about 2.5k–5k lines.
  - Thm 1.3 (effective A + B − C with the E1–E3 errors, Sections 4–6): about 10k–20k lines.
  - Thm 3.2 (parametric de Bruijn): about 0.5k–1k lines.
- **Finite computation:**
  - **(iii) Barrier.** Direct: 5.4·10^10 terms × 230 µs ≈ 145 core-days, about 4.5 days on 32 cores. With a kernel port of P15's Taylor multi-evaluation (a 3,000× gain in P15) it is on the order of hours, but that port is itself an unformalized design.
  - **(ii) Canopy.** Per-N exact-rational scalar inequalities from the Euler-mollifier bound. These suit the Telperion emitter.
  - **(i) Hypothesis.** A zero-free rectangle to height 3.06·10^10. This is infeasible kernel-only, since 10^6 is already about 11 weeks. It can only be carried as a named hypothesis (Platt 2017), in the way the Arb binders are.
- **Total:** about 13k–26k lines plus days of compute. The resulting theorem is hypothesis-carrying at (i).

**(c) Rodgers–Tao, Λ ≥ 0.**
- **Statement form:** sInf-free, `∀ t < 0, ∃ z, H t z = 0 ∧ z.im ≠ 0`.
- **RT route:** 61 pp.; needs a Riemann–von Mangoldt count for H_t at negative t, the Csordas–Smith–Varga dynamics, and Montgomery pair correlation. Zeta23's explicit formula and RvM are partial inputs, on another toolchain. About 20k–40k lines.
- **Dobner route:** 34 pp.; needs no zero information. About 8k–15k lines. It would also give Λ > −∞, which makes Λ definable.
- **Value for RH:** zero. It is the other direction: it shows RH ⟺ Λ = 0, i.e. no slack. Its value is as a formalization first and as sharper evidence that C10 has no margin.
- **Ranking:** low. Track it; do not staff.

**(d) Anything cheaper between 1/2 and 0.22.** No published intermediate step exists between KKL and P15; P15 itself went straight to 0.22. The structural observation is that Prop 3.3(i) becomes cheap when X is small:
- The hypothesis-free height floor gives (i) at X = 55/8 with no ladder at all.
- The Arb-conditional ladder gives (i) at X ≈ 1.28·10^6.

Either way, the cost moves to (ii) and (iii) at small or moderate x. For x < 200 that needs a direct H_t evaluator outside Thm 1.3's range. Since published Λ ≤ 0.2, (ii) is true for any t0 ≥ 0.2; the open question is certifiable margin. The best c0 reachable at these X was not computed this session.

## 5. Ranked next milestones

**M1. Parametric de Bruijn and the sInf-free C10 clause.**
- **Statements:**
  - (a) Thm 3.2 / de Bruijn Thm 13: `(∀ z, H t0 z = 0 → z.im^2 ≤ Y) → ∀ t ≥ t0, ∀ z, H t z = 0 → z.im^2 ≤ max (Y − 2(t−t0)) 0`.
  - (b) The up-set property of {t : H_t has only real zeros}.
  - (c) `RH ↔ ∀ t ≥ 0, ∀ z, H t z = 0 → z.im = 0`, from C4 plus (a) with Y = 0.
- **Method:** reweight the approximants by e^{t0 u²} (`DBNHeatApprox.lean:119-127`); re-prove order < 2 growth; reuse the generic iterate (`DBNStep.lean:459`) and Hurwitz.
- **Size:** 500–1,000 lines, no compute.
- **Value:** highest. It registers C10 exactly (crux `:72`), and every Λ ≤ c consumes (a).

**M0. Numeric scoping (no Lean).**
- **Task:** run P15's public code (github km-git-acc/dbn_upper_bound, P15 ref [20]) to find the smallest certifiable t0 + y0²/2 at X = 55/8 (hypothesis-free) and at X ≈ 1.28·10^6 (Arb-conditional). Record mesh counts and N.
- **Cost:** days of CPU.
- **Value:** high. It fixes the numeral target for M6. The roadmap's C8 projection G1 ~0.36 (`:223`) is a single-anchor extrapolation.

**M4. The P15 criterion as a conditional kernel theorem.**
- **Statement:** Prop 3.3 plus Thm 1.2, with (i)–(iii) as named Props; conclusion `∀ t ≥ t0 + y0²/2`, real zeros.
- **Method:** Prop 3.1 zero dynamics through the island's Hadamard data, the minimal-time argument, Rouché. The open-strip piece at y = 1 comes via the Mathlib `Nonvanishing.lean:411` lemma plus C2 (150–300 lines).
- **Size:** 2.5k–5k lines, no compute.
- **Value:** high. It turns every future bound into finite obligations. A discrete barrier variant built on `shiftAvg` is a speculative, unverified alternative.

**M5. C6/C7 core: effective H_t approximation (P15 Thm 1.3).**
- **Size:** 10k–20k lines. This is the long pole. It shares Γ/Stirling/EM infrastructure with the ANDURIL RS remainder (5k–11k lines).
- **Compute:** none for the theorem itself.
- **Value:** enabling. Without it nothing below 1/2 is effective.

**M6. First effective hypothesis-free Λ ≤ c0 < 1/2.**
- **Method:** M1 + M4 + M5; (i) from `AND_height_floor_kernel`; a small-x rigorous H_t evaluator for (ii)/(iii); canopy and barrier certificates.
- **Compute:** likely minutes to hours of kernel time, pending M0.
- **Value:** first formally certified bound with an explicit c0 < 1/2. The P15-scale target size is about 13k–26k lines (see (b)).

**M7. Arb-conditional Λ ≤ c on the ladder.**
- **Target:** the 640k ladder gives X ≈ 1.28·10^6; c from M0.
- **Honesty:** hypothesis-carrying (`RH_ROUTES_ROADMAP:223`).
- **Value:** medium. It will not beat 0.2.

**M8. Λ ≤ 0.22 / 0.2 reproduction.** Only with (i) carried as a Platt / Platt–Trudgian hypothesis; barrier compute about 145 core-days naive. Value: a record-rigor artifact, not RH progress.

**M9. Dobner (Λ ≥ 0).** 8k–15k lines; track only.

**Not recommended:** a standalone ineffective KKL proof, and a C5 Lehmer-pair Λ ≥ −ε bound (superseded by Rodgers–Tao).

**C10 (Λ ≤ 0) stays the wall.** Under P15 §10 the upper-bound rungs cost exp(C/ε) in verified height, so no M-item approaches it.

Source extracts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/` (p15.txt, pt.txt, rt.txt).

Sources:
- [arXiv:1904.12438](https://arxiv.org/abs/1904.12438)
- [arXiv:1801.05914](https://arxiv.org/abs/1801.05914)
- [arXiv:2004.09765](https://arxiv.org/abs/2004.09765)
- [arXiv:2005.05142](https://arxiv.org/abs/2005.05142)
- [Wikipedia: de Bruijn–Newman constant](https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant)
- Crossref records for doi 10.1016/j.aim.2009.04.003, 10.1017/fmp.2020.6, 10.1007/s40687-019-0193-1, 10.1112/blms.12460, 10.1090/s0002-9939-1976-0434982-5, 10.1215/s0012-7094-50-01720-0, 10.1090/S0025-5718-2011-02472-5, 10.1090/mcom/3198, 10.4064/aa200603-23-7