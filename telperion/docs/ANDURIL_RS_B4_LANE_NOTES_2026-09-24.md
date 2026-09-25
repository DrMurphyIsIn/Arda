# LANE_NOTES_B4 -- lane B4 (worktree arda-rs-b4, zeta_reflection island, Lean v4.32.0)

conjecture1_proved = False.  Finite-height sign certification infrastructure only.

## Task (2026-09-24)
Brick B4 of the Riemann-Siegel kernel ladder: an in-kernel, decide-able interval evaluator for
Zmain(t) = 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p), for ALL phi
with |phi - thetaMain t| <= 1/t, and its soundness against RSInt.rs_Z_C0.

## Rules held
- Git read-only.  No edits under telperion/missions/ or .github/.  New files only, prefix RS4_.
- lakefile.toml: 5 appended [[lean_lib]] blocks (RS4_Eval, RS4_Sound, RS4_Z, RS4_Demo, RS4_AxiomGuard).
- No sorry/admit/native_decide/axiom/opaque/implemented_by/ofReduceBool/extern/unsafe (docstring
  mentions only).  No emoji.  All Lean through scratchpad/leanlock.sh.
- Untrusted numerics: scratchpad/b4/emit.py (mpmath + exact Python ints).

## Design (verify, not compute; reuse, not duplicate)
- Dirichlet part: psum t N = sum n^(-1/2 - it) and log N come from the island's ArbEcon.run (the
  Nat-only evaluator, Probes/ArbEconomics_Eval) after N-1 steps; soundness via ArbEcon.run_sound.
  Main sum = cos(phi) Re psum - sin(phi) Im psum (RS4.main_sum_eq, via ArbEcon.cpow_term).
- Phase: the certificate brackets TH0 <= phi 2^P <= TH1 for the WHOLE ball; ArbEcon.trig /
  trig_sound then give cos/sin balls whose radius absorbs the ball width.
  thetaMain = t log a - t/2 - pi/8, log a = log N + log(1+y), y = p/N <= 1/2; log(1+y) by the
  degree-8 alternating series + tail 2y^9 (Mathlib abs_log_sub_add_sum_range_le), exact integer check.
- a = sqrt(t/2pi): bracket checked by squaring against the pi/2 ball of the config.  N = floor a and
  p > 0 follow.  (t/2pi)^(-1/4) = a^(-1/2): bracket checked by squaring.
- Psi: brackets of 2 pi p and 2 pi (p - p^2 + 1/16) (cos is even), ArbEcon.trig for both cosines, and
  a quotient check QuotOK that REQUIRES the cos(2 pi p) ball to exclude 0 (else the checker fails);
  it outputs cos(2 pi p) ≠ 0.
- Assembly: DIntvProd.DIntv mul/sub/add/neg (DIntvDef/DIntvCorrect mul_sound/add_sound/sub_sound/
  neg_sound), exponent -2P; claimed box [zlo, zhi] checked to contain the assembled one.
- Config: ArbEcon.OrderK.cfg64 tn tq (EMZetaHighCfg64), validated for all heights by
  ArbEcon.OrderK.valid64 (EMZetaHighCheck).  No new per-height Valid proofs.

## Files (lines)
- RS4_Eval.lean (203): Cert, lpPos/lpNeg, ballD, negIf, dstate, mainBox, c0Box, zBox, QuotOK,
  Checks (24 integer conditions), ChecksP + Decidable, checks_of, check.
- RS4_Sound.lean (827): real-side facts (a, N, p, y, log, phase ball, amplitude, angles, quotient,
  main-sum identity, DIntv assembly) and THE HEADLINE `RS4.check_sound`.
- RS4_Z.lean (71): `RS4.rs4_Z_enclosure`, `RS4.rs4_sign_pos`, `RS4.rs4_sign_neg` (glue to rs_Z_C0,
  2 t^(-3/4) <= 2/1000 for t >= 10000 via `tpow_le`).
- RS4_Demo.lean (118): t = 10000.5 and t = 10000 accepted by decide +kernel; certified signs;
  Hardy Z(10000.5) in [0.29604, 0.30105]; three negative controls rejected by decide +kernel.
- RS4_AxiomGuard.lean (101): 78 #print axioms, all subsets of [propext, Classical.choice, Quot.sound].
- Total 1,320 lines.

## Headline statements
- RS4.check_sound : Valid c t K -> check c z = true ->
    10000 <= t ∧ rsNn t = z.N ∧ 0 < rsFrac t ∧ cos(2 pi rsFrac t) ≠ 0 ∧
    ∀ phi, |phi - rsThetaMain t| <= 1/t -> zlo/2^(2P) <= Zmain t phi <= zhi/2^(2P)
  (Zmain is verbatim the main term of RSInt.rs_Z_C0.)
- RS4.rs4_Z_enclosure : same hypotheses -> ∃ M phi, 0 < M ∧ Gammaℝ(1/2+it) = M e^{i phi} ∧
    |phi - thetaMain t| <= 1/t ∧ zlo/2^(2P) - 2/1000 <= Re Lambda(1/2+it)/M <= zhi/2^(2P) + 2/1000.
- RS4.Demo.sign_A : 0 < Re completedRiemannZeta(1/2 + (20001/2) i).
- RS4.Demo.sign_B : Re completedRiemannZeta(1/2 + 10000 i) < 0.

## Measurements
- Each decide +kernel check (accept or reject): ~15 ms kernel type-checking (profiler), N = 39.
- Whole RS4_Demo file: ~26 s wall, almost all of it Mathlib import; max RSS ~5.5 GB (import mmap).
  Full lane build: green, 8697 jobs.
- Certified box half-width: ~2.1e-4 at t=10000.5, ~3.8e-4 at t=10000.  This is dominated by the
  phase ball (2|S|/t, |S| = |psum t N|), i.e. by RSTheta's 1/t, not by the arithmetic (P = 64).
- mpmath: Zmain(10000.5) = 0.2985403, siegelz = 0.2985402; Zmain(10000) = -0.3413976, siegelz = -0.3413947.

## Remaining (B5 and beyond; not claimed here)
- B5: band sign certificate: many dyadic sample heights t_i = tn_i/2^tq (emitter + one decide per
  point, ~15 ms each at N ~ 40..126), IVT via continuity of Re Lambda on the line, glue to the
  Turing-band / argument-principle counting at T = 1e5.
- The sign lemmas use the loose t-free margin 2/1000 (from t >= 10000).  Near 1e5 a t-dependent margin
  2 t^(-3/4) (~3.6e-4) would help Gram-interval sampling; `tpow_le` generalizes directly.
- The phase ball 1/t (RSTheta) caps the box width at ~2|S|/t; a sharper theta bracket would tighten it.
