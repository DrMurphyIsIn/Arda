# LANE_NOTES_B5 -- lane B5 (worktree arda-rs-b5, branch cl/rs-b5, zeta_reflection island, Lean v4.32.0)

conjecture1_proved = False.  This is finite-height zero certification infrastructure. It gives LOWER counts of
on-line zeros only.

## Rules held
- Git read-only.  Nothing under telperion/missions/ or .github/ was touched.  Only new files were added, all prefixed RS5_.
  No RS_/RSSeam_/RS4_ file was edited.
- lakefile.toml: 45 appended [[lean_lib]] blocks, append-only (+204 lines, 0 removed).
- No sorry/admit/native_decide/axiom/opaque/implemented_by/ofReduceBool/extern/unsafe in code. Two
  docstrings mention them.  No emoji.  Every Lean call went through scratchpad/leanlock.sh.
- Untrusted numerics live only in scratchpad/b5/: emit5.py (numpy RS sign scan, lane B4 cert emitter,
  exact box by Lean `#reduce`, mpmath nzeros cross-check), write_band.py, floorcert.py, gen_*.py.

## 1. RETARGET (t >= 509)
`RS4.Checks` hard-codes `10000 * 2^tq <= tn`.  Two new pieces work around that:
- RS5_Eval: `RS5.Checks5` / `ChecksP5` / `check5` are the RS4 versions VERBATIM except for the floor 509.
  They are generated mechanically from RS4_Eval, and every computable piece (Cert, zBox, mainBox, c0Box,
  QuotOK, lpPos, ...) is reused from RS4.
- RS5_Sound: RS4_Sound sections 1-9 re-stated for Checks5.  Only `t_ge` and `tn_pos` read the floor.  The
  height-free helpers are reused through `open RS4 (...)`.  HEADLINE `RS5.check5_sound`.
- RS5_Z:
  * `rs5_Z_enclosure`: this is check5 glued to `RSSeam.rs_Z_C0_seam`, with the EXACT margin (13/5) t^(-3/4).
  * `tpow_le_margin`: the integer check `MarginOK c E` (one^4 (2^tq)^3 <= E^4 tn^3) gives t^(-3/4) <= E/2^P.
  * Also: `rs5_Z_enclosure_E` (rational margin), `rs5_sign_pos` / `rs5_sign_neg`, and `sampleOK_sign`.

## 2. IVT corollary (RS5_Band, RS5_Demo)
- `zeta_zero_of_completed_zero`: Lambda(1/2+it) = 0 implies riemannZeta(1/2+it) = 0, via Mathlib
  riemannZeta_def_of_ne_zero.
- `exists_zeta_zero_of_signs`: t1 < t2 with opposite signs of Re Lambda gives some t in Ioo t1 t2 with
  riemannZeta(1/2+ti) = 0.  It uses XiLineZeros.gLine_continuous, lambda_eq_gLine and
  ZetaReflection.exists_zero_of_sign_change.
- `RS5.Demo.zeta_zero_10000`: there is a t in Ioo 10000 (20001/2) with riemannZeta(1/2+ti) = 0.  The inputs
  are RS4.Demo.sign_B and sign_A.

## 3. BAND certificate
- Checker (RS5_Eval):
  * `Sample` = (tn, tq, E, RS4 cert), with cfg64 tn tq.
  * `sampleOK` = check5 && MarginOK && (PosOK or NegOK on the claimed side).
  * `bandOK` also checks that the heights are strictly increasing.
  * `chgBy` counts sign changes; `lastOf` gives the last sample.
  * The loops use raw List.rec.
- Soundness (RS5_Band):
  * `band_sound`: K = chgBy gives a strictly increasing list of length K of ordinates in (t_0, t_k) with
    Lambda = 0 and riemannZeta = 0.
  * `band_sound_finset`: a Finset of card K.
  * `BandZeros` has glue / mono / zeta / finset / hLine forms.  The hLine form is VERBATIM the on-line
    antecedent of TuringBand.BandStatement.
- Demos (all GREEN, cross-checked against untrusted mpmath nzeros):
  | band            | file(s)                        | samples | K certified | mpmath N(T1)-N(T0) | sharp |
  |-----------------|--------------------------------|---------|-------------|--------------------|-------|
  | [510, 520]      | RS5_Band_T510 (1 chunk)        | 8       | 7           | 7                  | yes   |
  | [1000, 10000]   | RS5_Band_T1000 (32 chunks)     | 9494    | 9493        | 9493               | yes   |
  | [10000, 11000]  | RS5_Band_T10000 (4 chunks)     | 1183    | 1182        | 1182               | yes   |
  | [1000, 11000]   | RS5_Band_Joint (glue)          | -       | 10675       | 11324-649 = 10675  | yes   |
  Headlines:
  * `RS5.BandJoint.zeta_zeros`: 10675 distinct zeros of riemannZeta on Re s = 1/2 with 1000 < Im s < 11000.
  * Also `zeta_zeros_finset` and `hLine`.
  * Every sample in both bands passed; none was dropped.  The smallest |Z| at a sample was 0.0038, in [1000, 10000].
- Negative controls in RS5_Demo, each rejected by decide +kernel:
  * `bad_flip`: sign-flipped box.
  * `bad_margin`: E halved.
  * `bad_order`: samples swapped.
  * `bad_floor`: an honest exact-box certificate at t = 508.
- Measurements:
  * Chunks hold about 296 samples.  Kernel time is about 9.4 s per chunk at t ~ 1e4 (~32 ms/sample,
    N = 39-41).  Chunks are faster at lower t.
  * Peak RSS is 7.2-7.4 GB per chunk file (Mathlib import ~5.6 GB + ~5.7 MB/sample), so every file is < 10 GB.
    A single 1183-sample file hit 12.5 GB, which is why the bands are chunked.
  * Wall times: [1000,10000] needed 8 lake batches of 4 chunks at ~20 s each once imports were warm.
    [10000,11000] needed 4 chunks in one batch in ~42 s.
  * The emitter took ~6.5 min for 9494 samples, mostly the Lean `#reduce` of the exact boxes.
  * Box half-width is <= 0.0018 at t ~ 1e4 and <= 0.011 at t ~ 1e3.  It is dominated by the RSTheta 1/t phase ball.

## 4. What remains for "ALL zeros in the band are on the line" (NOT on this branch)
The band certificate gives a LOWER count: >= K zeros on the line.  The matching UPPER count is still needed:
the number of zeros of riemannZeta in {0 < Re s < 1, T0 < Im s < T1}, with multiplicity, is <= K.
Precisely, for a band [T0, T1] certified here with K changes, the obligation is the second antecedent of
TuringBand.BandStatement sigma0 sigma1 T0 T1 K ...:
- edge non-vanishing of riemannZeta on the rectangle boundary;
- the zero-confinement / Blaschke disc data;
- enclosures of the five RvM edge argument-changes that pin the box count to K.
This is the argument-principle / Turing count.  It lives on cl/arb3-h1000 (#613: ArgChange*, H1000*,
AllZerosKernel_h1000) and cl/arb4 (#620), not here.  Those branches were not imported.  With them,
`BandZeros.hLine` plugs directly into BandStatement.  The docstring of RS5_Band.lean records the same
statement.

## 5. Guard
- RS5_AxiomGuard.lean has 213 `#print axioms`.  They cover every theorem in RS5_Eval/Sound/Z/Band/Demo,
  every band headline, and each chunk's ok / count / zeros.
- Results: 132 print [propext, Classical.choice, Quot.sound], 44 print [propext], and 37 use no axioms.
  All of these are subsets of the standard three.
- The full guard build is green: 8816 jobs, guard step peak RSS 5.7 GB.

## Not done / follow-ups
- CI wiring of RS5_AxiomGuard.  .github is out of scope.
- Extend the bands toward 1e5.  Cost is linear: ~32 ms/sample at t ~ 1e4, rising with N ~ sqrt(t/2pi).
