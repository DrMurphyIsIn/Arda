# Research direction: multiplicativity as the discreteness-substitute

*2026-09-16. A genuine creative research angle on the **companion clause** (the sole
open wall after the archimedean localization). This is a SEARCH, not a claim:
`conjecture1_proved = False`. Success = new kernel-checkable structure, OR an honest
negative result that sharpens the map. A fake success is the only forbidden move.*

## The seed
The tame reality-forcing theorem (Kurasov–Sarnak → Olevskii–Ulanovskii →
Alon–Cohen–Vinzant) forces reality from **uniform discreteness**: a uniformly-discrete
ℕ-valued Fourier quasicrystal *is* the zero-counting measure of a Lee–Yang exponential
polynomial, whose zeros are real by construction. The load-bearing hypothesis is
uniform discreteness.

The zeta comb **provably fails** it (`primeLogSpectrum_dense`, kernel-verified): the
prime-log spectrum is dense. That failure is exactly where the wall sits.

The standard program responds by *dropping* discreteness and trying to classify the
wild broader FQ class — which is the Selberg-degree-conjecture-hard open problem.

**The fresh angle is a substitution, not a subtraction.** The zeta comb carries a
rigidity the tame class does not: its diffraction intensities are **completely
multiplicative through the primes** (the Euler product): `I(m log p) ∝ (log p)p^{−m/2}`.
Ask: *can multiplicativity play the structural role that uniform discreteness played in
the tame proof — a "multiplicative Lee–Yang" mechanism that forces reality without
discreteness?*

## Why it might be fresh (honest)
Neither thread is virgin — multiplicativity is the Selberg-class program; FQ-reality is
Dyson/ACV (2020–24). What is under-explored is the **joint** constraint:
*a Fourier quasicrystal whose intensities are completely multiplicative, WITHOUT uniform
discreteness.* The tame proof uses discreteness; the Selberg program uses multiplicativity
+ functional equation but not the diffraction/FQ rigidity. Putting the two rigidities on
the same object, and asking whether one can substitute for the other, is a genuinely
different attack surface than "classify the wild class."

## The honest obstructions it must confront (test these first)
1. **Selberg-degree collapse.** If "multiplicative + functional equation ⇒ real support"
   just re-encodes the Selberg degree conjecture, the angle dissolves into the known wall.
   *This is the most likely failure mode; test it early.*
2. **No stability analogue.** Lee–Yang gives real-rootedness via a stability/hyperbolicity
   property. It is unknown whether multiplicativity yields any analogous stability. If not,
   there is no "multiplicative Lee–Yang."
3. **Archimedean handled (good news).** The localization (`trivial_zero_is_archimedean`,
   `taylorCoeff_riemannXi_split`) already carves off the archimedean place, so the probe
   works on the pure companion — no Γ-factor confound.

## Formalizable probes (build these; keep what the kernel allows)
- **P1 — leakage dictionary (A2b).** `completely-multiplicative amplitude ⇒ structure of
  the composite Bragg amplitude`, as kernel lemmas on `DefectDictionary` / `BraggDefect`.
  What does multiplicativity force on the diffraction, exactly? (Substrate exists.)
- **P2 — multiplicative Lee–Yang micro-test.** Extend `twoFreq_realRooted_iff` /
  `ratFreq_realRooted_of_leeYangCircle`: does a *multiplicatively-constrained* two/three-
  frequency exponential sum have a real-rootedness criterion? A single positive or negative
  micro-result here is decisive signal.
- **P3 — Euler-factor rigidity.** `MM_euler_factor_section_offline` shows a single Euler
  factor's zeros sit at `Im = 1/2` (off-line for the section) — quantify what one factor's
  multiplicativity forces, and whether the *product* structure propagates it.

## The loop
Propose → check against ACV / Selberg-class literature (web-verified) → formalize the
smallest testable probe → run the kernel + negative controls → keep survivors, record
refutations honestly. Each probe is a brick; most will fail; the failures sharpen the map;
a survivor is the first sign of a real idea.

`conjecture1_proved = False.` We are looking for the idea, not asserting it.
