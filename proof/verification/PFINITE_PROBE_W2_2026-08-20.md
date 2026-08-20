# P-finiteness probe for the W2 interpolation family (Ibrahim-Salvy route)

**Date:** 2026-08-20  **Script:** `proof/verification/pfinite_probe_w2.py` (self-verifying `run_all()`)
**Arithmetic:** exact `Fraction`/`sympy.Rational` throughout. `conjecture1_proved = False`.

## Setup

The open "R7 interpolation lemma" (see `g34_deep.py` (4), `interpolation_lemma.py`) asks whether
the domination ratio

```
r(q) = best_template(n) / pi_star(cfg(q)),   cfg(q) = (2, 1, 0, 0, (q, 5, 9)),   n = 181 + 11q
```

is unimodal. The Ibrahim-Salvy positivity-certificate machinery (SODA 2024 arXiv:2306.05930,
JSC arXiv:2412.08576) turns unimodality/comparison of **P-finite (holonomic)** sequences into a
finite polynomial-sign certificate. The sole obstruction named by the orchestrator: is
`best_template` P-finite? This probe answers for both objects
`a(q) := pi_star(cfg(q))` and `b(q) := best_template(181 + 11q)`.

## Correctness gate

Reproduced the known exact values (matches the prior numeric picture):

| q | r(q) exact | float |
|---|---|---|
| 1 | 1305780426/882980405 | 1.4788328468 |
| 23 | 9571711680/6513636493 | 1.4694881562 |
| 34 | 15879220884/10803507029 | 1.4698209425 |
| 80 | 4901480343/3333515500 | 1.4703637475 |
| inf | 488925720/332391353 | 1.4709339325 |

## Findings

### (A) a(q) is P-finite of order 1 -- PROVED symbolically

Reading the code's own formula, the term-ratio is an explicit rational function of q:

```
a(q+1)/a(q) = 621 (q+1)(88185461 q + 176596081) / [64 (q+2)(88185461 q + 88410620)]
```

so a(q) is a hypergeometric term. Verified against the code **exactly for q = 1..119** (zero
mismatches). This is a *proof* of P-finiteness, not a guess. Cross-checked independently by
blind holonomic guessing: an order-1 degree-2 recurrence gives a 1-dimensional nullspace that
**validates exactly on held-out terms q = 40..60**, while order-1 degree-1 admits no recurrence.
Equivalent recurrence: `64(q+2)(88185461q+88410620) a(q+1) - 621(q+1)(88185461q+176596081) a(q) = 0`.

### (B) b(q) is a max of finitely many order-1 P-finite families -- the sandwich

Instrumenting `best_template`'s argmax over q = 1..80:

- **q = 1..4**: a short transient (isolated argmax choices);
- **q = 5..22**: family A = `(c0=0, nleaf=0, K=q+18, loads=[5]*(q+9) + [4]*9)`;
- **q >= 23**: family D = `(c0=0, nleaf=0, K=q+16, loads=[6]*2 + [5]*(K-2))`.

Each family's value equals `best_template` **exactly** on its range (verified) and is order-1
P-finite with an explicit symbolic ratio:

```
family A:  b(q+1)/b(q) = 621 (q+18)(247 q + 4747) / [64 (q+19)(247 q + 4500)]
family D:  b(q+1)/b(q) = 621 (q+16)(117 q + 1985) / [64 (q+17)(117 q + 1868)]
```

The two families carry different total cherry budgets (hence different affine K(q) laws,
q+18 vs q+16, and different loads) but both are order-1 P-finite. So `b(q)` is the pointwise
max of finitely many P-finite sequences -- exactly the sandwich the Ibrahim-Salvy route needs.

### (C) Sign of the first difference of r -- settled exactly

On family D (q >= 23), `r(q+1)/r(q) - 1` has numerator

```
379085447 q^2 + 1927564431 q + 7857434164   (all coefficients positive)
```

so **r(q+1) > r(q) for every q >= 23**: r is strictly increasing on the entire tail. Exact
arithmetic on q = 1..59 confirms r decreases on q = 1..23 and increases on q >= 23.

**Honest correction to the prior picture.** The interior minimum is at **q = 23**
(r = 1.46948816), **not q = 34**. q = 34 (r = 1.46982094) merely lies on the rising tail where
the slowly increasing curve passes near the sampled "min". The minimum is a **family-crossover
kink** at exactly the argmax switch A -> D (q = 22 -> 23), not a smooth stationary point --
which is why the earlier float-sampled probe misplaced it.

### (D) Poincare / dominant-root structure

`a(q+1)/a(q) -> 621/64` and `b(q+1)/b(q) -> 621/64` (= rhoB^11), so both sequences have the
**single simple** dominant characteristic root 621/64; `r(q+1)/r(q) -> 1` (unique simple
dominant root 1). This is precisely the Ibrahim-Salvy hypothesis, with **no near-degeneracy at
the n = 11q resonance** (the risk the orchestrator flagged does not materialize here). r(q)
converges to the exact limit `r(inf) = 488925720/332391353 = 1.4709339325`, strictly from below.

This also resolves an earlier confusion recorded in memory (2026-08-18): the hand-analysis
"pi ~ F(1,5)^q = 20.25^q, template ~ rhoB^11q" that contradicted the code was simply wrong on
the numerator's growth. The true dominant growth is `(621/64)^q ~ 9.70^q` on **both** sides;
their ratio r(q) is bounded and converges, exactly as the code shows.

## Verdict

The W2 family is **on the Ibrahim-Salvy route**:

- a(q): **P-finite order 1, proved symbolically** (and independently validated by blind guessing).
- b(q): **max of finitely many order-1 P-finite families** (sandwich found; family D dominant
  for q >= 23, family A for q = 5..22).
- r first-difference sign: **settled exactly** by an all-positive-coefficient quadratic
  (decreasing then increasing; min at q = 23).
- Dominant root: **simple** (621/64 for a, b; 1 for the r-ratio) -- no resonance degeneracy.

## Honest caveats / what this probe does NOT do

- The families' **values** were matched to `best_template` exactly on the checked ranges
  (family A: q = 5..22; family D: q = 23..80) plus the closed-form value identity. The probe
  does **not** prove "family D is the argmax for **all** q >= 23" as an all-q theorem -- that is
  the same finite max-over-family domination obligation that `interpolation_lemma.py` already
  isolates (heavy-top cav->0 / light-top q=1 corners). What is new is that the probe supplies an
  **exact order-1 P-finite backbone** for each competing family, so that obligation is now a
  finite comparison of P-finite sequences -- exactly the shape Ibrahim-Salvy consumes.
- All certificates are exact-rational; no numeric fits are trusted. The interior-minimum
  relocation (q=23, not q=34) is itself a demonstration that the earlier numeric sampling was
  imprecise -- reported as a correction, not swept under.

`conjecture1_proved = False`.
