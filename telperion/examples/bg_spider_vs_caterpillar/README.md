# bg_spider_vs_caterpillar — the spider beats the caterpillar (BG, kernel-gated)

**Part (ii) of the broom-dominance reduction.** The exchange analysis (`BG_ARITHMETIC_VS_COMBINATORIAL`) showed
that under rich single-edge moves the only spurious local maxima of `rho` are length-2-arm caterpillars (Pant's
family), each beaten by the broom/spider. So Obligation A reduces to: *(i)* every rich-exchange local max is the
broom or a length-2 caterpillar, *and* *(ii)* the spider beats every caterpillar. This gate discharges (ii)
asymptotically.

## What is gated

For the spider free energy `F* = log(621/64)/11` and the uniform-caterpillar free energy
`F(a) = log(lam(a))/(2a+1)` (`lam(a)` = transfer-matrix Perron eigenvalue, a quadratic surd
`lam = (t + sqrt(D))/2`), cross-multiplying clears the logs:

```
F* > F(a)   ⟺   (621/64)^(2a+1) > lam(a)^11 = A + B·sqrt(D).
```

`lam^11 = A + B·sqrt(D)` with exact rational `A, B` (binomial expansion of the surd). With `L = (621/64)^(2a+1)`,
the three **rational** facts

```
L > A,     B > 0,     (L − A)² > B²·D
```

are together *exactly equivalent* to `L > A + B·sqrt(D)` (for `D > 0`) — so the surd comparison is discharged by
`norm_num` atoms. `SpiderBeatsCaterpillarCertificate` emits these for `a = 1..12` (36 atoms), covering the
caterpillar arm-optimum `a = 7`.

**The tail (`a ≥ 13`) is gated too, uniformly** (3 more atoms), so *all* caterpillars are covered with no gap:
`lam(a) < (4/3)(3/2)^a` for **every** `a` — this reduces to the identity `(2a+3)² + 9 < (2a+5)²`, i.e. `9 < 8a+16`
— so `lam(a)^11 < (4/3)^11 (3/2)^{11a}`; with the **GROWTH** atom `(3/2)^11 < (621/64)²` and the **BASE** atom
`(4/3)^11 (3/2)^143 < (621/64)^27` (boundary `a = 13`), `lam(a)^11 < (621/64)^(2a+1)` for every `a ≥ 13`. (The
limit `lam(a)/(3/2)^a → 4/3` makes the `4/3` bound tight and universal.)

```
python examples/bg_spider_vs_caterpillar/generate.py [--check]
```
CI job `bg-spider-vs-caterpillar-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake
build`s it.

## Role

This is the arithmetic heart of part (ii): the spider strictly beats *every* caterpillar (`F* − F(7) ≈ +0.00149`
at the sup, huge margin after clearing) by an exact rational-plus-surd comparison — the arithmetic closing the
integrality-gap diagnosis called for, now complete for all arm-counts. The residual for a complete (A) is part
(i) (the exchange-reachability statement, verified `n ≤ 13`). `conjecture1_proved = False`.
