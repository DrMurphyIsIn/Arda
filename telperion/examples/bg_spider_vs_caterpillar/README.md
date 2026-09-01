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
caterpillar arm-optimum `a = 7`. `F(a)` decreases past the sup toward `log(3/2)/2 ≈ 0.2027 < F* ≈ 0.2066`, so the
gated range plus the monotone tail covers **all** caterpillars.

```
python examples/bg_spider_vs_caterpillar/generate.py [--check]
```
CI job `bg-spider-vs-caterpillar-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake
build`s it.

## Role

This is the arithmetic heart of part (ii): the spider strictly beats the best caterpillar (`F* − F(7) ≈
+0.00149`, huge margin after clearing) by an exact rational-plus-surd comparison — the arithmetic closing the
integrality-gap diagnosis called for. The residual for a complete (A) is part (i) (the exchange-reachability
statement, verified `n ≤ 13`) plus the caterpillar arm-optimum `a = 7` (a transfer unimodality). `conjecture1_proved
= False`.
