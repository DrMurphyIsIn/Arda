# bg_broom_optimum — star-of-cherry-brooms c=5 optimum (route-b retarget, kernel-gated)

After the length-2-arm caterpillar was refuted as the maximizer of the Laplacian ratio
`π = per(L)/∏deg` (see `docs/BG_PIECE3_OBSTRUCTION_MAP.md`), the retarget is the **star-of-cherry-brooms**
`S(k,c)`: one central hub joined to `k` branch-hubs, each of degree `c+1` carrying `c` length-2 cherries. Its
asymptotic per-vertex free-energy density is

```
F(c) = log(total(c)) / (2c+1),   total(c) = (3/2)^(c-1)(4c+3)/(2(c+1)),   total(5) = 621/64
```

The **star** core (branch-hub degree `c+1`) beats Pant 2026's **path** core (`c+2`): `F(5) = 0.206586 >
0.205098` (caterpillar sup). Among all rooted branches up to 16 vertices, `B(5)` is the unique density
maximizer.

## What is gated

The **discrete optimum `c* = 5`**: `F(5) > F(c)` for `c ∈ {2,3,4,6,7,8}`. The `(2c+1)`-th roots in
`rate(c) = total(c)^(1/(2c+1))` are cleared by **cross-exponentiation**:

```
rate(5) > rate(c)   ⟺   total(5)^(2c+1) > total(c)^11
```

both sides exact rationals, so each atom is a `norm_num`-checkable rational inequality (emitted by
`telperion.spider_broom.BroomOptimumCertificate`). The `total(c)` values are the exact branch weights
(`spider_Z` closed form `== matching_free_energy.rho`, checked in `tests/test_spider_broom.py`).

```
python examples/bg_broom_optimum/generate.py           # write the Lean
python examples/bg_broom_optimum/generate.py --check    # drift check (CI)
```

CI job `bg-broom-optimum-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.

This certifies only the `c`-argmax among brooms. The family-vs-caterpillar dominance is the exact
`spider_Z`/`rho` computation; the **global maximizer over all trees remains OPEN** — this is asymptotic
dominance of one explicit family, a stronger counterexample to Wu–Dong–Lai than Pant's, **not** a proof of
Brualdi–Goldwasser. `conjecture1_proved = False`.
