# bg_arm_balancing — m=2 arm-balancing strictly increases Z (route-b, kernel-gated)

The two-hub length-2-arm caterpillar `T(a, b)` (two adjacent hubs carrying `a` and `b` pendant length-2 arms)
has the exact closed-form monomer-dimer partition function

```
Z(T(a,b)) = (3/2)^(a+b-2) * ((4a+3)(4b+3) + 9) / (4 (a+1)(b+1))
```

(`telperion.transfer_caterpillar.two_hub_Z`, derived from the `(U,M)` cavity, verified `== matching_free_energy.rho`
on the `0..8` grid). At fixed spine-arm-total `s = a+b` the `(3/2)^(s-2)/4` prefactor is common, so the
split-dependent factor `g(a,b) = ((4a+3)(4b+3)+9)/((a+1)(b+1))` obeys the **factored identity**

```
g(a-1, b+1) - g(a, b) = 2 (a-b-1)(2a+2b-1) / (a (a+1)(b+1)(b+2))  >  0   for integers a >= b+2
```

(every factor positive; `= 0` at the balanced tie `a = b+1`). So moving one arm from the fuller hub to the
emptier one **strictly increases** `Z` — the rigorous, all-`(a,b)` m=2 arm-balancing lemma.

## Why it matters

This is the one monotone local move **salvaged** after the reassessed proof step "reduce every tree to the
length-2-arm caterpillar family by local `Z`-monotone moves" was **refuted at n=16**: the balanced symmetric
3-spider `S(3;2,2,2)` is a strict single-edge-swap local maximum (`Z = 847/32`) that sits below the family
maximum `Z(T(3,4)) = 35721/1280` (see `docs/BG_PIECE3_OBSTRUCTION_MAP.md`). The corrected architecture is
*local moves on the caterpillar complement + a direct comparison against the exceptional symmetric spiders*;
`m=2` arm-balancing is the verified backbone of the local-move half.

## What is gated

`generate.py` emits `lean/BGArmBalancing.lean`: the balancing direction `Z(T(a,b)) < Z(T(a-1,b+1))` as finite
`norm_num` anchor atoms over a spread of `(a,b)` with `a >= b+2` (exact closed-form rationals). The rationals
**are** the graph invariants `Z(T(...))` (closed form `== rho`, checked in `tests/test_transfer_caterpillar.py`);
the all-`(a,b)` generality is the Python-verified `arm_balance_delta_g` lemma, whose Lean upgrade obligation
(`field_simp; ring` for the identity, factor-sign positivity for `> 0`) is recorded in its docstring.

```
python examples/bg_arm_balancing/generate.py           # write the Lean
python examples/bg_arm_balancing/generate.py --check    # drift check (CI)
```

CI job `bg-arm-balancing-compiles` (`.github/workflows/telperion-lean-e2e.yml`) regenerates + `lake build`s it.
**NOT** a proof of Brualdi–Goldwasser — the complement reduction and the exceptional-spider comparison remain.
`conjecture1_proved = False`.
