# BG finding: 3 of the 5 residual general-env cells are GENUINE direct-step failures (2026-09-05)

Going deeper on the 5 residual cells of `certify_general_env_box` overturned a stated
conjecture in the codebase. `conjecture1_proved = False`.

## Context

`certify_general_env_box` (`kelmans_mixed_load.py`) box-certifies the adjacent hubward Kelmans
step as `pi`-non-decreasing for 25 of 30 load cells (ported to the kernel in
`R47R7KelmansGenEnvCert.lean`, all N/all m). The 5 residual `cb`-heavy cells
`{(0,5),(1,4),(1,5),(2,5),(3,5)}` are not box-certifiable. `three_hub_residual_probe` tested
them on 3-hub backbones, found 0 decreases, and conjectured the failure is
**"a CERTIFICATE artifact, not a real failure."**

## The finding — that conjecture is FALSE for 3 of the 5 cells

The probe only tested `B` with `≥ 1` arms. The box's failing corner is `σ_S → 0`, reached
when `B`'s **sole mover is a large de-loaded hub** `C` (`z_C = 3/(3·deg_C+4·load_C) → 0`), not
an arm. `two_hub_phi`'s bilinear identity `Φ = c1 + c2σ_Q + c3σ_S + c4σ_Qσ_S` is exact for
*arm* movers; a *hub* mover reaches the `σ_S≈0` regime the probe never sampled.

Probing that corner with **exact `Fraction` arithmetic**, restricted to the theorem's own
hypothesis `z_x ≤ 3/23` for every environment neighbour (`residual_hub_mover_probe.py`,
2052 in-scope configs/cell):

| cell | in-scope decreases | verdict |
|---|---|---|
| (0,5) | 0 | no decrease found — plausibly certifiable |
| (1,4) | 4 | **GENUINE decrease** |
| (1,5) | 42 | **GENUINE decrease** |
| (2,5) | 44 | **GENUINE decrease** |
| (3,5) | 0 | no decrease found — plausibly certifiable |

Explicit witness, cell (1,5), exact: `A(load1,1 arm) — B(load5, 0 arms) — C(load5, deg 9)`,
`z_C = 3/47 ≤ 3/23`, hubward `B→A` (`deg_B 2→1`):
`gain = −44233873362873340080631066197 / 2066035336255469780992 < 0`.

## Consequence

The 5 residual cells are **not a uniform certification gap**:

- **(1,4),(1,5),(2,5)** — the *direct* hubward step genuinely DECREASES `pi` at in-scope
  hub-mover configs. These are true K/H-stuck configs; the direct merge is the wrong move
  (the assisted merge / a borrow is required, as for de-loaded donors). No "sharp follow-up"
  certifies the direct step here — it is false.
- **(0,5),(3,5)** — no decrease found over the scanned in-scope region; these remain the
  genuine (still unproven) certifiable candidates.

The 25-cell `certify_general_env_box` / `R47R7KelmansGenEnvCert` theorem is **unaffected** — it
already excludes all 5. What changes is the *characterization* of the residual: the earlier
"certificate artifact" framing is refuted for the majority of it.

## Artifact

`proof/verification/residual_hub_mover_probe.py` — self-verifying (`run()` asserts the split),
exact arithmetic, in-scope-restricted. A standalone file (does not edit the parallel session's
`kelmans_mixed_load.py`). The correct next move for (1,4),(1,5),(2,5) is a general-environment
*assisted*-merge treatment, not direct-step certification; (0,5),(3,5) await the exact
hub-mover certificate.
