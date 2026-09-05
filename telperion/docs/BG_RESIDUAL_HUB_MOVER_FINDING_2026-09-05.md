# BG finding: 3 of the 5 residual general-env cells are GENUINE direct-step failures (2026-09-05)

Going deeper on the 5 residual cells of `certify_general_env_box` overturned a stated
conjecture in the codebase. `conjecture1_proved = False`.

> **CORRECTION 2026-09-05 (later, flint deep-push).** The "2 certifiable cells (0,5),(3,5)"
> claim below is WRONG — an artifact of a bounded scan (`deg_C ≤ ~61`). With `python-flint`
> pushing `deg_C` to the hundreds (exact `fmpq` sign), **ALL 5 cells fail the direct step** for
> a large-enough hub-mover: thresholds `deg_C =` 8 (2,5), 9 (1,5), 29 (1,4), 111 (3,5), 170
> (0,5), on the `A(1 arm)–B(0 arm)–C(load5,deg)` family. So none are "non-decreasing". Two
> further corrections: (i) `two_hub_phi` is NOT the exact step gain (my bilinear reading was
> off; the exact `pi` computation is ground truth); (ii) the anti-hubward step rescues the
> large-`deg_C` failures for (1,4),(1,5),(2,5),(3,5) but **NOT for (0,5)** — at `deg_C ≥ 170` the
> (0,5) config has NO pi-increasing Kelmans move. That stuck config is a **hub-backbone shape**
> (a path of 3 hubs with pendant arms), i.e. a merge NORMAL FORM, and it is dominated by another
> backbone (moving one arm `C→A` raises `pi`, though not via a Kelmans move). So it is a
> Kelmans-merge local max, not necessarily an obstruction to the DOMINATION goal (Hdom) — but it
> is decisively NOT evidence that (0,5) is direct-step-monotone. Net: the residual is best
> summarized as "the direct hubward merge is not universally non-decreasing for ANY of the 5
> cells; the anti-hubward move handles 4, and (0,5) has hub-form merge-local-maxima." The
> everything below the CORRECTION is the earlier, partially-superseded analysis; the 25-cell
> `R47R7KelmansGenEnvCert` theorem remains correct and unaffected (it excludes all 5).

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

## Resolution — the failures are NOT obstructions to the tree→hub reduction

Going one level deeper: at every one of these direct-step-failing configs, the tree is **not
hub-form**, so the tree→hub progress obligation `(R-prog)` demands *some* pi-increasing move.
There is one — and it is deterministic. Over **80** direct-failing in-scope configs across
(1,4),(1,5),(2,5) (exact arithmetic, `verify_antihub_rescue`):

    the ANTI-hubward step (merge A's subtree INTO B, `kelmans_step(B, A)`) strictly INCREASES
    pi in ALL 80 — zero exceptions.

(Consolidating the hub-mover `C` into `B` rescues only ~60%; the anti-hubward step is the
universal one.) So the finder rule

    "take the hubward step if it increases pi; otherwise take the anti-hubward step"

always makes progress. The hub-mover configs are move-SELECTION issues, not stuck states:
`(R-prog)` holds constructively, and the direct-step failures of (1,4),(1,5),(2,5) pose no
obstruction to `Hnorm`. The genuinely open remainder shrinks to the exact certificate for
(0,5),(3,5) — and the arm-mover monotonicity already in `R47R7KelmansGenEnvCert` (25 cells).

## Artifact

`proof/verification/residual_hub_mover_probe.py` — self-verifying (`run()` asserts the split
AND the 80/80 anti-hubward rescue), exact `Fraction` arithmetic, in-scope-restricted. A
standalone file (does not edit the parallel session's `kelmans_mixed_load.py`).

`proof/verification/residual_flint_probe.py` — the same split re-verified at **4.3× scale**
with `python-flint` `fmpq` (~20× faster; `pi_flint` validated against `pi_loaded`): **8814
in-scope configs/cell**, `deg_C` up to 60, in ~34 s. Result: (0,5),(3,5) **zero decreases**
across 8814 configs each; (1,4)/(1,5)/(2,5) fail (58/98/100 decreases); **anti-hubward rescues
all 256** direct failures. This is decisive numerical evidence for the split.

## Remaining open surface (now sharp)

- (1,4),(1,5),(2,5): NOT obstructions — the anti-hubward step handles them (proven-by-scan,
  256/256). The finder rule "hubward if it increases, else anti-hubward" suffices.
- (0,5),(3,5): the ONLY genuinely-open piece — a formal certificate that the direct step is
  non-decreasing for ALL in-scope configs. Mechanism identified: the failing corner
  `(σ_Q hi, σ_S=0)` is only MILDLY negative (const −648 / −18225 vs −26811 / −80514 for the
  failure cells), and the box over-counts `σ_Q` (it uses `(da−1)·z1`, but an arm contributes
  `z1·ρ_arm` with `ρ_arm < 1`); the tight `σ_Q` keeps the mild corner `≥ 0`. Exact-arithmetic
  check confirms the direct gain is `≥ 0` even in the `σ_S → 0` limit for every tested config.
  The certificate reduces to bounding `σ_Q ≤ (da−1)·z1·ρ_arm` and showing `Φ ≥ 0` there.
