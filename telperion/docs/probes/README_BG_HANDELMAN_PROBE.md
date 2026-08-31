# Probe: one Handelman engine certifies both a BG discharge atom and RH's zero-free witness

Feasibility evidence for the 2026-08-31 shared-endgame reassessment (memory
`rh_bg_shared_endgame_2026-08-31`): the reduced BG upper bound (`bg_bulk_discharge`,
`φ_v ≤ F*` on the cavity-field box) and RH's ζ zero-free region are the SAME
box-positivity cone — Handelman / constrained-SOS / cone / worst_corner.

Run (offline, exact rationals, no Lean build):
```
python3 telperion/docs/probes/bg_discharge_handelman_probe.py
```

## What it shows (green)

- **BG `c=5` full-edge discharge atom** — `a_v R_v ≤ ∏(1+h_{u→v}h_{v→u})` on `h∈[0,1]²`.
  At `c=5`, `1+2c=11` so `rhoB^{1+2c}=rhoB^{11}=621/64` is **exactly rational** — the
  irrational 11th root cancels and the atom is rational box-positivity, with the tie
  arithmetic manifest (`a = 156/161`, `161 = 7·23`; `621 = 27·23`). Certified by an
  **explicit Handelman/Bernstein certificate** (degree 3, 16 nonneg product terms,
  min coeff 3380, exact reconstruction `P == Σ terms`).
- **RH zero-free witness** — `(1+x)^n ≥ 0` on `{1±x≥0}` — certified by the same
  `find_handelman_certificate` (the `emit_zero_free_cosine` shape).

## Honest scope

This is the **atom** (the free-field full-edge bound, which has slack and is
box-positive), not the open core. The open Brualdi–Goldwasser problem is the
**universal discharge rule `τ`** that makes `φ_v ≤ F*` tight for every local
configuration; naive rules are provably spoofed (the acyclicity/surface barrier).
The shared engine certifies the atoms; constructing `τ` is the remaining research.
`conjecture1_proved = False`.

## Connection to the reconciliation

This dovetails with `BG_23ADIC_RECONCILIATION_20260831.md`: the `156/161` and the
`621/64` here are the same `23`-adic tie the Φ¹¹↔broom reconciliation pins at
`R(5)=1` (`64·243·23 = 621·576`). Suggested next step: a `bg_bulk_discharge`
kernel gate that emits the `c=5` (and neighbouring `c`) full-edge atoms via
`handelman_family` + `emit_padic` for the `27·23` tie.
