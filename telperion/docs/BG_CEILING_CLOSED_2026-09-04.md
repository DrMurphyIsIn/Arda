# BG additive-subaction ceiling CLOSED — verified both trust halves (2026-09-04)

The obligation `IsSubaction ρwit` — open through the entire subaction effort, the cell
family this campaign generated enclosure atoms for — is now a **proven theorem**, and it
discharges the branch ceiling **unconditionally**. Verified independently with the AXLE-
inspired trust tooling (`verify`, `statement_match`, `cert_deps`).

## The milestone

`R3Cert.BGSCL` (`BGSCLSubactionDispatch.lean`, 2026-09-04):

```
theorem isSubaction_ρwit : IsSubaction ρwit := by
  intro cs; rcases cs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, rest⟩⟩⟩⟩
  · exact subaction_deg1                    -- degree 1
  · exact subaction_deg2 c1                 -- degree 2
  · exact subaction_deg3 c1 c2              -- degree 3
  · exact subaction_deg4 c1 c2 c3           -- degree 4
  · exact tail_wrapper _ (…)                -- degree ≥ 5 (tail)

theorem bg_ceiling : ∀ b, bell b ≤ 0 := ceiling_of_witness isSubaction_ρwit
```

The full d=1/2/3/4 child-degree-profile cell family (`subaction_deg4_222 … _HHH … _L23`, the
mid cells, the tail decouple) is assembled by degree-dispatch into `isSubaction_ρwit`, which
feeds the already-nonneg-discharged `ceiling_of_witness` to give `bg_ceiling`.

## Verification — both trust halves (this was NOT in the earlier 16-module axiom audit)

`BGSCLSubactionDispatch` is a fresh file; the 2026-09-04 crosscheck predated it. Re-verified:

- **Negative half (axiom audit, `verify_lean` + `#print axioms`):** `bg_ceiling` and
  `isSubaction_ρwit` are both **axiom-clean** — `[propext, Classical.choice, Quot.sound]`,
  **no `sorryAx`**, 0 compile errors. Genuinely proven, no hidden gap.
- **Positive half (statement audit, `statement_match`):** `bg_ceiling` **matches**
  `∀ b, bell b ≤ 0` (the *unconditional* ceiling — no hypothesis remaining) and
  `isSubaction_ρwit` **matches** `IsSubaction ρwit`. Not weakened, not vacuous.

So the additive-subaction branch ceiling `∀ b, bell b ≤ 0` is **closed, unconditionally,
sorry-free, and stating exactly what it should.**

## Structure (`cert_deps`)

`isSubaction_ρwit` has **167 transitive dependencies**, `bg_ceiling` **168** — the whole
additive chain. `impact(subaction_deg4) = 3` (changing a degree-4 cell re-verifies deg4 →
isSubaction_ρwit → bg_ceiling). 77 of 246 corpus theorems are outside `bg_ceiling`'s cone —
the *other tracks* (the gstep/multiplicative-cap bridge, `ceil`/`hub` scaffolding), not dead
code: the additive proof legitimately uses 168, the rest serve the sibling routes.

## Tooling bug found + fixed by this analysis

The dep analysis initially reported `isSubaction_ρwit` with **0 deps** — a real gap:
`bundle.parse_theorems` and `cert_deps.extract_deps` used an ASCII-only identifier class
`[A-Za-z0-9_'.]`, so the Greek `ρ` in `ρwit`/`isSubaction_ρwit` truncated the name and
dropped every ρ-named theorem from the graph. Fixed both to a Unicode-aware `[\w'.]` boundary
(`\w` matches Unicode word chars in Py3). After the fix, the full 167/168-dep chain traces
correctly. (Consistent with the campaign pattern: applying the tools to the real corpus
surfaces — and fixes — the tools' own bugs.)

## Honest scope

`conjecture1_proved = False` still stands. `bg_ceiling : ∀ b, bell b ≤ 0` is the **additive
branch-model** ceiling — a genuine, now-verified, load-bearing PIECE — NOT the full classical
Brualdi–Goldwasser conjecture, which additionally needs the H2 bridge (Branch model →
`per(L)/∏deg`) and the R47 `Hnorm`/`Hdom` extremality for the fixed-N capstone (both audited
elsewhere as honest conditionals). What is closed and verified: the additive subaction
reframing delivers `bell b ≤ 0` for all branches, unconditionally, sorry-free.
