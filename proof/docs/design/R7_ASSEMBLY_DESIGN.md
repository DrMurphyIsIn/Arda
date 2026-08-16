# The R7' assembly: final-theorem design (2026-08-15)

Support artifact for the campaign's last layer, following the rate port.  Companion to
`assembly_composition_check.py` (executable validation) and the campaign's own method:
one honest-conditional capstone whose hypotheses are named Props carrying certificates --
never axioms, never `sorry`.

## The headline input from the composition check

**FAMILY CAPTURE (exact, brute force):** the extended single-hub template family
(hub load c0 <= 6, balanced arms, <= 2 hub leaves) contains the TRUE maximizer of
per L/prod deg at EVERY n in [8, 17], verified by exhaustive enumeration in exact
rationals.  (The check also CAUGHT an overstated sketch step: 'template >= C1 rho^n' is
FALSE at upgrade residues -- the DELTA-corrected form is the right one.  Executable
composition checks earn their keep.)  The small-n spider/broom maximizers are family members.  Consequence: the
assembly's reduction target is right at every tested n, not only asymptotically; the
`n >= n0` hedge protects the PROOF layers (dichotomy threshold, schedule stabilization
at K >= 40), not the statement's truth.  Recommend the paper state this explicitly.

## The final statement (Lean skeleton)

```lean
/-- the canonical family maximum at n (the searched template, as a def over the
    finite family -- computable, no choice) -/
noncomputable def templateMax (n : ℕ) : ℝ := ...

/-- THE HONEST-CONDITIONAL R7' CAPSTONE.  Each hypothesis is a named Prop defined
    elsewhere with its certificate provenance in the docstring. -/
theorem R7'_of
    (hRate   : HypRatePort)            -- pi = Z*R, S <= 1, R <= 4/3, Z <= rhoB^n
    (hLedger : HypLedgerTelescope)     -- logPhi = -phi(root) - Σ slack, slack >= 0
    (hFloors : HypFloors)              -- the class floors (rational certificates)
    (hHub    : HypAmortizedHub)        -- ledger >= (47/2000) * #pure-hubs
    (hSweep  : HypDominationSweeps)    -- the exact finite dominations
    (hStar   : HypStarSymbolic)        -- star-of-hubs + two-hub tail certificates
    (hDeep   : HypDepth3Generic)       -- the depth >= 3 genericity sliver
    (hSeam   : HypClassificationSeam)  -- confined tree -> Balanced/Capped encoding
    {n : ℕ} (hn : n0 <= n) (T : Tree n) :
    pi T <= templateMax n := ...
```

Already-green inputs consumed WITHOUT hypotheses (they are theorems in R3Cert):
`phi_le_one`, the bridge (`pi_litHub'`, `amplitude_bridge_real'`, `pi_utree`),
`chain_to_normalForm` (the merge-layer capstone), `R47Shed` (the shedding lemmas),
`R47Legs` (the (L) classification layer).

## The composition proof sketch (each arrow = one already-designed piece)

```
pi T = Z * R                                        [hRate; R <= 4/3, or 6/5 at a cherry tip]
     = rhoB^n * exp(logPhi (parse T)) * R           [bridge, green]
logPhi = -phi(root) - ledger                        [hLedger]
CASE ledger > theta:  pi T < C1 * rhoB^n * e^{-DELTA} <= templateMax n   [theta INCLUDES
     the uniform template deficit DELTA = 0.015 -- NECESSARY: at upgrade residues the
     template max dips below C1*rhoB^n (n = 445: -0.39%), caught by the composition
     check; the A2 identity anchors DELTA's validity]
CASE ledger <= theta (the confined family):
     T's parse is a bounded-defect hub-arm state    [hFloors + hHub confinement counts]
     -> encode as Balanced/Capped hub-state          [hSeam]
     -> chain_to_normalForm: rewrites monotonically to an ordered-merge normal form
        [GREEN capstone]  ... normal forms with >= 2 hubs or defects are dominated
        [hSweep + hStar + hDeep]
     -> single-hub family; the schedule picks the canonical template
        [R47Shed GREEN + the winner table (exact rational, ported at assembly time
         per the no-decorative-certificates rule)]
     -> pi T <= templateMax n.
```

## Hypothesis inventory with provenance and closing paths

| Prop | artifact | rigor now | path to discharge |
|---|---|---|---|
| HypRatePort | rate_bound_fixed_n.py + STEP4C prior art | designs validated | IN PROGRESS (parallel session) |
| HypLedgerTelescope | slack_ledger + hinge | Lean-shaped (DeficitNonneg green) | 1 CI file |
| HypFloors | g1_floor_certificates | RATIONAL (no floats) | G1_KERNEL_LEAN_DESIGN, 1-2 files |
| HypAmortizedHub | amortized_hub + g1_endpoint | RATIONAL | same kernel, 1 file |
| HypMergeCapstone | R47StepMono | **GREEN** | done |
| HypSchedule | R47Shed + finite_table | lemmas GREEN; table exact-rational | port table at assembly |
| HypDominationSweeps | 442,800-case + star + depth-3 region sweeps | EXACT RATIONAL Python | policy: cite-as-artifact / Lean sampling; native_decide banned |
| HypStarSymbolic | 972 + tails (sympy all-nonneg) | symbolic witnesses | nlinarith/positivity, mechanical |
| HypDepth3Generic | g34_deep sampling | PROBE (the one sliver) | the honest open hypothesis |
| HypClassificationSeam | R47Legs direction | design | the L/B seam, 1-2 files |

Two hypotheses deserve emphasis in the paper's honesty section: `HypDepth3Generic` (the
only probe-rigor link) and the sweep policy.  Everything else is theorem-grade in Python
rationals or already Lean-green.

## Suggested assembly order

1. Land the rate port (`pi_le_rate`) -- in progress.
2. `R7Hyps.lean`: the Prop definitions with provenance docstrings (half a file).
3. `R7Assembly.lean`: the capstone `R7'_of` with the case split; consume the green
   theorems directly and the Props by hypothesis.  The proof is glue: the case split,
   the exact A2 comparison (`norm_num`), and the chain through `chain_to_normalForm`.
4. Then hypothesis-discharge campaigns in any order (each shrinks the signature).

conjecture1_proved = False -- and after `R7Assembly.lean` lands, the ledger line should
read: "Conjecture 1 holds conditionally on the named Props; unconditional pieces:
[the list]" -- the precise, defensible statement forty-two years of this problem deserve.
