# BG statement-identity: `Aobj` IS classical `per(L)/∏deg` (2026-09-05)

The honest-spine report flagged an open caveat: is the capstone's objective
`Aobj t := Ztot (dtRealize t)` the **classical** Brualdi–Goldwasser objective
`per(L)/∏deg`, or the rooted-branch `Φ¹¹` variant (`81/8 ≠ 621/64` at the tie, per a
2026-08-29 note)? This resolves it — **kernel-verified: it is classical.**
`conjecture1_proved = False` (this pins the STATEMENT, not the proof).

## Kernel-verified identity chain (via `#print axioms` on the built env)

- **`R3Cert.Step3.pi_utree` — CLEAN** (`{Classical.choice, Quot.sound, propext}`, no
  `sorryAx`). Its statement, for EVERY rooted tree `t`:

      (lapl (aGraph (realize (dtRealize t)))).permanent
        / (∏ v, (aGraph (realize (dtRealize t))).degree v)   =   Aobj t

  i.e. **`Aobj` IS the Laplacian permanent ratio `per(L)/∏deg`** — an unconditional
  theorem. Proof route: `pi_eq_msum` (permanent = matching sum on acyclic graphs,
  Matching.lean's H1 `permanent_is_matching_sum_holds`) + `Ztot_eq_msum` (the cavity
  recursion computes that matching sum) + `rfl`.
- **`R3Cert.Step3.piRatio_eq_of_transport` — CLEAN**: `per(L)/∏deg` is a graph-transport
  invariant.
- **`R3Cert.Step3.Aobj_root_invariant` — CLEAN**: two rooted trees with transport-related
  realized address graphs have equal `Aobj` — CONDITIONAL on the transport `Equiv` as an
  explicit hypothesis (the honest remaining seam: a `SimpleGraph.Iso` construction, never
  stubbed to `True`).
- Tie value: `tie_anchor : (3/2)^5 + 5·(1/12)·(3/2)^4 = 621/64` (norm_num) — the CLASSICAL
  cherry-bundle tie `F_2(6) = 621/64`. `81/8` (the old Φ¹¹ tie) appears NOWHERE in the
  corpus; `621/64` appears in 40+ files including the capstone.

## Consequence for the capstone

`conjecture1_of_layers_fixedN` proves `∀ t, Aobj t ≤ Aobj (tie (usize t))`. Rewriting
both sides by `pi_utree`, that conclusion IS

    ∀ t,  per(L(t))/∏deg  ≤  per(L(tie))/∏deg,

the classical Brualdi–Goldwasser tree-extremality statement. So the assembly is not
about a rooted-branch surrogate — it targets the real conjecture. **The 2026-08-29
"Φ¹¹ ≠ classical BG" concern is SUPERSEDED**: the formalization moved to the classical
objective and PROVED the bridge (`pi_utree`).

## Honest residuals (precise)

1. `Aobj_root_invariant` is conditional on the address-graph transport iso existing — the
   remaining seam for treating `Aobj` as a fully root-free unrooted invariant. `pi_utree`
   itself is unconditional for the rooted realization, so the capstone's classical reading
   already holds per-realization; root-independence of the VALUE is the refinement still
   gated on that iso.
2. `DEC.lean` notes its own file does not do the matching/permanent bridge — that is LOCAL
   scoping; the bridge IS formalized elsewhere (`pi_utree` + `Matching.permanent_is_matching_sum_holds`).

## Net

The BG lane may state the capstone as CLASSICAL Brualdi–Goldwasser without mislabeling:
`Aobj = per(L)/∏deg` is a kernel-clean theorem (`pi_utree`). The only remaining content
is the two conditional hypotheses `Hnorm` + `Hdom` (see the honest-spine report) and the
minor root-invariance transport seam.

Reproduce: the `#print axioms` chain in `telperion/scratch/bg_honest_audit.py`-style calls
against `proof/formalization` (decls: `R3Cert.Step3.pi_utree`, `…piRatio_eq_of_transport`,
`…Aobj_root_invariant`). conjecture1_proved = False.
