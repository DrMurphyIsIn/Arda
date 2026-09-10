<!-- Campaign spec, 2026-09-10. Opens the Jensen-Polya / GORZ hyperbolicity emitter — the axis the
six-route closure assessment (RH_CLOSURE_ROUTES_ASSESSMENT_2026-09-10.md) ranked highest-value and
the ONLY route with genuine partial-uniform traction (reduces-to-named-subproblem). Recon findings
folded in. conjecture1_proved = False; this campaign does NOT approach RH — see the ceiling. -->

# Jensen–Pólya hyperbolicity emitter — campaign spec

## Why this axis

The closure-routes assessment ranked Jensen–Pólya/GORZ **highest-value** and the *only* route with
genuine partial-uniform traction: GORZ (2019) proved hyperbolicity for all `n` at each fixed `d`
(ineffective `n₀(d)`); GORTTW (2022) made it effective for `d ≤ 9×10²⁴`. Its rungs are **decidable
real-rootedness certificates**, and the engine beneath them (Hermite–Bezoutian / discriminant PSD)
is reusable far beyond RH (real stability, Lee–Yang, the BG cone). This is the one ladder where the
mathematics has genuinely climbed and where a certificate engine's finite rungs sit under real
theorems.

**What the emitter is (and is NOT).** It certifies *specific concrete* `(d,n)` Jensen polynomials
real-rooted. It does **not** reproduce the GORTTW `d ≤ 9×10²⁴` range — that is a single analytic
theorem (low-lying zeros of `Ξ⁽ⁿ⁾`), not an enumeration. Its honest value: (1) the reusable
real-rootedness certificate shape; (2) a **refutation instrument** — a certified *non*-hyperbolic
`J^{d,n}` refutes RH outright (cf. `li_neg_refutes_rh`); (3) the conditional structural theorem
(rungs discharged *given* an imported `n₀(d)`, flagged as an undischarged analytic input).

## Recon findings (2026-09-10) that shape the plan

1. **The `d=3` case is ELEMENTARY — no Hermite–Bezoutian engine needed.** A real cubic is real-rooted
   iff its **discriminant `Δ ≥ 0`** (`Δ>0` ⇒ three distinct real; `Δ=0` ⇒ repeated real; `Δ<0` ⇒ one
   real + conjugate pair). That is a single polynomial inequality in the coefficients — exactly the
   `nlinarith`-shaped certificate the merged deg-2 route (`hyperbolic_deg2_of_discrim_nonneg`) uses.
   So `d=3` extends the existing pattern directly. The Hermite–Bezoutian PSD engine is required only
   for **`d ≥ 4`**, where `Δ ≥ 0` is necessary but not sufficient (need the full Hermite form PSD).
2. **The deg-2 seed is on a FOSSIL branch.** `origin/merge/jensen-to-main` is **595 commits behind
   main** (its diff vs current main is −121,019 lines / 814 files). It **cannot be merged** — a PR
   would revert the session's entire body of work.
   **★ CORRECTION (2026-09-10, verified): the seed is ALREADY ON `origin/main` — no re-port needed.**
   `telperion/examples/jensen_hyperbolicity/` is on main (landed via `dddcf22e`
   "FIRST kernel-verified J^{2,0} hyperbolicity cert for zeta — MILESTONE"), byte-identical to the
   fossil: `JensenBridge.lean` (`hyperbolic_deg2_of_discrim_nonneg` + `#print axioms`,
   `[propext, Classical.choice, Quot.sound]`), `JensenHyperbolicity.lean`
   (`jensen_box_hyperbolic_deg2_{0,1,2}`, no `sorry`), on the **v4.32.0 main toolchain** (not a
   separate island), CI-wired as `jensen-hyperbolicity-compiles` in `telperion-lean-e2e.yml`
   (`generate.py --grid --check` + `lake build`). An honest rigor-fix `aa97f10f` already reverted an
   unsound `α(5)` path back to the sound `n=0,1,2` grid. So **Brick 0 is DONE**; the campaign starts
   at Brick 1. (The re-port instructions below are retained struck-through for provenance only.)
3. **Mathlib gap (as of 2026-09-10):** only `LinearAlgebra/Matrix/Charpoly/Disc.lean` (a matrix
   discriminant def). **No** Sturm-chain real-root-count theorem, **no** Hermite–Bezoutian
   PSD→all-roots-real bridge. So both the `d≥4` engine and any Sturm route are genuinely from-scratch.

## Bricks (dependency-ordered, each its own guard-verified session)

- **Brick 0 — re-port the deg-2 seed onto current main** — **✅ ALREADY DONE on main** (see the
  CORRECTION under Recon #2): `telperion/examples/jensen_hyperbolicity/` landed via `dddcf22e`,
  CI-wired, axiom-clean, no `sorry`. No action; the campaign starts at Brick 1.
- **Brick 1 — `d=3` via the cubic discriminant.** Bridge lemma `hyperbolic_deg3_of_discrim_nonneg`:
  for a real cubic with leading coeff `> 0`, `Δ ≥ 0 ⟹ roots.card = 3` (all real). Elementary,
  `nlinarith`-shaped, extends Brick 0. Emit `jensen_box_hyperbolic_deg3_{small n}` boxes from
  certified `γ(k)` enclosures. **Reachable near-term.**
- **Brick 2 — the Hermite–Bezoutian PSD → all-roots-real engine (`d = 4..8`).** The genuine new
  construction Mathlib lacks: `PSD(Hermite form of p) ⟺ all roots of p real`, degree-generic (or a
  per-degree `d=4,5,6,7,8` battery). This is the reusable engine and the campaign's hardest,
  fresh-context brick. Consumes the box-positivity/SOS/PSD substrate already in the repo (the BG cone
  engine) underneath, but the discriminant→real-roots bridge itself is new.
- **Brick 3 — the `γ(k)` Cauchy truncation-tail enclosure backend** (blocker (a) in
  `JENSEN_HYPERBOLICITY_STATUS.md`): rigorous rational enclosures of the `Ξ` Taylor coefficients
  `γ(m)` for `m ≥ 5` (needed for `n ≥ 3`), via the Cauchy estimate `|γ(k)| ≤ max_{|t|=R}|Ξ(t)|/R^{2k}`
  so the finite linear solve's dropped tail is bounded. Arb backend, mirrors `li_coeff.enclose_*`.
- **Brick 4 — the emitter + refutation atom.** `jensen_hyperbolic` (kind): given `(d,n)`, assemble
  `J^{d,n}` from Brick-3 enclosures, emit the real-rootedness certificate via Brick 1 (`d=3`) or
  Brick 2 (`d≥4`), plus `jensen_nonhyperbolic_refutes_rh` (a certified non-real-rooted `J^{d,n}`
  refutes RH through the Pólya/GORZ equivalence). Register in `certify.py` + `emitter_sensitivity.py`
  (certificate-sensitive: forge the discriminant/PSD witness → kernel rejects) + negctrl adapter +
  CI job + axiom guard.

## The ceiling (state at every step)

Even a perfect engine checks **finitely many** `(d,n)`. The uniform-in-`d` threshold `N(d)` — the
statement that `J^{d,n}` is hyperbolic for **all** `n` at **every** `d` — **is RH**. The emitter is a
finite-rung instrument like every other in this program; its distinction is a genuinely climbing
ladder above it and a reusable engine beneath it. It is a refutation-and-evidence instrument, never a
closer. `conjecture1_proved = False`.

## Attribution / honesty

Pólya (1927) for the Laguerre–Pólya equivalence; GORZ (PNAS 116, 2019 / arXiv:1902.07321) for the
fixed-`d`/all-large-`n` Hermite-limit theorem and `d≤8` all-`n`; GORTTW (Adv. Math. 397, 2022) for
`d ≤ 9×10²⁴`. These are the theorems ABOVE the ladder; the emitter cites, does not reprove them.
Any `n₀(d)` used to discharge a finite obligation enters as a documented, undischarged analytic
hypothesis — never as progress toward RH.
