# Audit testimony: AND_ladder_h1000_kernel (anduril), blind auditor A2, 2026-09-23

- pass: **true**
- axioms_clean: **true** (`[propext, Classical.choice, Quot.sound]`)
- statement_byte_identical: **true** (canonical `V.statement_matches` gate)
- conjecture1_proved = **False**. This is a finite verification up to height 1000. It says nothing about the Riemann Hypothesis.

## 1. My read of the statement (done before I opened the artifact)

`telperion/missions/anduril/lean/Statements/AND_ladder_h1000_kernel.lean` says:
`∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2`.

It uses Mathlib's `riemannZeta` and quantifies over all of ℂ, not only the critical strip. Requiring `Im > 0` rules out the trivial zeros and the removable value at s = 1. So the claim is exactly "every zeta zero with 0 < Im ρ ≤ 1000 lies on the critical line." That is a faithful finite statement.

## 2. Canonical gate

- `R.load_campaign(Path('telperion/missions/anduril'))` gives node `AND_ladder_h1000_kernel`.
- `V.statement_matches(AllZerosKernel_h1000.lean, V._normalized_statement(node, root))` returns **True**.
- `V.artifact_incompleteness_markers(artifact)` returns `[]`.
- I built the import closure myself across all three source roots (zeta_reflection 147, zeta_zero_localization 41, zero_free_bridge 66; 254 local modules in total). Every import resolved and none was ambiguous. The marker scan returned `[]` for every module.

## 3. Kernel checks

- `leanlock.sh lake build --no-build` reported "All targets up-to-date (9042 jobs)". That includes `AxiomGuardAllZerosKernel_h1000` and its 6 shards.
- My probe ran `#print axioms` on seven declarations and every one returned only the standard three axioms: the capstone, `_of_encl`, `HeightFloor.height_floor`, `seg_lineHyp`, `henc`, `hslab1` and `hpin`.
- A pure-Mathlib `example` restating the goal with `_root_.riemannZeta`, `Complex.im` and `Complex.re` is proved by the capstone.
- The probe file has been deleted.

## 4. Trust boundary

- A grep of the closure for `axiom`, `opaque`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `skipKernelTC`, `sorryAx` and `admit` found hits only in comments or docstrings, plus section `variable`s.
- The capstone has no binders. Its proof is `_of_encl E hpin henc hslab0 hslab1`, and every argument is a proved theorem in the artifact:
  - `hpin` is closed by `norm_num`.
  - `henc` comes from `enclHyp_of_K6`, built from `segK_side_i` and the proved `H1000Edge_*.hAH` terms.
  - `hslab0` and `hslab1` come from the `H1000Slab_*.slabClear` theorems and `band24_top_slabClear`.
  - The band-0 lower slab is `slab0_band0`.
  - `hγ` is `HeightFloor.height_floor 1000`.
  - `hLine` is `seg_lineHyp`.
- The guard's 4 negative controls are compiled `decide +kernel` proofs of `= false`, so the kernel rejects them.
- I added my own controls. The kernel rejected octant label 2 on T41 sub-box 0, and it rejected slab cell U41/0 with its radius 10 times larger. The positive twin of that slab cell returned `true`.
- One mutation of mine was ill-posed and I discarded it: I lowered the error budget FN/FD, which makes the check easier to pass, not harder.

## 5. Independent numerics (mpmath 1.3.0, one process)

- `nzeros(1000)` = 649. Walking `zetazero` gives the same 649, all on the critical line; the last is 999.7916 and the next is 1001.3495.
- All 25 bands: the declared `n` equals the number of zeros mpmath finds in [T0, T1].
- The declared counts add up to 650, which is 649 plus one zero counted twice. Band 5 is [201, 241.25] and band 6 is [241, 281]. They overlap on [241, 241.25], and that overlap holds exactly one zero, at 241.0492. The overlap is there because that zero sits too close to 241 to allow an upper slab above 241. It does not affect soundness, and the bands still cover [1, 1000].
- Slab checks (U41, L241, U965_4, U520): none of the four contains a zero ordinate, and the minimum of |ζ| on a 19x11 grid over 0 < x < 1 is at least 0.12 in each.
- Horizontal argument changes, 2 to -1:
  - T = 41: 2.6965580, inside [2.695651, 2.706101].
  - T = 241.25: 2.6778336, inside [2.657303, 2.680931].
  - T = 241: -2.6532024, inside [-2.658746, -2.651562].
- Pin check: for bands 0, 5, 6 and 24, the total argument change around each box divided by 2π equals 7.0, 24.0, 24.0 and 32.0, which matches `n` in each band.

## 6. What this establishes, and what it does not

It establishes that the Lean kernel accepts a proof, using only the standard three axioms and with no hypotheses, no `sorry` and no `native_decide`, that every nontrivial zeta zero with 0 < Im ≤ 1000 has Re = 1/2.

It does not establish RH or anything above height 1000. It trusts the Lean kernel and Mathlib's definitions. Because I used `--no-build`, the files were not recompiled in this audit; up-to-date build traces stand in for a fresh compile. conjecture1_proved = False.
