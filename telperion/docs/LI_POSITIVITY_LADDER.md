# Li positivity-ladder emitter (RH-roadmap Track 2)

Certifies finite prefixes of **Li's criterion** onto the *already-formalized* upstream
reduction, surfaced by the Palomar miner:

    nicholasbulka/li-criterion-rh-equivalence-lean
    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

(`liSummand n ρ = 1 − (1 − 1/ρ)^{−(n+1)}`; the RHS is the Li–Keiper positivity ladder.)

## What the emitter does

`LiPositivityLadderEmitter` (kind `li_positivity`) emits, per rung `n`:

    theorem li_rung_<n> (hlo : (lo : ℝ) ≤ (taylorCoeff riemannXi n).re) :
        0 ≤ (taylorCoeff riemannXi n).re :=
      le_trans (by norm_num : (0:ℝ) ≤ lo) hlo

- `lo` is a **certified positive rational lower bound** on the n-th ξ Taylor coefficient's
  real part. `certify` refuses `lo ≤ 0` (a non-positive bound cannot witness positivity) and `n < 0`.
- The claim is **load-bearing**: it is about the ACTUAL `(taylorCoeff riemannXi n).re`, not an
  abstract real — so it is non-vacuous.

## Trust seam (documented, honest)

`hlo` — the lower bound `lo ≤ (taylorCoeff riemannXi n).re` — is an EXTERNAL numeric input
(Arb / mpmath interval arithmetic on ξ's Taylor coefficient at 0), carried as a theorem
HYPOTHESIS. The kernel proves only `0 ≤ lo ⟹ 0 ≤ coeff`; it does NOT evaluate the
transcendental coefficient. Same discipline as the RH-in-a-box Arb enclosures and the
effective-dVP inputs.

## Honest ceiling

Each rung is a finite verification. The **uniform `∀ n`** is exactly the RHS of
`li_criterion_rh_iff` — i.e. **RH itself**. Certifying rungs 0..N is NOT progress toward RH;
it is the certificate-shaped, generator-producible prefix of a reduction whose tail is RH.
`conjecture1_proved = False`.

## Wiring status / TODO

- Emitter + `certify` + registry wiring + Python tests: DONE (this branch), classification green.
- The emitted rungs `import Lc.LiCriterion.XiOrderBridge`; **CI compilation needs the upstream
  `li-criterion-rh-equivalence-lean` as a lake dependency** (add a `require` to a new
  `examples/li_positivity/lean/lakefile.toml`, mirroring how `zeta_zero_localization` requires
  its sibling `zero_free_bridge`). Until wired, rungs are emitted-but-not-CI-compiled.
- NEXT: an Arb finder (`enclose_xi_taylor_coeff`) that computes the rigorous `lo` per n
  (reuse/extend `telperion.arb_enclosure`), turning the trust-seam hypothesis into a produced
  certificate — then assemble `∀ n < N, 0 ≤ (taylorCoeff riemannXi n).re` and cite
  `li_criterion_rh_iff` for the "first N rungs verified" statement.
- Reuse the RvM/explicit-formula foundation (`RVM_EXPLICIT_FORMULA_FOUNDATION.md`,
  `DiffractionCore.rect_explicit_formula`) if expressing λ_n via the arithmetic side later.
