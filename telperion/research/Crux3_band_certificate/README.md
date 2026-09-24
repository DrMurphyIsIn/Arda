# Crux3 band certificate: numerics and generators

These are the scripts behind `telperion/docs/Crux3_BAND_CERTIFICATE_2026-09-24.md` and the Lean modules
`Crux3_Band*.lean` on the `rvm_bridge` island. Everything runs in a single process with python3,
mpmath, numpy, scipy and python-flint (Arb). There are no multiprocessing pools.

`conjecture1_proved = False`. These scripts compute and certify finite instances of the Weil form on
a two-dimensional band of test functions. None of them bears on RH itself.

## What each script does

| script | purpose | runtime |
|---|---|---|
| `weilmodes.py` | Weil matrices of zeta and D in the grid Fourier basis `e^{2πimu/a}` on the window. The closed forms follow crux2 κ-certify's `galerkin_cos.py`. Reproduces κ-certify's D values `-2.5877383e-4` and `-1.0854653e-3` at `x = 40`, `N = 60` exactly. | seconds |
| `weilfreq.py` | the same for arbitrary frequencies, including non-grid ones; agrees with `weilmodes.py` to `1e-29` on grid frequencies | seconds |
| `dhzeros.py` | Davenport-Heilbronn zeros to height 300 (`dh_zeros.json`): on-line zeros by sign changes of `Z_D`, the four off-line zeros below 200 by Newton, and the argument-principle count, which agrees at `T = 50, 100, 150, 200` | about 3 min |
| `window_scan.py` | scans windows `A = qπ` for the best 2- and 3-mode Dirichlet-cosine bands separating zeta (positive definite) from D (indefinite) | about 1 min |
| `zeroside_check.py` | zero-side cross-check of the certificate instance. zeta: arithmetic side `0.6988851105`, zero side `0.6988851154`. D: `-0.6546194311` against `-0.6546405749`, with the off-line quadruple at 85.699 contributing `-1.046` | about 1 min |
| `optx.py`, `optx2.py`, `horizon.py` | height-local detection horizons for D's off-line zeros, using free-frequency complex bands | minutes to an hour |
| `cert_model.py` | the closed-form Lorentzian certificate model as a function of `N`. It converges to `0.698` (`N = 1000`: 0.6968; `N = 100`: 0.6114) | seconds |
| `arb_cert.py` | Arb certification of both sides: zeta's Lorentzian lower bound is positive definite at `λ = 1/2`, and D's exact band matrix has a certified negative Rayleigh quotient `-0.6545762050 ± 3e-11` at `c = (-3, 2)` | seconds |
| `mirror.py`, `final_mirror.py` | an exact-rational (`fractions.Fraction`) mirror of the Lean prime-side checker and of the final 2×2 check: `α = 7.5987`, `δ = 0.3700`, `β = 1.0942` | under a second |
| `gen_table.py`, `gen_lam.py` | generate the Lean table `tab` and the von Mangoldt table lemma `lam_tab` in `Crux3_BandTable.lean` | under a second |
| `dh_symbolic.py` | D's weights `c_D(n)`, `n <= 56`, symbolically, as polynomials in κ times prime logs, from `a(n) log n = Σ_{d ∣ n} c(d) a(n/d)`. Writes `dh_coeffs.json` and checks it against the numeric recursion (`4e-16`) | under a second |
| `gen_dh.py` | generates `dtab` and the 56 per-n identity lemmas plus the dispatcher `cD_conv` of `Crux3_BandDHData.lean` (writes `dtab.lean`, `dconv.lean`; both appear verbatim in the module) | under a second |
| `dmirror.py` | exact-rational mirror of the D prime-side checker (κ ball, prime-log balls, Horner balls): `PD11 = 4.937230860`, `PD22 = -1.239492159`, `PD12 = -7.350119196` | under a second |
| `gen_dtabE.py` | generates the D checker data of `Crux3_BandDH.lean` (square-root brackets, `lpTab`, `dtabE`; writes `dtabE.lean`, which appears verbatim in the module) | under a second |
| `dfinal.py` | the exact thresholds of the D certificate (`N = 300`, `R = 175`) and the final check: arch `<= 4.3188`, prime `>= 4.8630`, form `<= -0.5443` (units of `‖v‖²`) | seconds |
| `dh_model.py` | floating-point model of the D upper bound, used to choose `N` and `R` | seconds |

## The instance

| item | value |
|---|---|
| window | `A = 9π/14`, `x = e^{9π/7} = 56.780` |
| tests | `v(u) = c1 cos(763u/9) + c2 cos(259u/3)` on `[-A, A]`, `0` outside |
| Dirichlet condition | `k1 A = 109π/2`, `k2 A = 111π/2`, so every `v` is continuous |
| zeta | `Q_ζ(v) ≥ 0.699 ‖v‖²` (computed); kernel-checked `≥ (1/2) ‖v‖²` (`Crux3.band_floor`) |
| D | `Q_D(v) = -0.6546 ‖v‖²` at `c = (-3, 2)` (Arb-certified); kernel-checked `<= -(1/2) ‖v‖²` (`Crux3.dh_band_negative`, with `band_separation` for both sides at once) |

## Reproduce

```sh
cd telperion/research/Crux3_band_certificate
python3 arb_cert.py          # both sides, Arb
python3 zeroside_check.py    # zero sides (needs ../zeros2000.json and dh_zeros.json)
python3 final_mirror.py      # the exact-rational mirror of the Lean checker
python3 dh_symbolic.py && python3 gen_dh.py && python3 gen_dtabE.py && python3 dfinal.py   # the D side
cd ../../examples/rvm_bridge/lean
lake build Crux3_BandCert Crux3_BandDH && lake env lean AxiomGuardRvMBridge.lean
```
