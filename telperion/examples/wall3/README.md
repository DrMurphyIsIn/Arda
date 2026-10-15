# WALL-3/4/5/6 track T certificates

This directory holds track T's (Telperion's) certificates for the WALL-3 to WALL-6 research rounds of the RH team.
conjecture1_proved = False, and nothing here is progress on RH. Each certificate covers a *finite* numerical fact
(a zero box, a zero count, a ball enclosure, an exact count) about a calibration object, so that the tracks' float
numbers can be quoted as ARB, EXACT or KERNEL instead of COMPUTED. TOOLS3.md explains the trust classes and the
invocations; the scripts are in `scripts/` and their outputs in `certs/`.

All winding numbers and zero counts go through `telperion.arb_fakes` (`rigorous_winding`, `certify_zero_box`,
`count_offline`), which is on Arda main at 2dfc6eeee (PR #741; byte-identical to 72470dd5f, which carries the s = 1
pole guard). User-supplied objects are passed in as callables. A callable carries no declared poles, so every
script that counts zeros of a callable also certifies the pole exclusion it relies on.

## Where the scripts read and write (scripts/_paths.py)

Every script goes through `scripts/_paths.py`, the single path mechanism:

- **Inputs from the rh-team tracks** are read with `rh("<relative path>")`. Unless `TELPERION_RH_TEAM` is set
  explicitly, `rh()` takes the copy vendored under `inputs/<relative path>`, so the scripts rerun from the repo
  alone. Vendored copies (all small):

  | relative path | read by |
  |---|---|
  | `wall3/B/out/tw_REAL_*.json` (track B's runs; the residue A per run) | b_twist_real, b_twist_real_g, b_residue_check |
  | `wall3/E/out/e4_arb.cert.json` (track E's Arb table) | e_afe_recheck |
  | `wall2/F1/f1_arb_rouche.py` (WALL-2 F1's arc-ball Rouche code, imported read-only) | r_rouche_margins |

- **Certificates are written** with `cert_path(name)`: to a scratch dir by default; set
  `TELPERION_WRITE_COMMITTED_CERTS=1` to regenerate the committed `certs/` on purpose (the script announces the
  target on stderr). Certificates read as inputs (e.g. P_dominance_ratios by the other P scripts) use `cert_read`.
- `t3tools.py` is put on `sys.path` by `_paths`; `d1_r2_continuous` execs the prefix of `scripts/n8_continuous.py`.

The Lean file for the function-field fake is `lean/FFFake.lean` (core Lean v4.32.0; `run2.log` is its second and
last run). The `kernel` block in `certs/E_ff_fake.cert.json` is emitted verbatim by `e_ff_fake.py` and marked
STATIC: it describes those Lean runs and is not computed by the script.

## Reading a certificate

- `trust_class` is `arb`, `exact` or `KERNEL (finite arithmetic on local definitions)`.
- `winding` is zeros minus poles inside the box; `zeros_in_box` adds back the poles passed in `poles=`.
- Fields named `*_float` or `D1_floats` / `B_float*` are the tracks' float values, kept for comparison only.
  Comparison fields such as `B_float_within_ball_plus_1e-14` or `overlap_E` are tolerance tests, not certificates.
- Callables are recorded as `callable:<name>`.
