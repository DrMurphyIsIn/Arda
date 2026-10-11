# qrh_stage3: the Stage II exponent system of OpenAI's 7/8 half-plane, as a model

Companion to `telperion/docs/OAI_QRH_METHOD_MAP_2026-10-10.md` (section 5, "Model results").

- `stage2_model.py`: exact-rational reproduction of every certificate in paper1 §20 at the paper's values
  (C(7/8) = 3/16; (20.5) = -7/1200; (20.6) = -79/800; (20.7) = -1/48 - delta/16; Lemma 20.2's identity
  (20.9) symbolically and its 49/440640 margin on a grid; (20.11) = -49/14400). Run: `python stage2_model.py`.
- `stage3_search.py`: the system with the boundary sigma0, the previous-stage bound beta_in (bin ceiling
  alpha = 2 beta_in - 1; baseline capacity 1/(6(2 sigma0 - 1))) and the geometry (lx, b, ell; ly = lx + b,
  h = 1 - lx + ell, lx + ly + ell = 1) as parameters, with the §15 low-side constraints. Run:
  `python stage3_search.py`.

Both need only Python 3 + sympy (the e9 venv has them). What the model covers and what it does not is
stated at the top of each file and in the map. conjecture1_proved = False.

**Correction (2026-10-11):** `stage3_search.py` sets the bin ceiling `alpha = 2 beta_in - 1`; the paper FIXES
`alpha = 5/6` (paper.tex l. 15101) independently of the previous stage. With `alpha = 5/6` the high-side shortfall at
`ell = 1/5` is 0.044 (not 0.026) and the binding bin is Lemma 20.2's balanced witness count. See
`~/arda-research/followups/highside_sweep_ell_1_6_to_1_5.md` and SEXTIC_BOTTLENECK_2026-10-11.md section 7. The scripts
here are left as they were; `kmodel_heuristic.py` inherits the same `alpha` and the same caveat.
