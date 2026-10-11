# Zero-free watch: triage log

One line per hit, newest first. The seen-list `zero_free_seen.json` is updated only after the hit is triaged here.
Run: `PYTHONPATH=telperion/src python -m telperion.zero_free_watch` (add `--update` after triage). conjecture1_proved = False.

- 2026-10-11 **arxiv:2610.12234v1** [strip] Baiying Liu, "Slightly improved zero-free half-planes for the quasi-Riemann
  hypothesis" (8 Oct 2026): varies OpenAI's `b, ell`; `B_new = (1507 - 2 sqrt 921)/1653 = 0.874957...` with a Lean
  formalization at OpenAI's pin (Mathlib d13f23b, vendored OAI closure at adc7f124, verify.py with the standard axiom
  whitelist). ACTION: replay through Comparator, then compose with the dbn bridge at `theta = B_new`
  (`Lambda <= 2 (B_new - 1/2)^2 ~ 0.28119`, below the kernel-checked 9/32). Owner: e9 (replay); bridge composition to
  be coordinated with the Riemann session. The first live poll found this; it is exactly what the watcher is for.
- 2026-10-11 **openai:The-Quasi-Riemann-Hypothesis-October-5-2026** [strip] the simplified 11/12 paper (paper2). Known;
  see OAI_QRH_METHOD_MAP_2026-10-10.md.
- 2026-10-11 **openai:The-Quasi-Riemann-Hypothesis-September-30-2026** [strip] the 7/8 paper. Known; converted to
  `Lambda <= 9/32` (RH_dbn_real_zeros_nine_thirtyseconds).
- 2026-10-11 **arxiv:2608.06286v1** [input] "Average analytic rank for the L-functions of the elliptic curves
  y^2 = x^3 - dx": false positive on "Patterson" (author name). No action.
