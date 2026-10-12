# Zero-free watch: triage log

One line per hit, newest first. The seen-list `zero_free_seen.json` is updated only after the hit is triaged here.
Run: `python telperion/src/telperion/zero_free_watch.py` (stdlib only; the package import needs sympy) (add `--update` after triage). conjecture1_proved = False.

- 2026-10-12 **arxiv:2610.12803v1** [dbn] Hakimoglu-Brown, "A conditional bound Lambda <= 0.13963 for the de
  Bruijn--Newman constant" (8 Oct 2026): ASSUMES the 7/8 half-plane (OpenAI) and feeds it into a Polymath-15-style
  barrier argument (published Polymath numerics, Riemann-Siegel coefficient bounds, 24 strip-comparison steps,
  polynomial certificates). Not a new strip. Its input is now proved (Liu's B_new > 7/8 is kernel-checked), so the
  bound would be unconditional modulo its numerics; nothing is Lean and the Polymath numerics are far outside the
  dbn island. Recorded only; the kernel-checked picture stays 0 <= Lambda <= 0.2811857. No action now.
- 2026-10-12 **arxiv:2609.23222v2** [strip] Fiori, Jaskari, "Explicit bounds for the prime number theorem" (v2,
  8 Oct 2026): USES the 7/8 half-plane for explicit psi(x) - x bounds. Consumer, not a new strip. No action.
- 2026-10-11 **arxiv:2610.12234v1** [strip] Baiying Liu, "Slightly improved zero-free half-planes for the quasi-Riemann
  hypothesis" (8 Oct 2026): varies OpenAI's `b, ell`; `B_new = (1507 - 2 sqrt 921)/1653 = 0.874957...` with a Lean
  formalization at OpenAI's pin (Mathlib d13f23b, vendored OAI closure at adc7f124, verify.py with the standard axiom
  whitelist). ACTION: replay through Comparator, then compose with the dbn bridge at `theta = B_new`
  (`Lambda <= 2 (B_new - 1/2)^2 ~ 0.28119`, below the kernel-checked 9/32). Owner: e9 (replay); bridge composition to
  be coordinated with the Riemann session. The first live poll found this; it is exactly what the watcher is for.
- 2026-10-11 **arxiv:2610.04045v1** [input] de Faveri, "Optimal large sieve for fixed order characters" (2 Oct 2026): the
  best proved sextic/n-th order large sieve, already in SEXTIC_BOTTLENECK section 7 (it does not move the 7/8 boundary).
  No further action.
- 2026-10-11 **openai:An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026** [input] OpenAI's cubic
  first moment (cited by the 7/8 paper as not used). Known. No action.
- 2026-10-11 **arxiv:2609.39706v1** [input] sixth moment of a degree two L-function (large sieve). Not on the sextic
  bottleneck. No action.
- 2026-10-11 **arxiv:2608.10121v2** [input] Fourier summation formulas on a strip ("Selberg class"). No action.
- 2026-10-11 **arxiv:2608.20654v1** [input] curves y^3 = x^{(q^2+1)/2} + x ("cubic Gauss sum", finite fields). False
  positive. No action.
- 2026-10-11 **openai:The-Quasi-Riemann-Hypothesis-October-5-2026** [strip] the simplified 11/12 paper (paper2). Known;
  see OAI_QRH_METHOD_MAP_2026-10-10.md.
- 2026-10-11 **openai:The-Quasi-Riemann-Hypothesis-September-30-2026** [strip] the 7/8 paper. Known; converted to
  `Lambda <= 9/32` (RH_dbn_real_zeros_nine_thirtyseconds).
- 2026-10-11 **arxiv:2608.06286v1** [input] "Average analytic rank for the L-functions of the elliptic curves
  y^2 = x^3 - dx": false positive on "Patterson" (author name). No action.
