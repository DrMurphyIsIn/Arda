# zero_free_bridge — the Mertens certificate meets ζ (kernel-gated)

Hand-written, Mathlib-only frozen Lean (`lean/ZeroFreeBridge.lean`, kernel-checked by
`telperion-lean-e2e` via `lake build`). 16 theorems, generator UNTRUSTED, the Lean kernel the sole
arbiter. `conjecture1_proved = False` — this is **not** a proof of RH.

## What it proves

**The bridge.** The Mertens nonnegative-cosine certificate `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`,
proven in-kernel to hold on the actual Dirichlet series of `−ζ'/ζ`: for `σ > 1`,

    0 ≤ 3·Re(−ζ'/ζ)(σ) + 4·Re(−ζ'/ζ)(σ+it) + Re(−ζ'/ζ)(σ+2it)

(`zeta_logDeriv_comb_nonneg`, via `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). This is the exact
positivity the classical de la Vallée Poussin zero-free-region argument runs on. The chain:
`mertens_three_four_one` → `cpow_re` (`Re(n^{−s}) = n^{−σ}cos(t·log n)`, the crux) → `term_re` →
`term_comb_nonneg` → `vonMangoldt_re_comb_nonneg` → `zeta_logDeriv_comb_nonneg`.

**`residue_logDeriv`** (+ 3 helpers `logDeriv_congr_punctured`, `logDeriv_zpow_smul_split`,
`tendsto_sub_mul_logDeriv_zero`) — a general complex-analysis lemma, *order = residue of `logDeriv`*:
for `f` meromorphic at `z₀` of order `n`, `(z−z₀)·logDeriv f z → n` on the punctured neighbourhood.
Built from `meromorphicOrderAt_eq_int_iff`. This is a genuine **Mathlib v4.32.0 gap-filler** — the
library has only the analytic simple-zero (`n=1`) case (`AnalyticAt.tendsto_mul_logDeriv_simple_zero`);
the general-order version is master-only. Reusable, not RH-specific.

**`zeta_boundary_contradiction`** — the de la Vallée Poussin core: the positivity `×(σ−1)`, taken to
`σ→1⁺`, forces `3·1 − 4k − k' ≥ 0` (residue `+1` at the pole `s=1`, `−k` at a zero of order `k` at
`1+it`, `−k'` at `1+2it`), impossible for `k ≥ 1`. This routes non-vanishing through `−ζ'/ζ` — a
*different internal path* from Mathlib's product-route `riemannZeta_ne_zero_of_one_le_re`. The three
residue limits enter as hypotheses (each is the real-line restriction of `residue_logDeriv`).

**The improved (degree-3) certificate.** The de la Vallée Poussin polynomial is *not* optimal.
Optimizing the leading-order zero-free functional `F(P) = (√a₁−√a₀)² / Σ_{k≥1}aₖ` over nonnegative
cosine polynomials (`aₖ ≥ 0`) — the Mossinghoff–Trudgian 2015 program (`R₀ = 5.573412`) — widens the
region *constant*. The `(1+cos)ⁿ` family gives clean Fejér–Riesz certificates; `n=3` gives
`20 + 30cos θ + 12cos 2θ + 2cos 3θ = 8(1+cos θ)³ ≥ 0` (`mertens_improved`), with `a₁=30 > a₀=20` and
`F = 0.02296` vs `0.01436` (1.60× wider, leading order). Carried onto `−ζ'/ζ` in `zeta_logDeriv_comb4_nonneg`:
`20 Re(−ζ'/ζ)(σ) + 30 Re(−ζ'/ζ)(σ+it) + 12 Re(−ζ'/ζ)(σ+2it) + 2 Re(−ζ'/ζ)(σ+3it) ≥ 0` for `σ>1`. This
improves the classical-region **constant only** — not the Vinogradov–Korobov *rate*, and not RH.

## Honest scope

Not a proof of RH. `zeta_boundary_contradiction` is the `c=0` **boundary** edge of the classical region,
and `ζ(1+it)≠0` **already exists in Mathlib** (product route). A fully unconditional `ζ(1+it)≠0` also
needs ζ's simple-pole handle at `s=1` (a v4.32.0 API gap — Mathlib's ζ carries a junk value there, so
`(s−1)ζ` isn't analytic; build from `completedRiemannZeta`), order-finiteness, and `.re`/real-ray
plumbing — all classical, none certificate-shaped. The region beyond the boundary further needs the ζ
growth bound `|ζ(σ+it)| ≪ log|t|` (ordinary analysis, not certificate-shaped). See
`../../docs/ZERO_FREE_REGION_TERRAIN.md` for the cited terrain map.
