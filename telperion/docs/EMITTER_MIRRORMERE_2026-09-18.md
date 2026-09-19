# MIRRORMERE emitter additions -- 2026-09-18

conjecture1_proved = False.  Nothing in this document, and nothing emitted by the tools it
describes, is progress toward RH.  Each entry is a finite, unconditional, kernel-checked
fact, and several of them are explicitly NEGATIVE controls: they certify that a hoped-for
property FAILS at finite truncation.

## `twofreq_offline` -- certified OFF-line displacement of a two-frequency section

**Module** `telperion/src/telperion/emit_twofreq_offline.py` ·
**Emitter** `TwoFreqOfflineEmitter` ·
**Dogfood** `telperion/examples/twofreq_offline/generate.py` ->
`examples/quasicrystal/lean/EulerFactorSectionOffline.lean` ·
**CI** `twofreq-offline-compiles` ·
**Adapter** `negctrl_adapters/adapter_twofreq_offline.py` ·
**Stance** `STRUCTURALLY_NONVACUOUS` + `NEG_CONTROL_ADAPTER`.

### The shape

The quasicrystal island proves (`TwoFreqRigidity.lean:92`, v4.32)

```
twoFreq_realRooted_iff :
  c1 != 0 -> c2 != 0 -> lam1 != lam2 ->
  ((forall x : C, twoFreq c1 c2 lam1 lam2 x = 0 -> x.im = 0) <-> ||c1|| = ||c2||)
```

`selfinversive_rigidity` (2026-09-14) emits the POSITIVE direction: `|c1|^2 = |c2|^2`
EXACTLY, hence real-rooted.  `twofreq_offline` emits the NEGATIVE direction: `|c1|^2 !=
|c2|^2` EXACTLY, hence NOT real-rooted -- some zero lies strictly off the real line.

The two emitters **partition the coefficient space**.  Each REFUSES precisely the regime
the other certifies (`selfinversive_rigidity` refuses unequal modulus; `twofreq_offline`
refuses equal modulus), so neither can emit a false theorem, and the pair of refusals is
the anti-phantom guard for both.

### Why it was needed

`MM_euler_factor_section_offline` (ladder rung T2, `QC_TORUS_SECTION_LADDER_MEMO`
sections 4b/5) is exactly the negative direction at the `p = 2` Euler factor, and its
coefficient is the IRRATIONAL `-1/sqrt 2` -- which the Gaussian-rational-only
`selfinversive_rigidity` emitter cannot take.  So the emitter adds:

* three coefficient literal shapes with EXACT rational moduli --
  `gauss(re, im)` (`|c|^2 = re^2 + im^2`), `inv_sqrt(s, sign)` (`|c|^2 = 1/s`),
  `real_sqrt(q, s)` (`|c|^2 = q^2 s`);
* two frequency literal shapes -- `rat(r)` and `neglog(p)` (the literal `-(Real.log p)`).

That turns the single registry node into the whole T2 FAMILY: for every `p >= 2`, the
Euler factor `1 - p^(-s)` read on `s = 1/2 + i x` is the section
`twoFreq 1 (-(1/sqrt p)) 0 (-(log p))`, whose moduli `1` and `1/sqrt p` never agree.

### What each instance emits

1. `{nm}` -- `NOT (forall x : C, twoFreq c1 c2 lam1 lam2 x = 0 -> x.im = 0)`;
2. `{nm}_offline_zero` -- the existence corollary `exists x, ... = 0 AND x.im != 0`;
3. `{nm}_displacement` (mode `displacement`, Euler-factor shape ONLY) -- the certified
   LOCATION: `forall x, ... = 0 -> x.im = 1/2`, i.e. every zero sits on `Re s = 0`,
   uniformly, with no dependence on the truncation.

### Refusals (all EXACT rational arithmetic, no floats)

`|c1|^2 == |c2|^2` (the sum IS real-rooted -- the emitted negation would be FALSE); a zero
coefficient; `lam1 == lam2` including the disguised `neglog(1) == rat(0)` (log 1 = 0); a
negative rational frequency opposite a `-log p` frequency (the emitted separation is
`-log p < 0 <= r`); a radicand that is not an integer `>= 2`; `mode='displacement'`
outside the Euler-factor shape (the general displacement is
`-log(|c1|/|c2|) / (lam2 - lam1)`, not `1/2` -- refused rather than guessed); `p < 2`.

### Negative control

`adapter_twofreq_offline` forges the `selfinversive_rigidity` TRUE instance
(`c1 = 3/5 + 4/5 i`, `c2 = 1`, equal moduli 1) by hand-minting the frozen dataclass, thus
bypassing the Layer-1 refusal.  The forged proof reaches `h2 : (1 : R) = 1` with goal
`False` and the kernel rejects it (observed: `unsolved goals ... h2 : True |- False`).  The
true twin -- the `p = 2` Euler factor, moduli 1 vs 1/2 -- compiles clean.  Both twins are
rendered in BRIDGE-HYPOTHESIS mode (the island `twoFreq` copied verbatim into the prelude,
the island iff carried as an explicit hypothesis `hiff`), because the harness elaborates
against plain `import Mathlib`; the same discipline as `adapter_bragg_floor`.  The
hypothesis-FREE island theorem is what the `twofreq-offline-compiles` CI job builds.

### Verification performed (2026-09-18, local, v4.32 quasicrystal island)

* `lake build EulerFactorSectionOffline` -- green, 8 theorems, no warnings;
* `#print axioms` on all 8 -- `[propext, Classical.choice, Quot.sound]`;
* `telperion.statement_match.statement_match_check` -- 2/2 match, so
  `euler_factor_section_offline` and its displacement companion state EXACTLY the intended
  propositions (kernel-level defeq, not string containment);
* `generic_negative_control` against the island env -- `kernel_rejects=True`,
  `true_compiles=True`, `okay=True`.

### Honest scope

A finite fact about ONE Euler factor at a time.  It says nothing about zeta, about the
Euler product, or about RH.  Read positively it is a WARNING: per-rung line membership
genuinely fails, at every rung and every prime, with a uniform displacement of 1/2, so
critical-line membership can only ever be an infinite-N continuation phenomenon -- never a
finite-section fact.  conjecture1_proved = False.
