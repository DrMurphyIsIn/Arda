# crux_dynamics-ergodic: the Lax–Phillips edge no-go, built

`conjecture1_proved = False`. RH is open. Nothing in this directory or in the companion Lean
file says anything about where the zeros of zeta are. What it does is pin down, precisely and
in the kernel where possible, what the dynamical lens (unitary scattering on the modular surface
`PSL(2,Z)\H`) can and cannot see. It also records four corrections to the submitted idea.

- **Lean (kernel-checked):**
  `telperion/examples/li_positivity/lean/Crux/Crux_dynamics_ergodic.lean`. It has 94 theorems and
  lemmas. Each one prints `[propext, Classical.choice, Quot.sound]` under `#print axioms`. There is
  no `sorry`, no `native_decide` and no new `axiom`.
- **Computations (this directory):** Python 3.9 (`/usr/bin/python3`), python-flint 0.6 (Arb) and
  mpmath 1.3. The trust class is stated per claim below.

## How to re-run

```
# Lean, single-file elaboration (never `lake build`; the island .lake is shared)
cd telperion/examples/li_positivity/lean
<leanlock.sh> lake env lean Crux/Crux_dynamics_ergodic.lean     # ~10-40 s, 94 axiom lines

# computations
cd telperion/research/crux_dynamics-ergodic
/usr/bin/python3 hecke_orbit_class_numbers.py   # ~1 s    exact integers
/usr/bin/python3 hecke_orbit_genus.py           # ~2 s    exact + Arb certificates
/usr/bin/python3 certify_zeros.py               # ~6 s    Arb certificates
/usr/bin/python3 orbit_scan.py 60               # ~3 min  floating point (not a certificate)
/usr/bin/python3 scattering_checks.py           # ~2 min  floating point (not a certificate)
```

## 1. The kernel-checked core (what the Lean file proves)

The Lean file's header lists each theorem. In outline, with the status tag for each part:

| Part | Statement | Tag |
|---|---|---|
| Finite orbit core | One functional-equation quadruple is a contractive factor of `φ(s) = Λ(2s-1)/Λ(2s)` on `Re s ≥ 1/2` iff `0 ≤ Re ρ ≤ 1`, and it is unimodular on the axis (`scat_edge_iff`, ...). | THEOREM-kernel-checked (ported from `ResonanceEdge.lean`) |
| Multiplicity-correct multisets | Zero multisets are closed under `ι w = 1 - conj w`. `ch_edge_iff`: the `h`-shifted channel is pole-free and contractive iff every zero has `\|Re w - 1/2\| ≤ h`. `cooked_quadruple_threshold`: `ρ₀ = 3/4 + 20i` is seen by channel `h` iff `h < 1/4`. | THEOREM-kernel-checked |
| Real `ξ` is contractive | `xi_inner`: `‖ξ(2s-1)‖ ≤ ‖ξ(2s)‖` for `Re s ≥ 1/2`. It comes from the upstream unconditional paired Hadamard factorisation (LiCriterion) and the gap `\|ρ + conj v\|² - \|ρ - v\|² = 4 Re ρ Re v`. | THEOREM-kernel-checked (classical fact, new kernel proof) |
| Birman–Krein | `bk_of_inner`: for any `Λ` with the functional equation and reality, contractivity forces `Re(conj Λ Λ')(1+2it) ≥ 0`. `bk_phase_identity`: `logDeriv φ_Λ(1/2+it) = -4 Re Λ'/Λ(1+2it)`. | THEOREM-kernel-checked |
| **Channel no-go** | `ChannelAxioms` bundles entire, FE, reality, the edge (no zero on `Re w ≥ 1`), contractivity, axis unitarity and weak BK positivity. It holds for `ξ` and is closed under multiplication by the quadruple of any finite set of points of the open strip. `channel_axioms_do_not_imply_rh`. | THEOREM-kernel-checked |
| Exchange rate | `zero_free_strip_iff_shift_contractive`: all zeros satisfy `\|Re ρ - 1/2\| ≤ h₀` iff every shift `h > h₀` is contractive. `rh_iff_all_shifts_contractive` and `rh_iff_resonances_on_quarter_line` use Mathlib's `RiemannHypothesis`. | THEOREM-kernel-checked; RELABELINGS, flagged, used only to price an improvement |
| Hecke–wave | `λ_n(s) = Σ_{ad=n}(a/d)^{s-1/2}` is invariant under `s ↦ 1-s`, so it is a function of `s(1-s)` on unitary AND resonant states (`heckeEig_fun_of_laplace`). It is real on the axis, and `λ_p(1/2+ir) = 2 cos(r log p)`. | THEOREM-kernel-checked (scalar core; the operator form is classical) |
| Emergent unitarity | `finite_euler_blowup_on_axis`: every finite Euler truncation of the scattering matrix blows up along the axis at `s = 1/2`. | THEOREM-kernel-checked |
| Hecke-orbit correction | `2i ∈ T_2(i)`, `3i ∈ T_3(i)`, `4i ∈ T_4(i)`. `euler2_disc16_zeros_on_line` and `euler3_disc36_zeros_on_line`: the local Euler-factor corrections have all their zeros on `Re s = 1/2`. | THEOREM-kernel-checked |

**The no-go in one sentence.** Contractivity, unitarity, the edge and Birman–Krein positivity are
all properties of the scattering channel. They hold for `ξ` and for `ξ · Q_{ρ₀}`, and
`ξ · Q_{ρ₀}` vanishes at `ρ₀ = 3/4 + 20i`. So no argument that uses only these properties can put
the zeros on the line (`channel_axioms_do_not_imply_rh`). The Hecke operators do not help on the
channel: their eigenvalues there are a fixed function of the Laplace eigenvalue `s(1-s)`, the same
for `ξ` and for any fake (`heckeEig_fun_of_laplace`). A usable argument has to use non-unitary
arithmetic on the resonant sector, which is quasi-RH by the exchange rate, or data off the
channel, such as cusp forms or the trace formula, at the exact arithmetic point.

**Scope of "Unitarity = PNT".** Taken as a whole, the channel data are the edge: no zero on
`Re w ≥ 1`, i.e. regular Eisenstein data on the axis, which is the PNT input. Contractivity alone
needs even less: zeros in the CLOSED strip, because zeros on `Re w = 1` cancel inside `φ`
(`inner_forces_partner`). The Lean proof of `xi_inner` goes through the upstream zero-set
description, which consumes Mathlib's zero-free line, but mathematically that line is not needed
for contractivity.

## 2. Corrections to the submitted idea (with evidence)

1. **Normalisation of the scattering matrix.** The Eisenstein scattering matrix is
   `φ(s) = Λ(2s-1)/Λ(2s)` with `Λ = completedRiemannZeta`. It has the pole of the residual spectrum
   (the constants) at `s = 1` and is not bounded on `Re s > 1/2`. The contractive object is
   `φ_ξ(s) = φ(s)(s-1)/s = ξ(2s-1)/ξ(2s)`. In the kernel this is `modScat_eq` together with
   `scatXi_one_ne_zero`. Floating-point illustration (`scattering_checks_output.json`, item b):

   | s | 1.001 | 1.01 | 1.1 | 1.5 | 3 |
   |---|---|---|---|---|---|
   | `\|φ\|` | 955.8 | 96.36 | 10.41 | 2.74 | 1.20 |
   | `\|φ_ξ\|` | 0.955 | 0.954 | 0.946 | 0.912 | 0.801 |

   Even at `s = 3`, `|φ| > 1`.
2. **Contractivity is weaker than PNT.** See the scope note in section 1 and `inner_forces_partner`.
3. **Multiplicity.** The quadruple `{ρ, conj ρ, 1-ρ, 1-conj ρ}` counts an on-line zero twice. The
   Lean file uses `ι`-closed multisets instead, where a simple on-line zero is `[ρ, conj ρ]`
   (`pairList_iota_closed`).
4. **The Hecke orbit of `i` is not "`i` plus class-number ≥ 2 points".** It contains two
   class-number-one points, `i` (`f = 1`) and `2i` (`f = 2`, `2i ∈ T_2(i)`, discriminant -16). The
   extra Euler factor at `2i` has all its zeros on the line, so RH at `2i` is equivalent to RH at `i`.
   The consequence the idea drew, that no open or almost-everywhere property of the base point
   implies RH at `i`, does not rely on this claim. It rests on the base-point genericity theorem
   (paper proof, not formalised).

## 3. Computations: exact claims and data

### 3.1 Class numbers along the Hecke orbit of `i`: exact integers

Script: `hecke_orbit_class_numbers.py`. Output: `hecke_orbit_class_numbers_output.txt`.

- The point `(a i + b)/d ∈ T_n(i)` is a CM point with primitive discriminant `-4f²`. The script
  computes `f` exactly.
- `h(-4f²) = 1` exactly for `f ∈ {1, 2}`. This was checked by counting reduced forms for
  `1 ≤ f ≤ 300`. For every `2 ≤ f ≤ 300` the count also matches the order class number formula
  `h(-4f²) = (f/2) ∏_{p|f} (1 - χ₋₄(p)/p)`, which gives `h ≥ 2` for all `f ≥ 3` (standard).
  The first values are `1:1, 2:1, 3:2, 4:2, 5:2, 6:4, 7:4, 8:4, 9:6, 10:4, 11:6, 12:8`.
- Across all points of `T_n(i)` with `n ≤ 60`, the class-number-one points have conductor
  `f ∈ {1, 2}` only (94 occurrences). The idea's neighbour `21i/20 ∈ T_420(i)` has `f = 420` and
  `h = 256`.

### 3.2 Genus identities at orbit points: exact to n ≤ 4000, plus an Arb cross-check

Script: `hecke_orbit_genus.py`. Output: `hecke_orbit_genus_output.json`.

- `Z_{x²+4y²} = 2 ζ(s) L(s,χ₋₄) (1 - 2^{-s} + 2^{1-2s})` (disc -16, h = 1)
- `Z_{x²+9y²} = ζ(s) L(s,χ₋₄)(1 + 3^{1-2s}) + L(s,χ₋₃) L(s,χ₁₂)` (disc -36, h = 2)
- `Z_{x²+16y²} = ζ(s) L(s,χ₋₄)(1 - 2^{-s} + 2^{1-2s} - 2^{1-3s} + 2^{2-4s}) + L(s,χ₋₈) L(s,χ₈)` (disc -64, h = 2)

The Dirichlet coefficients of each side agree exactly for every `n ≤ 4000` (integer arithmetic).
The general identity is genus theory for the orders `Z[fi]` (classical). Each right-hand side,
evaluated with Arb, also agrees with the independent rigorous Fourier expansion of
`E*(iy, s) = π^{-s} Γ(s) y^s Z(s)/2` at `s = 0.83 + 17.31i`. The balls overlap, with agreement to
about 37 digits.

### 3.3 Certified off-line zeros: Arb, segment-certified winding

Scripts: `hecke_orbit_genus.py` and `certify_zeros.py`. Outputs: the two `*_output.json` files.
Method: `arb_winding.py`. Every boundary piece is enclosed by a ball on which the function is
certified to lie in an open half-plane. The winding interval must isolate exactly one integer.
Every box below lies inside `Re s > 1/2`, so winding 1 means a zero OFF the critical line. Trust
class: Arb ball arithmetic, not the Lean kernel. The identification of each function with the
Epstein zeta function rests on the classical genus identities in 3.2.

| Function | Box (winding 1) | Located zero | Control box (winding 0) |
|---|---|---|---|
| `Z_{x²+9y²}`, `3i ∈ T_3(i)`, h = 2 | (169/200, 177/200) × (20.627, 20.667) | 0.86509118125745098931 + 20.647342245148918387 i | (37/40, 193/200) × same |
| `Z_{x²+9y²}`, second zero | (0.789, 0.829) × (42.099, 42.139) | 0.80901668549954239703 + 42.119220595511900834 i | (0.869, 0.909) × same |
| `Z_{x²+16y²}`, `4i ∈ T_4(i)`, h = 2 | (327/500, 347/500) × (28.098, 28.138) | 0.67374145341373762739 + 28.117871677219443313 i | (367/500, 387/500) × same |
| `Z_{x²+5y²}`, `i√5`, h = 2 (not in the orbit of `i`) | (0.90, 0.96) × (15.64, 15.70) | 0.93296969748541410476 + 15.668249531278472362 i | (0.60, 0.66) × same |
| Davenport–Heilbronn `D(s)` | (0.79, 0.83) × (85.68, 85.72) | 0.80851718245663738555 + 85.699348485377592172 i | (0.60, 0.70) × same |

These are the Hecke-orbit negative control in certified form. `3i ∈ T_3(i)` and `4i ∈ T_4(i)`
lie in the Hecke orbit of `i`, which is dense in `X`. Their Eisenstein series have the same
functional equation as `E*(i, ·)`, and they carry zeros off the line. The local corrections at `2i`
and `3i` have all their zeros on the line (Lean: `euler2_disc16_zeros_on_line` and
`euler3_disc36_zeros_on_line`). So the off-line zeros at `3i` come from the genus sum of two
Euler products, not from a local factor.

### 3.4 NUMERICAL only: the idea's example `21i/20 ∈ T_420(i)`

Newton on the Fourier expansion gives a zero at `0.7759858498628036515878 + 21.66552639862992521508 i`.
This confirms the idea's `0.77599 + 21.66553i`. At the Newton midpoint, the rigorous enclosure
of `E*` (tail ball included) is `[±5.3e-42] + [±5.3e-42]i`. At the nearby point `0.70 + 21.665i`
it is about `9e-17`.

This is **not certified**. Arb's `K_ν` for a BALL of complex order `ν = s - 1/2` with
`Im ν ≈ 21.7` amplifies the input radius by roughly `e^{π|Im ν|}`, because of cancellation between
`I_{±ν}`. As a result no segment ball is ever accepted: a segment of length 1e-8 already gives an
enclosure of about 1e8. A certificate at this point needs a Bessel-free representation. The class
group of discriminant `-4·420²` has order 256 and is not 2-torsion, so genus theory alone does not
give one. The certified orbit examples in 3.3 are used instead.

### 3.5 Floating-point argument-principle scan (not a certificate)

Script: `orbit_scan.py`. Output: `orbit_scan_output.txt`. The scan covers `(0.55, 0.99) × [1, 60]`
with 400-bit Arb midpoints; each value's radius is checked to be below `1e-6` of its modulus.
Phase tracking is adaptive, starting from a 0.04 mesh.

| Point | Hecke position | h | Unit cells `[t, t+1]` with a zero in `(0.55, 0.99) × [1, 60]` |
|---|---|---|---|
| `i` | `T_1` | 1 | none |
| `2i` | `T_2(i)` | 1 | none |
| `3i` | `T_3(i)` | 2 | `t` = 20, 42, 47, 50, 53, 55 |
| `4i` | `T_4(i)` | 2 | `t` = 28, 32, 47, 53 |
| `21i/20` | `T_420(i)` | 256 | `t` = 21, 38 |

No evaluation failed the radius check.

The class-number-one points `i` and `2i` show no zero there, which is consistent with section 2,
item 4. The class-number ≥ 2 orbit points do show zeros. (An earlier version of the scan without
the 0.04 initial mesh aliased phase jumps of 2π and reported spurious cells. The mesh fixes that;
the certified results in 3.3 do not depend on the scan.)

### 3.6 Floating-point sanity checks of the kernel statements

Script: `scattering_checks.py`. Output: `scattering_checks_output.json`. mpmath, 50 digits.

- (a) `max |φ_ξ| = 0.99999996` over 400 random points with `Re s ≥ 1/2` and `|Im s| ≤ 60`, and
  `||φ_ξ| - 1| ≤ 5e-51` on the axis (`xi_inner`, `xi_unitary`).
- (b) The normalisation table in section 2 (`modScat_eq`).
- (c) The phase identity `logDeriv φ_ξ(1/2+it) = -4 Re ξ'/ξ(1+2it)` agrees to 12 digits at
  `t = 0.3, 1, 3.7, 7.05, 14, 25.5`. All values are ≤ 0 (`bk_phase_identity`, `bk_of_inner`).
- (d) `max |φ_fake| = 0.99996` over 300 random points, and `fakeXi(ρ₀) = 0`
  (`channelAxioms_fakeXi`, `fakeXi_offline_zero`).
- (e) `|c_{2}c_{3}c_{5}(1/2 + it)| = 1.6, 28.9, 1.0e3, 2.7e4, 2.7e7` at
  `t = 0.3, 0.1, 0.03, 0.01, 0.001` (`finite_euler_blowup_on_axis`).
- (f) Davenport–Heilbronn rational-face slices, `t ∈ [1, 200]`, step 0.25: `min Re Λ_DH'/Λ_DH` is
  0.103 at σ = 1.0, 0.083 at σ = 0.9 and 0.066 at σ = 0.82, with no negative value on any of these
  three lines. At σ = 0.80 it is first negative at `t = 85.75`, next to the certified DH zero
  `0.8085 + 85.699i`. So below height 200 the σ ≥ 0.82 slices, and in particular the channel's
  σ = 1 slice, do not see DH's off-line zero. The prior scan quoted in the idea went further, to
  `t ≤ 2000`, and found σ = 0.82 negative somewhere in `[240, 1864]`. The σ = 1 statement is
  consistent with it. DH is still NOT channel-admissible: a periodic Dirichlet series that is not
  of the form `P(s)L(s,χ)` has zeros with `Re s > 1` (Saias–Weingartner 2009, after
  Davenport–Heilbronn 1936), so DH fails the `edge` field at some height. Those zeros are not seen
  below height 2000.

## 4. Side finding: a rigor gap in the program's DH certificate

`telperion/src/telperion/arb_dh.py:winding_number` encloses `D` only at `4·n_per_side` nodes and
adds up quadrant advances. Its docstring calls "a returned integer a RIGOROUS zero count". Node
values in adjacent quadrants do not rule out the argument turning the long way round between the
nodes, so the claim fails without an enclosure of each boundary segment or a bound on `|D'|`.

The fix is segment enclosure (`arb_winding.py` here). It certifies the same DH zero: winding 1 on
(0.79, 0.83) × (85.68, 85.72) with 39 certified pieces, and a control box with winding 0. The
axiso_literature lane found the same gap and fixed it independently
(`telperion/research/axiso_literature/arb_winding.py`). The source file is **not** modified here.
Its consumers (`emit_winding_box_zero.py`, `examples/winding_box_zero`) should switch to a
segment-certified routine.

## 5. What is NOT established

- Anything about the zeros of zeta. RH is open; `conjecture1_proved = False`.
- The infinite form for every order-one `Λ` with the functional equation and reality. The kernel
  covers `ξ` and `ξ` times finitely many quadruples. The general case is the same argument once the
  upstream paired factorisation is generalised from `ξ` to an arbitrary order-one `Λ` (paper
  proof).
- Realizability, i.e. that every inner function is a Lax–Phillips scattering matrix
  (Sz.-Nagy–Foias). Classical, not formalised.
- The operator form of the Hecke–wave identity, the equivalence "axis regularity of `E(z,s)` iff
  `ξ(1+it) ≠ 0`" (Sarnak), and strict BK positivity (only `≥ 0` is in the kernel).
- Base-point genericity, i.e. zeros with `Re s > 1` for algebraically independent `x, y` (paper
  proof; no numerics here), and the nowhere-density and nullity of the RH locus that it implies.
- A certificate for the `21i/20` zero (section 3.4).
