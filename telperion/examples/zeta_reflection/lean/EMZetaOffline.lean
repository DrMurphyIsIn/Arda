/-  EMZetaOffline.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 "off-line evaluator", EM route): the headline theorems of the OFF-LINE kernel evaluator
    of ζ, in one place.

    THE PIECES (every theorem below is proved in the named module; axioms
    [propext, Classical.choice, Quot.sound], checked by AxiomGuardEMZetaOffline):

      * EMZetaOfflineCore      -- the order-m Euler-Maclaurin identity CONTINUED to `Re s > 1 - m`
                                  (`em_zeta_order_ext`), and the general-K remainder bounds for
                                  `σ > 1 - 2K` / `σ > -2K`;
      * EMZetaOfflineEval      -- the Nat-only evaluator at `σ = (a - b)/q` (validated Newton root for
                                  `m^(-σ)`), `p + 1` accumulators of `Σ (log m)^k m^(-s)`;
      * EMZetaOfflineSound     -- its soundness (`offline_evaluator_sound` below);
      * EMZetaOfflineCheck     -- the exact correction factor and odd-saw remainder at general σ and
                                  the kernel checker `checkG` (`offline_enclosure_sound` below);
      * EMZetaOfflineI_*       -- three certified enclosures OFF the critical line;
      * EMZetaOfflineSlab, …SlabCheck, …SlabClear -- the Taylor model of the EM finite part, the
                                  kernel cell checker, reflection, and the packaged zero-free cell;
      * EMZetaOfflineSlab_T1000, …SlabBand -- the hypothesis-free slab `SlabClear 1000 (1000 + 5773/100000)`,
                                  = the top-edge clearance input of band 24 of the `[1, 1000]` segment.

    MEASURED KERNEL COST (Lean profiler "type checking", this machine, t ≈ 1000, P = 64):
      σ = 3/10, N = 800: 0.27 s;  σ = 6/5, N = 600: 0.18 s;  σ = -1, N = 1000: 0.26 s per evaluation
      (0.26-0.33 ms per Dirichlet term, 8-10 ms for the checker); a slab cell (N = 300, 6 accumulators):
      0.17 s + 12 ms check; the whole slab (3 cells) about 0.55 s of kernel time.

    conjecture1_proved = False.  Finite interval arithmetic at finitely many points and one finite
    zero-free slab; nothing here bears on the Riemann Hypothesis.
-/
import EMZetaOfflineCore
import EMZetaOfflineSound
import EMZetaOfflineCheck
import EMZetaOfflineI_S03_T1000
import EMZetaOfflineI_S12_T1000
import EMZetaOfflineI_SM1_T9995
import EMZetaOfflineSlabClear
import EMZetaOfflineSlab_T1000
import EMZetaOfflineSlabBand

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat

namespace ArbEcon.Off.Headline

/-- **The continuation** (O4): the order-`m` Euler-Maclaurin identity holds on `Re s > 1 - m`. -/
theorem em_zeta_order_offline (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 1 - (m : ℝ) < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = emFiniteM m s N + (-1) ^ (m - 1) * emTail s N m / (m ! : ℂ) :=
  EMOff.em_zeta_order_ext m hm hs hs1 hN

/-- **The general-σ evaluator is sound**: at `s = σ + i t` (`σ = (a - b)/q` rational of any sign,
    `t = tn/2^tq`), a kernel-checked chunk `StO.beq (runO c o L s) s' = true` carries the invariant
    `InvO` (log bracket plus the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`) from `n` to
    `n + L` terms; the initial state satisfies it after `n = 1`. -/
theorem offline_evaluator_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K)
    (ho : OValid c o σ) (L n : ℕ) (s s' : StO) (hI : InvO c σ t n s)
    (hchk : StO.beq (runO c o L s) s' = true) : InvO c σ t (n + L) s' :=
  chunkO_sound c o σ t K hv ho L n s s' hI hchk

theorem offline_evaluator_init (c : Cfg) (σ t : ℝ) (p : ℕ) (hone : c.one = 2 ^ c.P) :
    InvO c σ t 1 (StO.init c p) :=
  initO_sound c σ t p hone

/-- **The off-line enclosure checker is sound** (order-(2K+1) EM with the odd-saw remainder, valid
    for `σ > -2K`): `checkG … = true` gives `lo/D ≤ Re ζ(σ + i t) ≤ hi/D` and the same for `Im`. -/
theorem offline_enclosure_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (x1 x2 : Acc)
    (h1 : AccOK c.P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK c.P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (hc : checkG c o K N x1 x2 D reLo reHi imLo imHi Qp Rn Rd = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) :=
  checkG_sound c o σ t hσ ht K N x1 x2 h1 h2 D reLo reHi imLo imHi Qp Rn Rd hc

/-- **ζ(0.3 + 1000 i)**, kernel-checked, no hypotheses. -/
theorem zeta_03_1000 :
    ((-92072451 / 100000000 : ℝ) ≤ (riemannZeta ((3 / 10 : ℂ) + (1000 : ℂ) * Complex.I)).re ∧
      (riemannZeta ((3 / 10 : ℂ) + (1000 : ℂ) * Complex.I)).re ≤ (-92072448 / 100000000 : ℝ)) ∧
    ((221154813 / 100000000 : ℝ) ≤ (riemannZeta ((3 / 10 : ℂ) + (1000 : ℂ) * Complex.I)).im ∧
      (riemannZeta ((3 / 10 : ℂ) + (1000 : ℂ) * Complex.I)).im ≤ (221154817 / 100000000 : ℝ)) :=
  ArbEcon.Off.I_S03_T1000.zeta_re_im

/-- **ζ(1.2 + 1000 i)**, kernel-checked, no hypotheses. -/
theorem zeta_12_1000 :
    ((956459664 / 1000000000 : ℝ) ≤ (riemannZeta ((6 / 5 : ℂ) + (1000 : ℂ) * Complex.I)).re ∧
      (riemannZeta ((6 / 5 : ℂ) + (1000 : ℂ) * Complex.I)).re ≤ (956459668 / 1000000000 : ℝ)) ∧
    ((-41708669 / 1000000000 : ℝ) ≤ (riemannZeta ((6 / 5 : ℂ) + (1000 : ℂ) * Complex.I)).im ∧
      (riemannZeta ((6 / 5 : ℂ) + (1000 : ℂ) * Complex.I)).im ≤ (-41708665 / 1000000000 : ℝ)) :=
  ArbEcon.Off.I_S12_T1000.zeta_re_im

/-- **ζ(-1 + 999.5 i)**, kernel-checked, no hypotheses (needs the continuation to `Re s ≤ 0`). -/
theorem zeta_m1_9995 :
    ((69122182 / 100000 : ℝ) ≤ (riemannZeta ((-1 : ℂ) + (1999 / 2 : ℂ) * Complex.I)).re ∧
      (riemannZeta ((-1 : ℂ) + (1999 / 2 : ℂ) * Complex.I)).re ≤ (69122185 / 100000 : ℝ)) ∧
    ((-181643135 / 100000 : ℝ) ≤ (riemannZeta ((-1 : ℂ) + (1999 / 2 : ℂ) * Complex.I)).im ∧
      (riemannZeta ((-1 : ℂ) + (1999 / 2 : ℂ) * Complex.I)).im ≤ (-181643132 / 100000 : ℝ)) :=
  ArbEcon.Off.I_SM1_T9995.zeta_re_im

/-- **A real edge-clearance slab, hypothesis-free**: no zero of ζ with `0 < Re s < 1` and
    `1000 ≤ Im s ≤ 1000 + 5773/100000`. -/
theorem slabClear_1000 : EdgeClearGlue.SlabClear 1000 (1000 + 5773 / 100000) :=
  ArbEcon.Off.Slab_T1000.slabClear

/-- The same slab as the band-24 top-edge input of the `[1, 1000]` segment (`BandGlue_h1000`). -/
theorem band24_top_slabClear :
    EdgeClearGlue.SlabClear (BandGlue_h1000.seg 24).T1
      ((BandGlue_h1000.seg 24).T1 + BandGlue_h1000.capHi 24) :=
  ArbEcon.Off.Slab_T1000.band24_top_slabClear

end ArbEcon.Off.Headline
