/-
  ZhuParity -- the parity vocabulary for the Zhu window node (2026-09-23).

  Zhu Theorem 1.1 and the certified even-mode Legendre block cover REAL EVEN test functions.  The
  registry's `WeilWindow.WindowFloor` quantifies over ALL complex smooth compactly supported f, and
  Zhu's Lemma 6.1 / Corollary 6.3 close that gap by parity decoupling: Q(f) = Q(Re f) + Q(Im f)
  and Q(f) = Q(f_even) + Q(f_odd) for real f, with the ODD sector certified separately (its own
  Legendre block, pole sign reversed; 8.2e-15 at L = 0.8).  `OddSectorFloor L lam` names the odd
  sector's floor so the re-specified node can carry it as an explicit hypothesis instead of
  silently letting an even-mode certificate speak for complex f.  Helpers only; nothing about
  zeros; no `sorry`.  conjecture1_proved = False.
-/
import ZhuSymbol

open MeasureTheory

namespace WeilWindow
open MeasureTheory Complex WeilExplicit WeilForm

/-- The ODD-sector window floor (Zhu Section 6, eq. (14)): the Weil form of every real ODD smooth
    test function supported in `[-L, L]` is at least `lam ‖f‖₂²`.  Together with the real even
    sector this yields `WindowFloor L lam` for complex `f` (Zhu Lemma 6.1, Corollary 6.3). -/
def OddSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

/-- The real EVEN-sector window floor, the sector Zhu Theorem 1.1 certifies. -/
def EvenSectorFloor (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re

end WeilWindow

namespace RvMBridgeZhu

/-- The full window floor implies each sector's floor (the trivial direction). -/
theorem evenSectorFloor_of_windowFloor {L lam : ℝ}
    (h : ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → tsupport f ⊆ Set.Icc (-L) L →
      lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re) :
    WeilWindow.EvenSectorFloor L lam :=
  fun f hf _ _ hs => h f hf hs

theorem oddSectorFloor_of_windowFloor {L lam : ℝ}
    (h : ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → tsupport f ⊆ Set.Icc (-L) L →
      lam * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re) :
    WeilWindow.OddSectorFloor L lam :=
  fun f hf _ _ hs => h f hf hs

end RvMBridgeZhu
