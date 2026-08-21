import R3Cert.R47Tree
import R3Cert.R47RateZBound

/-!
  # R47Rate: the rate bound on the REAL Laplacian permanent ratio (leaf rooting)

  Chains the P1 capstone `pi_utree` (`Aobj = per(L)/∏deg` for every rooted tree) with
  the leaf-rooting rate bound `pi_le_rate` (`Aobj(node[K]) ≤ (4/3)ρ_B^n`) to land the
  rate directly on the actual graph invariant for a leaf rooting `node [K]`:

      `per(L(T)) / ∏deg ≤ (4/3)·ρ_B^n`     (`T = node [K]`, a leaf-rooted tree)

  This is the rate corner of `HypRatePort` on the real permanent object — not just on
  the `Ztot`-recursion `Aobj`.  By `pi_utree` the ratio is rooting-independent, so the
  arbitrary-rooting generalization is exactly graph iso-invariance of `per(L)/∏deg`,
  deferred to assembly by design (the reduction picks a leaf-rooted normal form).
  `conjecture1_proved = False`.
-/

namespace R3Cert
namespace Step3

open RTree

/-- **Rate bound on the real Laplacian permanent ratio, leaf rooting.**
    For every subtree `K`, the leaf-rooted tree `node [K]` satisfies
    `per(L(node [K])) / ∏deg ≤ (4/3)·ρ_B^(usize (node [K]))`. -/
theorem pi_rate_leafRooted (K : UTree) :
    (lapl (aGraph (realize (dtRealize (UTree.node [K]))))).permanent
        / (∏ v, ((aGraph (realize (dtRealize (UTree.node [K])))).degree v : ℝ))
      ≤ 4 / 3 * rhoB ^ usize (UTree.node [K]) := by
  rw [pi_utree]
  exact pi_le_rate K

end Step3
end R3Cert
