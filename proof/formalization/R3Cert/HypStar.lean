import R7Hyps.StarOfHubs.Cells9

/-!
  # HypStarSymbolic — the star-of-hubs domination hypothesis of the R7' assembly

  Authored from `proof/verification/assembly_composition_check.py`
  (`hypothesis_inventory`) and the family definition
  `telperion/examples/r7_starofhubs/family.py`.  The R7' capstone consumes eight
  named Props; `HypStarSymbolic` is the **depth-2 multi-hub discharge**:

  > every defected star-of-hubs stuck configuration (top-defected or subs-defected)
  > is strictly dominated by a same-`n` single-hub comparator, for **all** arm counts
  > `pT = x ≥ 0` and sub-hub sizes `q = y + 1 ≥ 1` — the per-cell claim being
  > `0 ≤ comparator_template(x,y) − star_config(x,y)`.

  The 972 witnesses are the telperion-generated, kernel-checked certificates
  `R7Hyps.StarOfHubs.star_{top,subs}_S…_cT…_cB…_…` (frozen family
  `R7StarOfHubs`, `input-hash 4700f6da…`, 120 theorems/shard × 9 shards,
  each an all-nonneg-witness rational inequality closed by `field_simp`+`positivity`).
  By wiring the frozen shards into the `R7Hyps` library they are now part of the
  verified R3Cert corpus, not a detached example.

  `hypStarSymbolic_witnesses` below discharges the hypothesis on a covering
  representative set — **both** variants (`top`, `subs`) × **all three** defect
  classes (`leaf`, `arm1`, `arm2`) at the base configuration `S2, cT0, cB0` — by
  reference to the cell theorems (so no polynomial is restated).  The complete
  family is the full `R7Hyps.StarOfHubs` namespace.  `conjecture1_proved = False`.
-/

namespace R3Cert
namespace HypStar

open R7Hyps.StarOfHubs

/-- **HypStarSymbolic (covering representative discharge).**  The star-of-hubs
    domination `0 ≤ comparator − star_config` holds across both variants and all
    three defect classes at the base configuration — discharged by the frozen
    telperion certificates.  Its inferred type is the conjunction of the six
    representative cell statements; the full 972-cell family is `R7Hyps.StarOfHubs`. -/
def hypStarSymbolic_witnesses :=
  And.intro star_top_S2_cT0_cB0_leaf_j1
   (And.intro star_top_S2_cT0_cB0_arm1_j1
    (And.intro star_top_S2_cT0_cB0_arm2_j1
     (And.intro star_subs_S2_cT0_cB0_leaf
      (And.intro star_subs_S2_cT0_cB0_arm1
        star_subs_S2_cT0_cB0_arm2))))

end HypStar
end R3Cert
