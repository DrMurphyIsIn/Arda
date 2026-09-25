/-
  R3Cert.BGEnvCert.G40.Main -- the envelope certificate for 7 <= n <= 40 (generated).

  Every tree on n vertices, 7 <= n <= 40, either reroots to a spider or has Aobj strictly
  below the certified best spider `spiderT spTab n`.  Kernel-checked (`decide +kernel`, no
  native_decide), no sorry, standard axioms only.
-/
import R3Cert.BGEnvCert.G40.FragShared
import R3Cert.BGEnvCert.G40.Frag1
import R3Cert.BGEnvCert.G40.Frag2
import R3Cert.BGEnvCert.G40.Frag3
import R3Cert.BGEnvCert.G40.Frag4
import R3Cert.BGEnvCert.G40.Frag5
import R3Cert.BGEnvCert.G40.Frag6
import R3Cert.BGEnvCert.G40.Frag7
import R3Cert.BGEnvCert.G40.Frag8
import R3Cert.BGEnvCert.G40.Frag12
import R3Cert.BGEnvCert.G40.Frag16
import R3Cert.BGEnvCert.G40.Frag22
import R3Cert.BGEnvCert.G40.Frag38

namespace R3Cert.EnvCert.G40
open R3Cert.EnvCert R3Cert.BGSCL R3Cert.RTree R3Cert.Step3 BGMax

def caps : List CapData := [cap1, cap2, cap3, cap4, cap5, cap6, cap7, cap8, cap12, cap16, cap22, cap38]

theorem caps_ok : ∀ d ∈ caps, capCheck tanTab ldTab phiTab d = true ∧ d.C + 1 ≤ DMAX := by
  intro d hd
  simp only [caps, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cap1_ok, by decide⟩
  · exact ⟨cap2_ok, by decide⟩
  · exact ⟨cap3_ok, by decide⟩
  · exact ⟨cap4_ok, by decide⟩
  · exact ⟨cap5_ok, by decide⟩
  · exact ⟨cap6_ok, by decide⟩
  · exact ⟨cap7_ok, by decide⟩
  · exact ⟨cap8_ok, by decide⟩
  · exact ⟨cap12_ok, by decide⟩
  · exact ⟨cap16_ok, by decide⟩
  · exact ⟨cap22_ok, by decide⟩
  · exact ⟨cap38_ok, by decide⟩

set_option maxRecDepth 100000 in
theorem cover_ok : coverOK caps 7 40 = true := by decide +kernel

/-- **Finite range 7 ≤ n ≤ 40.**  Every tree either reroots to a spider or is strictly
    beaten by the certified spider of the same size. -/
theorem envcert (t : UTree) (h1 : 7 ≤ usize t) (h2 : usize t ≤ 40) :
    usize (spiderT spTab (usize t)) = usize t ∧
      ((∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧ RerootRel t (UTree.node cs)) ∨
        Aobj t < Aobj (spiderT spTab (usize t))) :=
  envcert_utree tanTab ldTab phiTab spTab spM DMAX caps 7 40 (by norm_num) tan_ok ld_ok
    caps_ok cover_ok spiders_ok t h1 h2

end R3Cert.EnvCert.G40
