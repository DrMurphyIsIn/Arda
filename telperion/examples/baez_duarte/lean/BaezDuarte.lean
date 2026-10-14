/- telperion 0.1.6 | family BaezDuarte | input-hash b87f2efd512bda8c
   6 theorems, 6 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BaezDuarte

-- bd_neg_refutes: the falsifiability face.  Generic in P, dN2, L, eps: a
-- certified LOWER bound L ≤ dN2 with eps ≤ L contradicts hRH : P → dN2 < eps.
-- Intended instance: P = RH and dN2 = the Báez-Duarte / Bagchi d²_N of THIS
-- file (g_k = {1/(kx)} − {1/x}/k, k ≥ 2, in L²(0,1)), where RH ⟹ d²_N → 0 is
-- a theorem (Báez-Duarte 2003; Bagchi 2006, Thm 2 / Thm 7); hRH at fixed N needs N
-- past an inexplicit N₀(eps), so it is an external hypothesis.  Do NOT use the
-- pre-2026-10-14 family {1/(kx)} without the −{1/x}/k term: its d²_N is
-- ≥ 1/2 − (ln 2)² ≈ 0.019547 for every N, so hRH is false for eps ≤ 0.01954.
-- Not expected to fire; makes the sequence falsifiable.
theorem bd_neg_refutes {P : Prop} (dN2 L eps : ℝ)
    (hRH : P → dN2 < eps) (hLo : L ≤ dN2) (hbad : eps ≤ L) : ¬P :=
  fun hP => absurd (hRH hP) (not_lt.mpr (le_trans hbad hLo))

-- bd_N2: Báez-Duarte rung N=2 — d²_N ≤ 306852819447/1000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=2.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N2 (dN2 : ℝ) (hval : dN2 ≤ ((104416603697551955386467185954184854095 / 340282366920938463463374607431768211456) : ℝ)) : dN2 ≤ ((306852819447 / 1000000000000) : ℝ) :=
  le_trans hval (by norm_num)

-- bd_N3: Báez-Duarte rung N=3 — d²_N ≤ 957477839437/10000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=25342123/21907823, c_3=3909695/2844439.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N3 (dN2 : ℝ) (hval : dN2 ≤ ((32581282547771005811770524566122408227 / 340282366920938463463374607431768211456) : ℝ)) : dN2 ≤ ((957477839437 / 10000000000000) : ℝ) :=
  le_trans hval (by norm_num)

-- bd_N4: Báez-Duarte rung N=4 — d²_N ≤ 329758471231/5000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=26818141/31055408, c_3=98458465/92782516, c_4=3271669/4606334.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N4 (dN2 : ℝ) (hval : dN2 ≤ ((22442198620519439488459306399494758975 / 340282366920938463463374607431768211456) : ℝ)) : dN2 ≤ ((329758471231 / 5000000000000) : ℝ) :=
  le_trans hval (by norm_num)

-- bd_N5: Báez-Duarte rung N=5 — d²_N ≤ 181595090343/5000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=49039331/56792348, c_3=80840245/93154498, c_4=27622042/92675263, c_5=19871120/26286597.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N5 (dN2 : ℝ) (hval : dN2 ≤ ((12358721432619032332123258234782891697 / 340282366920938463463374607431768211456) : ℝ)) : dN2 ≤ ((181595090343 / 5000000000000) : ℝ) :=
  le_trans hval (by norm_num)

-- bd_N6: Báez-Duarte rung N=6 — d²_N ≤ 362080347681/10000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=49521001/57097290, c_3=64755984/73209283, c_4=26714755/87837628, c_5=61190701/78336520, c_6=-360582/6133885.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N6 (dN2 : ℝ) (hval : dN2 ≤ ((12320955772437730932024545741797685617 / 340282366920938463463374607431768211456) : ℝ)) : dN2 ≤ ((362080347681 / 10000000000000) : ℝ) :=
  le_trans hval (by norm_num)

-- bd_N7: Báez-Duarte rung N=7 — d²_N ≤ 121941843667/5000000000000.
-- d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)}, g_k(x) = {1/(kx)} − {1/x}/k
-- (RH ⟺ d²_N → 0: Báez-Duarte 2003; Bagchi 2006, Thm 2, in L²(0,1) as Thm 7).
-- Witnessing coefficient vector: c_2=81289225/90927768, c_3=70139742/78212591, c_4=3427723/17501491, c_5=18225184/26968917, c_6=-16651485/41658562, c_7=41437131/67232510.  Its form value
-- Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is certified ≤ Uexact
-- (the trust seam, hypothesis hval).
-- Kernel proves d²_N ≤ Uexact ≤ U (norm_num).  A finite spectral rung; NOT RH.
theorem bd_N7 (dN2 : ℝ) (hval : dN2 ≤ ((4149465918955040022088048550354818853 / 170141183460469231731687303715884105728) : ℝ)) : dN2 ≤ ((121941843667 / 5000000000000) : ℝ) :=
  le_trans hval (by norm_num)

end BaezDuarte
