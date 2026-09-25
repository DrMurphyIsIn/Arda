# LANE_NOTES_H11K -- lane H11K (worktree arda-h11k, branch cl/h11000, zeta_reflection island, Lean v4.32.0)

conjecture1_proved = False.  Finite verification up to a fixed height only.

## Plan (as adapted from the code)
- ONE Turing band [31851/4, T1] (T1 >= 11000, chosen mid-gap), reusing from Arb4_h8000: the bottom edge
  E_T31851_4 (Arb4_H8000Edges), the slab S_L31851_4 below it, and the GamD at 31851/4.
- hLine: RS5 chunks (new chunk [31851/4, 525170/64]) ++ RS5_Band_T1000 C25..C31 ++ RS5_Band_T10000 ++ new chunk [11000, T1].
- Pin: TuringBand.band_count_eq hardcodes 3.14 < pi < 3.1416, which caps a band at ~N < 700 zeros.
  A band with ~3700 zeros needs a sharp-pi variant (3.141592 < pi < 3.141593): new H11K_ glue.
- Top edge at T1: Arb4 edgeOK is one decide per edge, ~19 GB at 1e4 (Arb4 notes); split per piece.

## Log
- K (untrusted, mpmath): N(7962.75) = 7788, N(8000) = 7830, N(11000) = 11324, N(11004) = 11329; band K = 3541.
  T1 = 11004 = midpoint of the widest gap near 11000 (zeros 11003.2835 / 11004.7802).
- Environment: the seeded .lake lacked zzl_core/.lake and zero_free_bridge/.lake; reflink-copied both from
  ~/arda-arb4 (sources byte-identical).  zfb oleans are not byte-reproducible across builds, so lake rebuilt
  RSTheta (31 s; olean hash unchanged 06dc91f6) and the RS5 modules above it (RS_Bridge, RSSeam_Bridge,
  RS5_Z, RS5_Band, the needed chunks).  No Arb4 module was rebuilt.
- MEASURED top-edge cost BEFORE committing: plan_edge(11004) 1.8 s Python, 25 pieces all radius 1/16, N = 3302,
  width 0.034 rad; probe: edgeRest 2.4 s kernel, one piece 2.3 s kernel, 6.1 GB RSS.
  => whole edge ~60 s kernel.  Built: H11K_Edge_T11004 92 s wall, H11K_Slab_U11004 (3 cells, N = 3302) 39 s,
  peak 7.8 GB.
- Pins (exact Python mirror): old pins FAIL (upper slack -6.44 rad); sharp pins slack 3.68 / 4.83 rad.
- RS5 chunks (emit5h.py = lane B5 emit5.py over a dyadic tn range): [509616/64, 525170/64] 278 samples,
  277 changes; [704000/64, 704256/64] 6 samples, 5 changes; both sharp vs mpmath, no sample dropped.
  277 + 2077 (B5 C25..C31) + 1182 (B5 T10000) + 5 = 3541.
- Line build (11 RS5 chunk modules rebuilt in parallel by one lake build): 75 s wall.  NOTE: lake ran them
  concurrently (~7.4 GB each); build RS5 chunk sets in smaller batches next time.
- Capstone H11K_h11000 built (35 s).  H11K_AxiomGuard built: 64 `#print axioms`, 28 x the three,
  1 x [propext, Quot.sound], 31 x [propext], 4 none; 5 kernel negative controls rejected (old pins,
  n = 3542, n = 3540, too-small ball, top edge Lo shifted by 1/10).
- Forbidden-token scan: only docstring phrase "No `sorry`".  No emoji.  lakefile: +37 lines, 0 removed.

## Result
`H11K_h11000.all_nontrivial_zeros_up_to_height_11000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im →
ρ.im ≤ 11000 → ρ.re = 1 / 2`, hypothesis-free, axioms [propext, Classical.choice, Quot.sound]
(also `..._11004`).  conjecture1_proved = False (finite verification only).

## Files (new)
H11K_Turing, H11K_EdgeSplit, H11K_Edge_T11004, H11K_Slab_U11004, RS5_Band_T8000Lo_C0, RS5_Band_T8000Hi_C0,
H11K_Line, H11K_h11000, H11K_AxiomGuard (+ lean_lib blocks appended).  Untrusted emitters (scratch only):
scratchpad/h11k/{plan_edge,plan_rest,emit_edge,emit_slab,emit5h,write_chunk,emit_cap}.py, cap_template.lean.

## Scaling note
The sharp-pi wide band makes each further 1000-3000 of height cost ONE new edge + ONE slab + RS5 chunks:
at T ~ 1.1e4 an edge is ~1 min kernel with per-piece decides (vs 27+ bands/segment in the Arb4 ladder).
The pin budget allows about 2 pi - 4 - (edge widths) of total enclosure slack independent of N, so band
width is limited only by pi precision (2 * 1e-6 * N rad: fine to N ~ 1e5 with the d6 bounds).
