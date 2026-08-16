# R5/R6 layer — design (2026-08-15, surveyed at gate)

Ground truth: `gap_discharges.py` G5/G6 (four shedding lemmas L1-L4, symbolic
shared-Sigma endpoints, thresholds K >= 25/40; n0 = 421; finite table below),
`distribution.py`/`hub.py`, ExactCruxes' green tie crux `(26/23)^11 < 621/64`,
and the reviewed G1 rational-kernel design for the amortized layer.

## Porting analysis

* The shedding lemmas are sympy `check_neg` certificates after a `K = K0 + t`
  shift — EXACTLY the P4 pipeline shape (nonneg-coefficient numerator over a
  positive denominator in the shift variable).  Port = extend the generator:
  extract each lemma's shifted rational function, clear, emit the Polya
  certificate + positivity.  `R47Shed.lean` (generated).
* The n < 421 finite table = a generated norm_num sweep (`R47ShedTable.lean`)
  — enumerate from the Python table, re-verify each exactly at emission.
* The single-hub END-STATE comparison (R5 residual): normal forms of the merge
  layer with >= 2 hubs would always admit an ordered merge by the strict-mirror
  dichotomy, MODULO the APPLICABILITY SEAM (named, honest): the topped-up merge
  needs `5 - cb` load-5 borrow arms; `Balanced` guarantees loads in {4,5} but
  not the count of 5s.  Options at assembly: (a) strengthen the family invariant
  (enough 5-arms per hub — check preservation under the residue), (b) a
  weakened borrow rule with its own certified table, or (c) treat under-borrowed
  states via the shedding/rebalancing layer.  DECIDE AT ASSEMBLY with a numeric
  probe of which invariant the merges actually preserve.
* The normal-form characterization + the de-loading schedule then identify the
  end state as the (canonical single-hub) template for n >= 421, finite table
  below — consumed by the R7' assembly against the near-star arithmetic theorem.

## R47ShedTable DEFERRED to assembly time (decision 2026-08-15)

The n < 421 finite table is a WINNER table ((j4, j6, c0) per (d, K) cell); porting
it wholesale = ~6000 pairwise dominance norm_num facts, most of which the assembly
will never cite.  Per the no-decorative-certificates rule (the near_star_tie lesson
from the 2026-08-09 audit): generate the per-cell winner-dominance certificates ONLY
when the R7' assembly pins which cells it consumes, in exactly the form it consumes
them.  The table's DATA + the monotone-de-loading sanity live in gap_discharges.py
(re-runnable); the Lean side waits for its consumer.

Method unchanged: survey -> exact validation -> generated Lean -> CI loop.
conjecture1_proved=False.
