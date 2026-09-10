/- telperion 0.1.6 | family BGP | input-hash 574b76dbbb6bc73f
   2 theorems, 14 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/


namespace BGP212

-- Admissible k-tuple checker (self-contained, core Lean only).  A set
-- H = {h1 < ... < hk} is ADMISSIBLE iff for every prime p the residues
-- {hi mod p} omit at least one class mod p.  KEY FINITENESS FACT: only
-- primes p <= k need checking -- for p > k, k residues cannot cover all
-- p classes (pigeonhole), so admissibility is a FINITE decidable check.
-- The generator supplies the exact prime list p <= k (re-verified in
-- Python).  Int `%` (Int.emod) yields a residue in [0, p) for positive
-- p, matching the residue convention.  The DHL[k,2] + diameter => H1<=d
-- sieve implication (bgp212 Lemma 12.1 shape) is the CITED theorem, NOT
-- emitted here.  conjecture1_proved = False.
def coversAllResidues (p : Nat) (H : List Int) : Bool :=
  (List.range p).all (fun r => H.any (fun h => h % (p : Int) == (r : Int)))

def admissibleCheck (ps : List Nat) (H : List Int) : Bool :=
  ps.all (fun p => !(coversAllResidues p H))

-- Inline fold-based diameter endpoints (core-only; no List.maximum?).
def tupleMax (H : List Int) : Int :=
  H.foldl (fun a b => if a < b then b else a) (H.headD 0)

def tupleMin (H : List Int) : Int :=
  H.foldl (fun a b => if b < a then b else a) (H.headD 0)

-- H45_bgp212: admissible 45-tuple, diameter 212, checked over primes p <= 45 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] (exact-evaluated pre-emission; kernel decide is the final gate).
def tupleH_H45_bgp212 : List Int := [0, 2, 12, 14, 24, 26, 30, 36, 44, 50, 54, 56, 60, 66, 72, 74, 80, 84, 92, 96, 102, 110, 114, 116, 122, 126, 134, 140, 144, 150, 156, 162, 164, 170, 176, 180, 182, 186, 192, 194, 200, 204, 206, 210, 212]

set_option maxRecDepth 100000 in
theorem H45_bgp212_admissible : admissibleCheck [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] tupleH_H45_bgp212 = true := by decide

set_option maxRecDepth 100000 in
theorem H45_bgp212_diameter : tupleMax tupleH_H45_bgp212 - tupleMin tupleH_H45_bgp212 = 212 := by decide

end BGP212