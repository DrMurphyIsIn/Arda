/-  Spike/BenchExpD.lean -- A1 micro-benchmark: expD (Horner kernel) at 128-bit precision.

    Times ONE kernel typecheck of `TaylorKernels.hornerD` evaluating a degree-10 exp partial
    sum on a 128-bit dyadic DIntv argument, discharged by `rfl`.  Measures the kernel
    reduction cost of the transcendental hot path the reflection evaluators will run.

    Run:  time env LEAN_ABORT_ON_PANIC=1 lake env lean -Dprofiler=true Spike/BenchExpD.lean

    The coefficients are placeholder dyadic literals at exponent −128 (the benchmark measures
    kernel reduction-step cost of `mul`/`add`/`roundTo`/shift on 128-bit mantissas, NOT the
    numeric accuracy of this particular constant -- accuracy is CertVerify's job).

    conjecture1_proved = False.
-/
import TaylorKernels

open TaylorKernels DIntvProd DIntvProd.DIntv

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BenchExpD

/-- 128-bit dyadic argument `x ≈ 0.5` : mantissa `2^127`, exponent `-128`. -/
def xArg : DIntv := ⟨2 ^ 127, 2 ^ 127, -128⟩

/-- Degree-10 exp Taylor coefficients `1/k!` as 128-bit dyadic points (high degree first),
    each pinned at exponent −128 (mantissa = round(2^128 / k!)).  Placeholder magnitudes. -/
def expCoeffs : List DIntv :=
  [ ⟨(2 ^ 128) / 3628800, (2 ^ 128) / 3628800 + 1, -128⟩   -- 1/10!
  , ⟨(2 ^ 128) / 362880,  (2 ^ 128) / 362880 + 1,  -128⟩   -- 1/9!
  , ⟨(2 ^ 128) / 40320,   (2 ^ 128) / 40320 + 1,   -128⟩   -- 1/8!
  , ⟨(2 ^ 128) / 5040,    (2 ^ 128) / 5040 + 1,    -128⟩   -- 1/7!
  , ⟨(2 ^ 128) / 720,     (2 ^ 128) / 720 + 1,     -128⟩   -- 1/6!
  , ⟨(2 ^ 128) / 120,     (2 ^ 128) / 120 + 1,     -128⟩   -- 1/5!
  , ⟨(2 ^ 128) / 24,      (2 ^ 128) / 24 + 1,      -128⟩   -- 1/4!
  , ⟨(2 ^ 128) / 6,       (2 ^ 128) / 6 + 1,       -128⟩   -- 1/3!
  , ⟨(2 ^ 128) / 2,       (2 ^ 128) / 2,           -128⟩   -- 1/2!
  , ⟨2 ^ 128, 2 ^ 128, -128⟩                                -- 1/1!
  , ⟨2 ^ 128, 2 ^ 128, -128⟩ ]                              -- 1/0!

/-- The Horner evaluation of the degree-10 exp series at `xArg`, accumulator pinned at
    exponent −128, dropping 8 bits per step to cap mantissa growth.  This is the kernel-hot
    computation the benchmark times. -/
def expResult : DIntv := hornerD xArg (-128) 8 expCoeffs

/-- The BENCHMARK theorem: force the kernel to reduce the FULL Horner fold to its concrete
    128-bit dyadic endpoints by reflexivity.  Matching against explicit ~127-bit Int literals
    drives complete whnf of every `mul`/`add`/`roundTo`/shift in the fold -- so the kernel
    typecheck time of THIS `rfl` is the A1 expD-at-128-bit metric.  Concrete endpoints were
    obtained by `#eval` and pinned; a mismatch would fail `rfl`. -/
theorem bench_expD :
    expResult = ⟨2455414656975596183634424121458606886,
                 2455414656975596183634424121458606889, -128⟩ := rfl

end BenchExpD
