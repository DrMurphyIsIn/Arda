/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
RHLinalg aggregator — the §3 linear-algebra prelude of arXiv:2608.13637 (Alpöge–Furman),
namespace `RHLinalg`. Source-ported VERBATIM from the sibling v4.32.0 `hermitian_moment`
island (`telperion/examples/hermitian_moment/lean/RHLinalg/`), which itself is the verbatim
port of `anthropics/formal-math` path `zeta23/Zeta23/LinAlg/` at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (Apache-2.0). Same Lean/Mathlib pin
(leanprover/lean4:v4.32.0, mathlib rev v4.32.0) — no version drift, the copy is byte-identical.

Only the four modules the DefectDictionary consumes are ported here: PosIndex (posIndex /
negIndex / posIndexAbove / rtrace / frobSq), HermitianPosPart, Sylvester
(finrank_le_posIndex_of_posDefOn, hermForm, PosDefOn), Inertia (posIndex_conj_le = lem:inertia,
posIndex_add_le). The RankTrace / VonNeumann / Weyl modules are not needed by the dictionary and
are omitted. conjecture1_proved = False.
-/
import RHLinalg.PosIndex
import RHLinalg.HermitianPosPart
import RHLinalg.Sylvester
import RHLinalg.Inertia
