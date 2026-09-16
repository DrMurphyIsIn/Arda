/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Aggregator for the four RHLinalg linear-algebra modules needed by Route P Brick D4
(the diffraction/inertia bridge, `RvMRoutePInertia`).  These are the positive-index /
Sylvester-inertia prelude of §3 of arXiv:2608.13637, source-ported verbatim from the
v4.32.0 `hermitian_moment` island (namespace `RHLinalg`).  Only the four modules on the
`Inertia` import path are ported (PosIndex → HermitianPosPart → Sylvester → Inertia);
RankTrace / VonNeumann / Weyl are not needed here.  conjecture1_proved = False.
-/
import RHLinalg.PosIndex
import RHLinalg.HermitianPosPart
import RHLinalg.Sylvester
import RHLinalg.Inertia
