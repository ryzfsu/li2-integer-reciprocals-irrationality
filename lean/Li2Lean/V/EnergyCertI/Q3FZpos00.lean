/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..1 of piece `zpos` (q = 3). -/
def q3F_zpos_000_b : List QF := [
  (3, 5), (4, 5), (1, 1)]

/-- 2 cells, about 374 transcendental evaluations (field mode). -/
theorem q3F_zpos_000 :
    cellsOK (fieldUB q3D 3 vLogRF .zpos) (kzQ 3) q3F_zpos_000_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
