/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 252..255 of piece `arc2` (q = 2). -/
def q2F_arc2_042_b : List QF := [
  (63, 64), (253, 256), (127, 128), (255, 256),
  (1, 1)]

/-- 4 cells, about 1492 transcendental evaluations (field mode). -/
theorem q2F_arc2_042 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_042_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
