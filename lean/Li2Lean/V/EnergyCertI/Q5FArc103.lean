/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 126..130 of piece `arc1` (q = 5). -/
def q5F_arc1_021_b : List QF := [
  (123, 128), (31, 32), (125, 128), (63, 64),
  (127, 128), (1, 1)]

/-- 5 cells, about 1805 transcendental evaluations (field mode). -/
theorem q5F_arc1_021 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_021_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
