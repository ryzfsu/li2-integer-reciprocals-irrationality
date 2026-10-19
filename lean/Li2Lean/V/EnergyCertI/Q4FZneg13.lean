/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 1092..1100 of piece `zneg` (q = 4). -/
def q4F_zneg_091_b : List QF := [
  (-645, 1024), (-401, 640), (-3191, 5120), (-1587, 2560),
  (-3157, 5120), (-157, 256), (-3123, 5120), (-1553, 2560),
  (-3089, 5120), (-3, 5)]

/-- 9 cells, about 1674 transcendental evaluations (field mode). -/
theorem q4F_zneg_091 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_091_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
