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

/-- Breakpoints of cells 1200..1205 of piece `x` (q = 2). -/
def q2F_x_048_b : List QF := [
  (1023751, 1024000), (4095253, 4096000), (2047751, 2048000), (8191253, 8192000),
  (4095751, 4096000), (8191751, 8192000), (1, 1)]

/-- 6 cells, about 558 transcendental evaluations (field mode). -/
theorem q2F_x_048 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
