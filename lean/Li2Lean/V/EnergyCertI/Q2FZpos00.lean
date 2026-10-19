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

/-- Breakpoints of cells 0..3 of piece `zpos` (q = 2). -/
def q2F_zpos_000_b : List QF := [
  (3, 5), (7, 10), (4, 5), (9, 10),
  (1, 1)]

/-- 4 cells, about 760 transcendental evaluations (field mode). -/
theorem q2F_zpos_000 :
    cellsOK (fieldUB q2D 2 vLogRF .zpos) (kzQ 2) q2F_zpos_000_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
