/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 1170..1182 of piece `zneg` (q = 7). -/
def q7F_zneg_090_b : List QF := [
  (-213, 320), (-53, 80), (-211, 320), (-21, 32),
  (-209, 320), (-13, 20), (-207, 320), (-103, 160),
  (-41, 64), (-51, 80), (-203, 320), (-101, 160),
  (-201, 320), (-5, 8)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_090 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_090_b = true := by
  decide +kernel

/-- Breakpoints of cells 1183..1190 of piece `zneg` (q = 7). -/
def q7F_zneg_091_b : List QF := [
  (-5, 8), (-199, 320), (-99, 160), (-197, 320),
  (-49, 80), (-39, 64), (-97, 160), (-193, 320),
  (-3, 5)]

/-- 8 cells, about 1440 transcendental evaluations (field mode). -/
theorem q7F_zneg_091 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_091_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
