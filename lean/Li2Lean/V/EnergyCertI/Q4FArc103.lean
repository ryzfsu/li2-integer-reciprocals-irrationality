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

/-- Breakpoints of cells 126..131 of piece `arc1` (q = 4). -/
def q4F_arc1_021_b : List QF := [
  (227, 256), (57, 64), (229, 256), (115, 128),
  (29, 32), (117, 128), (235, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_021 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..137 of piece `arc1` (q = 4). -/
def q4F_arc1_022_b : List QF := [
  (235, 256), (59, 64), (237, 256), (119, 128),
  (15, 16), (121, 128), (61, 64)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_022 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 138..143 of piece `arc1` (q = 4). -/
def q4F_arc1_023_b : List QF := [
  (61, 64), (123, 128), (31, 32), (125, 128),
  (63, 64), (127, 128), (1, 1)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_023 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
