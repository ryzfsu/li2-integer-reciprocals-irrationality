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

/-- Breakpoints of cells 168..173 of piece `arc1` (q = 2). -/
def q2F_arc1_028_b : List QF := [
  (239, 256), (15, 16), (241, 256), (121, 128),
  (243, 256), (61, 64), (245, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_028 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 174..179 of piece `arc1` (q = 2). -/
def q2F_arc1_029_b : List QF := [
  (245, 256), (123, 128), (247, 256), (31, 32),
  (249, 256), (125, 128), (251, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_029 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..184 of piece `arc1` (q = 2). -/
def q2F_arc1_030_b : List QF := [
  (251, 256), (63, 64), (253, 256), (127, 128),
  (255, 256), (1, 1)]

/-- 5 cells, about 1865 transcendental evaluations (field mode). -/
theorem q2F_arc1_030 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_030_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
