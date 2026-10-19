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

/-- Breakpoints of cells 210..215 of piece `arc2` (q = 7). -/
def q7F_arc2_035_b : List QF := [
  (107, 128), (215, 256), (27, 32), (109, 128),
  (55, 64), (111, 128), (7, 8)]

/-- 6 cells, about 2118 transcendental evaluations (field mode). -/
theorem q7F_arc2_035 :
    cellsOK (fieldUB q7D 7 vLogRF .arc2) (kzQ 7) q7F_arc2_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 216..221 of piece `arc2` (q = 7). -/
def q7F_arc2_036_b : List QF := [
  (7, 8), (113, 128), (57, 64), (115, 128),
  (29, 32), (117, 128), (59, 64)]

/-- 6 cells, about 2118 transcendental evaluations (field mode). -/
theorem q7F_arc2_036 :
    cellsOK (fieldUB q7D 7 vLogRF .arc2) (kzQ 7) q7F_arc2_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 222..227 of piece `arc2` (q = 7). -/
def q7F_arc2_037_b : List QF := [
  (59, 64), (119, 128), (15, 16), (121, 128),
  (61, 64), (123, 128), (31, 32)]

/-- 6 cells, about 2118 transcendental evaluations (field mode). -/
theorem q7F_arc2_037 :
    cellsOK (fieldUB q7D 7 vLogRF .arc2) (kzQ 7) q7F_arc2_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 228..231 of piece `arc2` (q = 7). -/
def q7F_arc2_038_b : List QF := [
  (31, 32), (125, 128), (63, 64), (127, 128),
  (1, 1)]

/-- 4 cells, about 1412 transcendental evaluations (field mode). -/
theorem q7F_arc2_038 :
    cellsOK (fieldUB q7D 7 vLogRF .arc2) (kzQ 7) q7F_arc2_038_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
