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

/-- Breakpoints of cells 702..714 of piece `zneg` (q = 5). -/
def q5F_zneg_054_b : List QF := [
  (-6167, 2560), (-1539, 640), (-1229, 512), (-3067, 1280),
  (-6123, 2560), (-191, 80), (-6101, 2560), (-609, 256),
  (-6079, 2560), (-1517, 640), (-6057, 2560), (-3023, 1280),
  (-1207, 512), (-753, 320)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_054 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 715..727 of piece `zneg` (q = 5). -/
def q5F_zneg_055_b : List QF := [
  (-753, 320), (-6013, 2560), (-3001, 1280), (-5991, 2560),
  (-299, 128), (-5969, 2560), (-2979, 1280), (-5947, 2560),
  (-371, 160), (-1185, 512), (-2957, 1280), (-5903, 2560),
  (-1473, 640), (-5881, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_055 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_055_b = true := by
  decide +kernel

/-- Breakpoints of cells 728..740 of piece `zneg` (q = 5). -/
def q5F_zneg_056_b : List QF := [
  (-5881, 2560), (-587, 256), (-5859, 2560), (-731, 320),
  (-5837, 2560), (-2913, 1280), (-1163, 512), (-1451, 640),
  (-5793, 2560), (-2891, 1280), (-5771, 2560), (-9, 4),
  (-5749, 2560), (-2869, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_056 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 741..753 of piece `zneg` (q = 5). -/
def q5F_zneg_057_b : List QF := [
  (-2869, 1280), (-5727, 2560), (-1429, 640), (-1141, 512),
  (-2847, 1280), (-5683, 2560), (-709, 320), (-5661, 2560),
  (-565, 256), (-5639, 2560), (-1407, 640), (-5617, 2560),
  (-2803, 1280), (-1119, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_057 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 754..766 of piece `zneg` (q = 5). -/
def q5F_zneg_058_b : List QF := [
  (-1119, 512), (-349, 160), (-5573, 2560), (-2781, 1280),
  (-5551, 2560), (-277, 128), (-5529, 2560), (-2759, 1280),
  (-5507, 2560), (-687, 320), (-1097, 512), (-2737, 1280),
  (-5463, 2560), (-1363, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_058 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 767..779 of piece `zneg` (q = 5). -/
def q5F_zneg_059_b : List QF := [
  (-1363, 640), (-5441, 2560), (-543, 256), (-5419, 2560),
  (-169, 80), (-5397, 2560), (-2693, 1280), (-1075, 512),
  (-1341, 640), (-5353, 2560), (-2671, 1280), (-5331, 2560),
  (-133, 64), (-5309, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_059 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_059_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
