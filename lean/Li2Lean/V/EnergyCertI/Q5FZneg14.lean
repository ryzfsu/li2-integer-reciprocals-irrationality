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

/-- Breakpoints of cells 1092..1104 of piece `zneg` (q = 5). -/
def q5F_zneg_084_b : List QF := [
  (-1877, 2560), (-933, 1280), (-371, 512), (-461, 640),
  (-1833, 2560), (-911, 1280), (-1811, 2560), (-45, 64),
  (-1789, 2560), (-889, 1280), (-1767, 2560), (-439, 640),
  (-349, 512), (-867, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_084 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_084_b = true := by
  decide +kernel

/-- Breakpoints of cells 1105..1117 of piece `zneg` (q = 5). -/
def q5F_zneg_085_b : List QF := [
  (-867, 1280), (-1723, 2560), (-107, 160), (-1701, 2560),
  (-169, 256), (-1679, 2560), (-417, 640), (-1657, 2560),
  (-823, 1280), (-327, 512), (-203, 320), (-1613, 2560),
  (-801, 1280), (-1591, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_085 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_085_b = true := by
  decide +kernel

/-- Breakpoints of cells 1118..1122 of piece `zneg` (q = 5). -/
def q5F_zneg_086_b : List QF := [
  (-1591, 2560), (-79, 128), (-1569, 2560), (-779, 1280),
  (-1547, 2560), (-3, 5)]

/-- 5 cells, about 920 transcendental evaluations (field mode). -/
theorem q5F_zneg_086 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_086_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
