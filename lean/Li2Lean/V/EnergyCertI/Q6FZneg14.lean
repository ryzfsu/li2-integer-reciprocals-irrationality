/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 1092..1104 of piece `zneg` (q = 6). -/
def q6F_zneg_084_b : List QF := [
  (-273, 320), (-4341, 5120), (-2157, 2560), (-4287, 5120),
  (-213, 256), (-4233, 5120), (-2103, 2560), (-4179, 5120),
  (-519, 640), (-825, 1024), (-2049, 2560), (-4071, 5120),
  (-1011, 1280), (-4017, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_084 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_084_b = true := by
  decide +kernel

/-- Breakpoints of cells 1105..1117 of piece `zneg` (q = 6). -/
def q6F_zneg_085_b : List QF := [
  (-4017, 5120), (-399, 512), (-3963, 5120), (-123, 160),
  (-3909, 5120), (-1941, 2560), (-771, 1024), (-957, 1280),
  (-3801, 5120), (-1887, 2560), (-3747, 5120), (-93, 128),
  (-3693, 5120), (-1833, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_085 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_085_b = true := by
  decide +kernel

/-- Breakpoints of cells 1118..1130 of piece `zneg` (q = 6). -/
def q6F_zneg_086_b : List QF := [
  (-1833, 2560), (-3639, 5120), (-903, 1280), (-717, 1024),
  (-1779, 2560), (-3531, 5120), (-219, 320), (-3477, 5120),
  (-345, 512), (-3423, 5120), (-849, 1280), (-3369, 5120),
  (-1671, 2560), (-663, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_086 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_086_b = true := by
  decide +kernel

/-- Breakpoints of cells 1131..1139 of piece `zneg` (q = 6). -/
def q6F_zneg_087_b : List QF := [
  (-663, 1024), (-411, 640), (-3261, 5120), (-1617, 2560),
  (-3207, 5120), (-159, 256), (-3153, 5120), (-1563, 2560),
  (-3099, 5120), (-3, 5)]

/-- 9 cells, about 1629 transcendental evaluations (field mode). -/
theorem q6F_zneg_087 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_087_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
