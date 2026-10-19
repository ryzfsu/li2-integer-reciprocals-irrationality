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

/-- Breakpoints of cells 546..558 of piece `zneg` (q = 5). -/
def q5F_zneg_042_b : List QF := [
  (-7883, 2560), (-123, 40), (-7861, 2560), (-785, 256),
  (-7839, 2560), (-1957, 640), (-7817, 2560), (-3903, 1280),
  (-1559, 512), (-973, 320), (-7773, 2560), (-3881, 1280),
  (-7751, 2560), (-387, 128)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_042 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 559..571 of piece `zneg` (q = 5). -/
def q5F_zneg_043_b : List QF := [
  (-387, 128), (-7729, 2560), (-3859, 1280), (-7707, 2560),
  (-481, 160), (-1537, 512), (-3837, 1280), (-7663, 2560),
  (-1913, 640), (-7641, 2560), (-763, 256), (-7619, 2560),
  (-951, 320), (-7597, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_043 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 572..584 of piece `zneg` (q = 5). -/
def q5F_zneg_044_b : List QF := [
  (-7597, 2560), (-3793, 1280), (-1515, 512), (-1891, 640),
  (-7553, 2560), (-3771, 1280), (-7531, 2560), (-47, 16),
  (-7509, 2560), (-3749, 1280), (-7487, 2560), (-1869, 640),
  (-1493, 512), (-3727, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_044 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 585..597 of piece `zneg` (q = 5). -/
def q5F_zneg_045_b : List QF := [
  (-3727, 1280), (-7443, 2560), (-929, 320), (-7421, 2560),
  (-741, 256), (-7399, 2560), (-1847, 640), (-7377, 2560),
  (-3683, 1280), (-1471, 512), (-459, 160), (-7333, 2560),
  (-3661, 1280), (-7311, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_045 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 598..610 of piece `zneg` (q = 5). -/
def q5F_zneg_046_b : List QF := [
  (-7311, 2560), (-365, 128), (-7289, 2560), (-3639, 1280),
  (-7267, 2560), (-907, 320), (-1449, 512), (-3617, 1280),
  (-7223, 2560), (-1803, 640), (-7201, 2560), (-719, 256),
  (-7179, 2560), (-14, 5)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_046 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 611..623 of piece `zneg` (q = 5). -/
def q5F_zneg_047_b : List QF := [
  (-14, 5), (-7157, 2560), (-3573, 1280), (-1427, 512),
  (-1781, 640), (-7113, 2560), (-3551, 1280), (-7091, 2560),
  (-177, 64), (-7069, 2560), (-3529, 1280), (-7047, 2560),
  (-1759, 640), (-1405, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_047 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_047_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
