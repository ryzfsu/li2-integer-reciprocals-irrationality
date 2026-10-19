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

/-- Breakpoints of cells 588..599 of piece `zneg` (q = 2). -/
def q2F_zneg_049_b : List QF := [
  (-901, 1280), (-359, 512), (-447, 640), (-1781, 2560),
  (-887, 1280), (-1767, 2560), (-11, 16), (-1753, 2560),
  (-873, 1280), (-1739, 2560), (-433, 640), (-345, 512),
  (-859, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_049 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 600..611 of piece `zneg` (q = 2). -/
def q2F_zneg_050_b : List QF := [
  (-859, 1280), (-1711, 2560), (-213, 320), (-1697, 2560),
  (-169, 256), (-1683, 2560), (-419, 640), (-1669, 2560),
  (-831, 1280), (-331, 512), (-103, 160), (-1641, 2560),
  (-817, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_050 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 612..623 of piece `zneg` (q = 2). -/
def q2F_zneg_051_b : List QF := [
  (-817, 1280), (-1627, 2560), (-81, 128), (-1613, 2560),
  (-803, 1280), (-1599, 2560), (-199, 320), (-317, 512),
  (-789, 1280), (-1571, 2560), (-391, 640), (-1557, 2560),
  (-155, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_051 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 624..625 of piece `zneg` (q = 2). -/
def q2F_zneg_052_b : List QF := [
  (-155, 256), (-1543, 2560), (-3, 5)]

/-- 2 cells, about 380 transcendental evaluations (field mode). -/
theorem q2F_zneg_052 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_052_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
