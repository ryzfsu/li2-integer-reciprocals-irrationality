/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 588..599 of piece `zneg` (q = 3). -/
def q3F_zneg_049_b : List QF := [
  (-207, 160), (-165, 128), (-411, 320), (-819, 640),
  (-51, 40), (-813, 640), (-81, 64), (-807, 640),
  (-201, 160), (-801, 640), (-399, 320), (-159, 128),
  (-99, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_049 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 600..611 of piece `zneg` (q = 3). -/
def q3F_zneg_050_b : List QF := [
  (-99, 80), (-789, 640), (-393, 320), (-783, 640),
  (-39, 32), (-777, 640), (-387, 320), (-771, 640),
  (-6, 5), (-153, 128), (-381, 320), (-759, 640),
  (-189, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_050 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 612..623 of piece `zneg` (q = 3). -/
def q3F_zneg_051_b : List QF := [
  (-189, 160), (-753, 640), (-75, 64), (-747, 640),
  (-93, 80), (-741, 640), (-369, 320), (-147, 128),
  (-183, 160), (-729, 640), (-363, 320), (-723, 640),
  (-9, 8)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_051 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 624..635 of piece `zneg` (q = 3). -/
def q3F_zneg_052_b : List QF := [
  (-9, 8), (-717, 640), (-357, 320), (-711, 640),
  (-177, 160), (-141, 128), (-351, 320), (-699, 640),
  (-87, 80), (-693, 640), (-69, 64), (-687, 640),
  (-171, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_052 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 636..647 of piece `zneg` (q = 3). -/
def q3F_zneg_053_b : List QF := [
  (-171, 160), (-681, 640), (-339, 320), (-135, 128),
  (-21, 20), (-669, 640), (-333, 320), (-663, 640),
  (-33, 32), (-657, 640), (-327, 320), (-651, 640),
  (-81, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_053 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_053_b = true := by
  decide +kernel

/-- Breakpoints of cells 648..659 of piece `zneg` (q = 3). -/
def q3F_zneg_054_b : List QF := [
  (-81, 80), (-129, 128), (-321, 320), (-639, 640),
  (-159, 160), (-633, 640), (-63, 64), (-627, 640),
  (-39, 40), (-621, 640), (-309, 320), (-123, 128),
  (-153, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_054 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 660..671 of piece `zneg` (q = 3). -/
def q3F_zneg_055_b : List QF := [
  (-153, 160), (-609, 640), (-303, 320), (-603, 640),
  (-15, 16), (-597, 640), (-297, 320), (-591, 640),
  (-147, 160), (-117, 128), (-291, 320), (-579, 640),
  (-9, 10)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_055 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_055_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
