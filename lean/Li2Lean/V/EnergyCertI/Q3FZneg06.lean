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

/-- Breakpoints of cells 504..515 of piece `zneg` (q = 3). -/
def q3F_zneg_042_b : List QF := [
  (-27, 16), (-1077, 640), (-537, 320), (-1071, 640),
  (-267, 160), (-213, 128), (-531, 320), (-1059, 640),
  (-33, 20), (-1053, 640), (-105, 64), (-1047, 640),
  (-261, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_042 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 516..527 of piece `zneg` (q = 3). -/
def q3F_zneg_043_b : List QF := [
  (-261, 160), (-1041, 640), (-519, 320), (-207, 128),
  (-129, 80), (-1029, 640), (-513, 320), (-1023, 640),
  (-51, 32), (-1017, 640), (-507, 320), (-1011, 640),
  (-63, 40)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_043 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 528..539 of piece `zneg` (q = 3). -/
def q3F_zneg_044_b : List QF := [
  (-63, 40), (-201, 128), (-501, 320), (-999, 640),
  (-249, 160), (-993, 640), (-99, 64), (-987, 640),
  (-123, 80), (-981, 640), (-489, 320), (-195, 128),
  (-243, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_044 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 540..551 of piece `zneg` (q = 3). -/
def q3F_zneg_045_b : List QF := [
  (-243, 160), (-969, 640), (-483, 320), (-963, 640),
  (-3, 2), (-957, 640), (-477, 320), (-951, 640),
  (-237, 160), (-189, 128), (-471, 320), (-939, 640),
  (-117, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_045 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 552..563 of piece `zneg` (q = 3). -/
def q3F_zneg_046_b : List QF := [
  (-117, 80), (-933, 640), (-93, 64), (-927, 640),
  (-231, 160), (-921, 640), (-459, 320), (-183, 128),
  (-57, 40), (-909, 640), (-453, 320), (-903, 640),
  (-45, 32)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_046 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 564..575 of piece `zneg` (q = 3). -/
def q3F_zneg_047_b : List QF := [
  (-45, 32), (-897, 640), (-447, 320), (-891, 640),
  (-111, 80), (-177, 128), (-441, 320), (-879, 640),
  (-219, 160), (-873, 640), (-87, 64), (-867, 640),
  (-27, 20)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_047 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_047_b = true := by
  decide +kernel

/-- Breakpoints of cells 576..587 of piece `zneg` (q = 3). -/
def q3F_zneg_048_b : List QF := [
  (-27, 20), (-861, 640), (-429, 320), (-171, 128),
  (-213, 160), (-849, 640), (-423, 320), (-843, 640),
  (-21, 16), (-837, 640), (-417, 320), (-831, 640),
  (-207, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_048 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
