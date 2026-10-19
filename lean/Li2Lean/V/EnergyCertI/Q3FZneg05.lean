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

/-- Breakpoints of cells 420..431 of piece `zneg` (q = 3). -/
def q3F_zneg_035_b : List QF := [
  (-333, 160), (-1329, 640), (-663, 320), (-1323, 640),
  (-33, 16), (-1317, 640), (-657, 320), (-1311, 640),
  (-327, 160), (-261, 128), (-651, 320), (-1299, 640),
  (-81, 40)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_035 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 432..443 of piece `zneg` (q = 3). -/
def q3F_zneg_036_b : List QF := [
  (-81, 40), (-1293, 640), (-129, 64), (-1287, 640),
  (-321, 160), (-1281, 640), (-639, 320), (-255, 128),
  (-159, 80), (-1269, 640), (-633, 320), (-1263, 640),
  (-63, 32)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_036 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 444..455 of piece `zneg` (q = 3). -/
def q3F_zneg_037_b : List QF := [
  (-63, 32), (-1257, 640), (-627, 320), (-1251, 640),
  (-39, 20), (-249, 128), (-621, 320), (-1239, 640),
  (-309, 160), (-1233, 640), (-123, 64), (-1227, 640),
  (-153, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_037 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 456..467 of piece `zneg` (q = 3). -/
def q3F_zneg_038_b : List QF := [
  (-153, 80), (-1221, 640), (-609, 320), (-243, 128),
  (-303, 160), (-1209, 640), (-603, 320), (-1203, 640),
  (-15, 8), (-1197, 640), (-597, 320), (-1191, 640),
  (-297, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_038 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 468..479 of piece `zneg` (q = 3). -/
def q3F_zneg_039_b : List QF := [
  (-297, 160), (-237, 128), (-591, 320), (-1179, 640),
  (-147, 80), (-1173, 640), (-117, 64), (-1167, 640),
  (-291, 160), (-1161, 640), (-579, 320), (-231, 128),
  (-9, 5)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_039 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 480..491 of piece `zneg` (q = 3). -/
def q3F_zneg_040_b : List QF := [
  (-9, 5), (-1149, 640), (-573, 320), (-1143, 640),
  (-57, 32), (-1137, 640), (-567, 320), (-1131, 640),
  (-141, 80), (-225, 128), (-561, 320), (-1119, 640),
  (-279, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_040 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 492..503 of piece `zneg` (q = 3). -/
def q3F_zneg_041_b : List QF := [
  (-279, 160), (-1113, 640), (-111, 64), (-1107, 640),
  (-69, 40), (-1101, 640), (-549, 320), (-219, 128),
  (-273, 160), (-1089, 640), (-543, 320), (-1083, 640),
  (-27, 16)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_041 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
