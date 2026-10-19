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

/-- Breakpoints of cells 336..347 of piece `zneg` (q = 3). -/
def q3F_zneg_028_b : List QF := [
  (-3027, 1280), (-189, 80), (-3021, 1280), (-1509, 640),
  (-603, 256), (-753, 320), (-3009, 1280), (-1503, 640),
  (-3003, 1280), (-75, 32), (-2997, 1280), (-1497, 640),
  (-2991, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_028 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 348..359 of piece `zneg` (q = 3). -/
def q3F_zneg_029_b : List QF := [
  (-2991, 1280), (-747, 320), (-597, 256), (-1491, 640),
  (-2979, 1280), (-93, 40), (-2973, 1280), (-297, 128),
  (-2967, 1280), (-741, 320), (-2961, 1280), (-1479, 640),
  (-591, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_029 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 360..371 of piece `zneg` (q = 3). -/
def q3F_zneg_030_b : List QF := [
  (-591, 256), (-369, 160), (-2949, 1280), (-1473, 640),
  (-2943, 1280), (-147, 64), (-2937, 1280), (-1467, 640),
  (-2931, 1280), (-183, 80), (-585, 256), (-1461, 640),
  (-2919, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_030 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 372..383 of piece `zneg` (q = 3). -/
def q3F_zneg_031_b : List QF := [
  (-2919, 1280), (-729, 320), (-291, 128), (-363, 160),
  (-1449, 640), (-723, 320), (-2889, 1280), (-1443, 640),
  (-2883, 1280), (-9, 4), (-2877, 1280), (-1437, 640),
  (-2871, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_031 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 384..395 of piece `zneg` (q = 3). -/
def q3F_zneg_032_b : List QF := [
  (-2871, 1280), (-717, 320), (-573, 256), (-1431, 640),
  (-357, 160), (-285, 128), (-711, 320), (-1419, 640),
  (-177, 80), (-1413, 640), (-141, 64), (-1407, 640),
  (-351, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_032 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 396..407 of piece `zneg` (q = 3). -/
def q3F_zneg_033_b : List QF := [
  (-351, 160), (-1401, 640), (-699, 320), (-279, 128),
  (-87, 40), (-1389, 640), (-693, 320), (-1383, 640),
  (-69, 32), (-1377, 640), (-687, 320), (-1371, 640),
  (-171, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_033 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 408..419 of piece `zneg` (q = 3). -/
def q3F_zneg_034_b : List QF := [
  (-171, 80), (-273, 128), (-681, 320), (-1359, 640),
  (-339, 160), (-1353, 640), (-135, 64), (-1347, 640),
  (-21, 10), (-1341, 640), (-669, 320), (-267, 128),
  (-333, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_034 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_034_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
