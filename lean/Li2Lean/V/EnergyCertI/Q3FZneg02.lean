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

/-- Breakpoints of cells 168..179 of piece `zneg` (q = 3). -/
def q3F_zneg_014_b : List QF := [
  (-3531, 1280), (-441, 160), (-705, 256), (-1761, 640),
  (-3519, 1280), (-879, 320), (-3513, 1280), (-351, 128),
  (-3507, 1280), (-219, 80), (-3501, 1280), (-1749, 640),
  (-699, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_014 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..191 of piece `zneg` (q = 3). -/
def q3F_zneg_015_b : List QF := [
  (-699, 256), (-873, 320), (-3489, 1280), (-1743, 640),
  (-3483, 1280), (-87, 32), (-3477, 1280), (-1737, 640),
  (-3471, 1280), (-867, 320), (-693, 256), (-1731, 640),
  (-3459, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_015 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 192..203 of piece `zneg` (q = 3). -/
def q3F_zneg_016_b : List QF := [
  (-3459, 1280), (-27, 10), (-3453, 1280), (-345, 128),
  (-3447, 1280), (-861, 320), (-3441, 1280), (-1719, 640),
  (-687, 256), (-429, 160), (-3429, 1280), (-1713, 640),
  (-3423, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_016 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 204..215 of piece `zneg` (q = 3). -/
def q3F_zneg_017_b : List QF := [
  (-3423, 1280), (-171, 64), (-3417, 1280), (-1707, 640),
  (-3411, 1280), (-213, 80), (-681, 256), (-1701, 640),
  (-3399, 1280), (-849, 320), (-3393, 1280), (-339, 128),
  (-3387, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_017 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 216..227 of piece `zneg` (q = 3). -/
def q3F_zneg_018_b : List QF := [
  (-3387, 1280), (-423, 160), (-3381, 1280), (-1689, 640),
  (-675, 256), (-843, 320), (-3369, 1280), (-1683, 640),
  (-3363, 1280), (-21, 8), (-3357, 1280), (-1677, 640),
  (-3351, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_018 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 228..239 of piece `zneg` (q = 3). -/
def q3F_zneg_019_b : List QF := [
  (-3351, 1280), (-837, 320), (-669, 256), (-1671, 640),
  (-3339, 1280), (-417, 160), (-3333, 1280), (-333, 128),
  (-3327, 1280), (-831, 320), (-3321, 1280), (-1659, 640),
  (-663, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_019 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..251 of piece `zneg` (q = 3). -/
def q3F_zneg_020_b : List QF := [
  (-663, 256), (-207, 80), (-3309, 1280), (-1653, 640),
  (-3303, 1280), (-165, 64), (-3297, 1280), (-1647, 640),
  (-3291, 1280), (-411, 160), (-657, 256), (-1641, 640),
  (-3279, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_020 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
