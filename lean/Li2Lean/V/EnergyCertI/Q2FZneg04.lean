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

/-- Breakpoints of cells 336..347 of piece `zneg` (q = 2). -/
def q2F_zneg_028_b : List QF := [
  (-1783, 1280), (-3559, 2560), (-111, 80), (-709, 512),
  (-1769, 1280), (-3531, 2560), (-881, 640), (-3517, 2560),
  (-351, 256), (-3503, 2560), (-437, 320), (-3489, 2560),
  (-1741, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_028 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 348..359 of piece `zneg` (q = 2). -/
def q2F_zneg_029_b : List QF := [
  (-1741, 1280), (-695, 512), (-867, 640), (-3461, 2560),
  (-1727, 1280), (-3447, 2560), (-43, 32), (-3433, 2560),
  (-1713, 1280), (-3419, 2560), (-853, 640), (-681, 512),
  (-1699, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_029 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 360..371 of piece `zneg` (q = 2). -/
def q2F_zneg_030_b : List QF := [
  (-1699, 1280), (-3391, 2560), (-423, 320), (-3377, 2560),
  (-337, 256), (-3363, 2560), (-839, 640), (-3349, 2560),
  (-1671, 1280), (-667, 512), (-13, 10), (-3321, 2560),
  (-1657, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_030 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 372..383 of piece `zneg` (q = 2). -/
def q2F_zneg_031_b : List QF := [
  (-1657, 1280), (-3307, 2560), (-165, 128), (-3293, 2560),
  (-1643, 1280), (-3279, 2560), (-409, 320), (-653, 512),
  (-1629, 1280), (-3251, 2560), (-811, 640), (-3237, 2560),
  (-323, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_031 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 384..395 of piece `zneg` (q = 2). -/
def q2F_zneg_032_b : List QF := [
  (-323, 256), (-3223, 2560), (-201, 160), (-3209, 2560),
  (-1601, 1280), (-639, 512), (-797, 640), (-3181, 2560),
  (-1587, 1280), (-3167, 2560), (-79, 64), (-3153, 2560),
  (-1573, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_032 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 396..407 of piece `zneg` (q = 2). -/
def q2F_zneg_033_b : List QF := [
  (-1573, 1280), (-3139, 2560), (-783, 640), (-625, 512),
  (-1559, 1280), (-3111, 2560), (-97, 80), (-3097, 2560),
  (-309, 256), (-3083, 2560), (-769, 640), (-3069, 2560),
  (-1531, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_033 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 408..419 of piece `zneg` (q = 2). -/
def q2F_zneg_034_b : List QF := [
  (-1531, 1280), (-611, 512), (-381, 320), (-3041, 2560),
  (-1517, 1280), (-3027, 2560), (-151, 128), (-3013, 2560),
  (-1503, 1280), (-2999, 2560), (-187, 160), (-597, 512),
  (-1489, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_034 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_034_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
