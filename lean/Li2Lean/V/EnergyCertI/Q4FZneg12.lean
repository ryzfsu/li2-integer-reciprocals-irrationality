/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 1008..1019 of piece `zneg` (q = 4). -/
def q4F_zneg_084_b : List QF := [
  (-4653, 5120), (-1159, 1280), (-4619, 5120), (-2301, 2560),
  (-917, 1024), (-571, 640), (-4551, 5120), (-2267, 2560),
  (-4517, 5120), (-225, 256), (-4483, 5120), (-2233, 2560),
  (-4449, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_084 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_084_b = true := by
  decide +kernel

/-- Breakpoints of cells 1020..1031 of piece `zneg` (q = 4). -/
def q4F_zneg_085_b : List QF := [
  (-4449, 5120), (-277, 320), (-883, 1024), (-2199, 2560),
  (-4381, 5120), (-1091, 1280), (-4347, 5120), (-433, 512),
  (-4313, 5120), (-537, 640), (-4279, 5120), (-2131, 2560),
  (-849, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_085 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_085_b = true := by
  decide +kernel

/-- Breakpoints of cells 1032..1043 of piece `zneg` (q = 4). -/
def q4F_zneg_086_b : List QF := [
  (-849, 1024), (-1057, 1280), (-4211, 5120), (-2097, 2560),
  (-4177, 5120), (-13, 16), (-4143, 5120), (-2063, 2560),
  (-4109, 5120), (-1023, 1280), (-815, 1024), (-2029, 2560),
  (-4041, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_086 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_086_b = true := by
  decide +kernel

/-- Breakpoints of cells 1044..1055 of piece `zneg` (q = 4). -/
def q4F_zneg_087_b : List QF := [
  (-4041, 5120), (-503, 640), (-4007, 5120), (-399, 512),
  (-3973, 5120), (-989, 1280), (-3939, 5120), (-1961, 2560),
  (-781, 1024), (-243, 320), (-3871, 5120), (-1927, 2560),
  (-3837, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_087 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_087_b = true := by
  decide +kernel

/-- Breakpoints of cells 1056..1067 of piece `zneg` (q = 4). -/
def q4F_zneg_088_b : List QF := [
  (-3837, 5120), (-191, 256), (-3803, 5120), (-1893, 2560),
  (-3769, 5120), (-469, 640), (-747, 1024), (-1859, 2560),
  (-3701, 5120), (-921, 1280), (-3667, 5120), (-365, 512),
  (-3633, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_088 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_088_b = true := by
  decide +kernel

/-- Breakpoints of cells 1068..1079 of piece `zneg` (q = 4). -/
def q4F_zneg_089_b : List QF := [
  (-3633, 5120), (-113, 160), (-3599, 5120), (-1791, 2560),
  (-713, 1024), (-887, 1280), (-3531, 5120), (-1757, 2560),
  (-3497, 5120), (-87, 128), (-3463, 5120), (-1723, 2560),
  (-3429, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_089 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_089_b = true := by
  decide +kernel

/-- Breakpoints of cells 1080..1091 of piece `zneg` (q = 4). -/
def q4F_zneg_090_b : List QF := [
  (-3429, 5120), (-853, 1280), (-679, 1024), (-1689, 2560),
  (-3361, 5120), (-209, 320), (-3327, 5120), (-331, 512),
  (-3293, 5120), (-819, 1280), (-3259, 5120), (-1621, 2560),
  (-645, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_090 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_090_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
