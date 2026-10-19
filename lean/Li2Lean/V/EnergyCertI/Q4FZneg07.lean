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

/-- Breakpoints of cells 588..599 of piece `zneg` (q = 4). -/
def q4F_zneg_049_b : List QF := [
  (-11793, 5120), (-23, 10), (-11759, 5120), (-5871, 2560),
  (-2345, 1024), (-2927, 1280), (-11691, 5120), (-5837, 2560),
  (-11657, 5120), (-291, 128), (-11623, 5120), (-5803, 2560),
  (-11589, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_049 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 600..611 of piece `zneg` (q = 4). -/
def q4F_zneg_050_b : List QF := [
  (-11589, 5120), (-2893, 1280), (-2311, 1024), (-5769, 2560),
  (-11521, 5120), (-719, 320), (-11487, 5120), (-1147, 512),
  (-11453, 5120), (-2859, 1280), (-11419, 5120), (-5701, 2560),
  (-2277, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_050 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 612..623 of piece `zneg` (q = 4). -/
def q4F_zneg_051_b : List QF := [
  (-2277, 1024), (-1421, 640), (-11351, 5120), (-5667, 2560),
  (-11317, 5120), (-565, 256), (-11283, 5120), (-5633, 2560),
  (-11249, 5120), (-351, 160), (-2243, 1024), (-5599, 2560),
  (-11181, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_051 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 624..635 of piece `zneg` (q = 4). -/
def q4F_zneg_052_b : List QF := [
  (-11181, 5120), (-2791, 1280), (-11147, 5120), (-1113, 512),
  (-11113, 5120), (-1387, 640), (-11079, 5120), (-5531, 2560),
  (-2209, 1024), (-2757, 1280), (-11011, 5120), (-5497, 2560),
  (-10977, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_052 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 636..647 of piece `zneg` (q = 4). -/
def q4F_zneg_053_b : List QF := [
  (-10977, 5120), (-137, 64), (-10943, 5120), (-5463, 2560),
  (-10909, 5120), (-2723, 1280), (-2175, 1024), (-5429, 2560),
  (-10841, 5120), (-1353, 640), (-10807, 5120), (-1079, 512),
  (-10773, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_053 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_053_b = true := by
  decide +kernel

/-- Breakpoints of cells 648..659 of piece `zneg` (q = 4). -/
def q4F_zneg_054_b : List QF := [
  (-10773, 5120), (-2689, 1280), (-10739, 5120), (-5361, 2560),
  (-2141, 1024), (-167, 80), (-10671, 5120), (-5327, 2560),
  (-10637, 5120), (-531, 256), (-10603, 5120), (-5293, 2560),
  (-10569, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_054 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 660..671 of piece `zneg` (q = 4). -/
def q4F_zneg_055_b : List QF := [
  (-10569, 5120), (-1319, 640), (-2107, 1024), (-5259, 2560),
  (-10501, 5120), (-2621, 1280), (-10467, 5120), (-1045, 512),
  (-10433, 5120), (-651, 320), (-10399, 5120), (-5191, 2560),
  (-2073, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_055 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_055_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
