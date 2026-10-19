/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 780..792 of piece `zneg` (q = 6). -/
def q6F_zneg_060_b : List QF := [
  (-1599, 640), (-2553, 1024), (-6369, 2560), (-12711, 5120),
  (-3171, 1280), (-12657, 5120), (-1263, 512), (-12603, 5120),
  (-393, 160), (-12549, 5120), (-6261, 2560), (-2499, 1024),
  (-3117, 1280), (-12441, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_060 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 793..805 of piece `zneg` (q = 6). -/
def q6F_zneg_061_b : List QF := [
  (-12441, 5120), (-6207, 2560), (-12387, 5120), (-309, 128),
  (-12333, 5120), (-6153, 2560), (-12279, 5120), (-3063, 1280),
  (-2445, 1024), (-6099, 2560), (-12171, 5120), (-759, 320),
  (-12117, 5120), (-1209, 512)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_061 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 806..818 of piece `zneg` (q = 6). -/
def q6F_zneg_062_b : List QF := [
  (-1209, 512), (-12063, 5120), (-3009, 1280), (-12009, 5120),
  (-5991, 2560), (-2391, 1024), (-1491, 640), (-11901, 5120),
  (-5937, 2560), (-11847, 5120), (-591, 256), (-11793, 5120),
  (-5883, 2560), (-11739, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_062 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_062_b = true := by
  decide +kernel

/-- Breakpoints of cells 819..831 of piece `zneg` (q = 6). -/
def q6F_zneg_063_b : List QF := [
  (-11739, 5120), (-183, 80), (-2337, 1024), (-5829, 2560),
  (-11631, 5120), (-2901, 1280), (-11577, 5120), (-1155, 512),
  (-11523, 5120), (-1437, 640), (-11469, 5120), (-5721, 2560),
  (-2283, 1024), (-2847, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_063 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 832..844 of piece `zneg` (q = 6). -/
def q6F_zneg_064_b : List QF := [
  (-2847, 1280), (-11361, 5120), (-5667, 2560), (-11307, 5120),
  (-141, 64), (-11253, 5120), (-5613, 2560), (-11199, 5120),
  (-2793, 1280), (-2229, 1024), (-5559, 2560), (-11091, 5120),
  (-1383, 640), (-11037, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_064 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 845..857 of piece `zneg` (q = 6). -/
def q6F_zneg_065_b : List QF := [
  (-11037, 5120), (-1101, 512), (-10983, 5120), (-2739, 1280),
  (-10929, 5120), (-5451, 2560), (-2175, 1024), (-339, 160),
  (-10821, 5120), (-5397, 2560), (-10767, 5120), (-537, 256),
  (-10713, 5120), (-5343, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_065 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
