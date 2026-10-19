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

/-- Breakpoints of cells 1014..1026 of piece `zneg` (q = 6). -/
def q6F_zneg_078_b : List QF := [
  (-3237, 2560), (-6447, 5120), (-321, 256), (-6393, 5120),
  (-3183, 2560), (-6339, 5120), (-789, 640), (-1257, 1024),
  (-3129, 2560), (-6231, 5120), (-1551, 1280), (-6177, 5120),
  (-615, 512), (-6123, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_078 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_078_b = true := by
  decide +kernel

/-- Breakpoints of cells 1027..1039 of piece `zneg` (q = 6). -/
def q6F_zneg_079_b : List QF := [
  (-6123, 5120), (-381, 320), (-6069, 5120), (-3021, 2560),
  (-1203, 1024), (-1497, 1280), (-5961, 5120), (-2967, 2560),
  (-5907, 5120), (-147, 128), (-5853, 5120), (-2913, 2560),
  (-5799, 5120), (-1443, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_079 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_079_b = true := by
  decide +kernel

/-- Breakpoints of cells 1040..1052 of piece `zneg` (q = 6). -/
def q6F_zneg_080_b : List QF := [
  (-1443, 1280), (-1149, 1024), (-2859, 2560), (-5691, 5120),
  (-177, 160), (-5637, 5120), (-561, 512), (-5583, 5120),
  (-1389, 1280), (-5529, 5120), (-2751, 2560), (-1095, 1024),
  (-681, 640), (-5421, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_080 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_080_b = true := by
  decide +kernel

/-- Breakpoints of cells 1053..1065 of piece `zneg` (q = 6). -/
def q6F_zneg_081_b : List QF := [
  (-5421, 5120), (-2697, 2560), (-5367, 5120), (-267, 256),
  (-5313, 5120), (-2643, 2560), (-5259, 5120), (-327, 320),
  (-1041, 1024), (-2589, 2560), (-5151, 5120), (-1281, 1280),
  (-5097, 5120), (-507, 512)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_081 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_081_b = true := by
  decide +kernel

/-- Breakpoints of cells 1066..1078 of piece `zneg` (q = 6). -/
def q6F_zneg_082_b : List QF := [
  (-507, 512), (-5043, 5120), (-627, 640), (-4989, 5120),
  (-2481, 2560), (-987, 1024), (-1227, 1280), (-4881, 5120),
  (-2427, 2560), (-4827, 5120), (-15, 16), (-4773, 5120),
  (-2373, 2560), (-4719, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_082 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_082_b = true := by
  decide +kernel

/-- Breakpoints of cells 1079..1091 of piece `zneg` (q = 6). -/
def q6F_zneg_083_b : List QF := [
  (-4719, 5120), (-1173, 1280), (-933, 1024), (-2319, 2560),
  (-4611, 5120), (-573, 640), (-4557, 5120), (-453, 512),
  (-4503, 5120), (-1119, 1280), (-4449, 5120), (-2211, 2560),
  (-879, 1024), (-273, 320)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_083 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_083_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
