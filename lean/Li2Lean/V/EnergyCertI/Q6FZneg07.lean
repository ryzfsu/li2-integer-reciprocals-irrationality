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

/-- Breakpoints of cells 546..558 of piece `zneg` (q = 6). -/
def q6F_zneg_042_b : List QF := [
  (-1911, 512), (-19083, 5120), (-1191, 320), (-19029, 5120),
  (-9501, 2560), (-3795, 1024), (-4737, 1280), (-18921, 5120),
  (-9447, 2560), (-18867, 5120), (-471, 128), (-18813, 5120),
  (-9393, 2560), (-18759, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_042 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 559..571 of piece `zneg` (q = 6). -/
def q6F_zneg_043_b : List QF := [
  (-18759, 5120), (-4683, 1280), (-3741, 1024), (-9339, 2560),
  (-18651, 5120), (-291, 80), (-18597, 5120), (-1857, 512),
  (-18543, 5120), (-4629, 1280), (-18489, 5120), (-9231, 2560),
  (-3687, 1024), (-2301, 640)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_043 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 572..584 of piece `zneg` (q = 6). -/
def q6F_zneg_044_b : List QF := [
  (-2301, 640), (-18381, 5120), (-9177, 2560), (-18327, 5120),
  (-915, 256), (-18273, 5120), (-9123, 2560), (-18219, 5120),
  (-1137, 320), (-3633, 1024), (-9069, 2560), (-18111, 5120),
  (-4521, 1280), (-18057, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_044 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 585..597 of piece `zneg` (q = 6). -/
def q6F_zneg_045_b : List QF := [
  (-18057, 5120), (-1803, 512), (-18003, 5120), (-2247, 640),
  (-17949, 5120), (-8961, 2560), (-3579, 1024), (-4467, 1280),
  (-17841, 5120), (-8907, 2560), (-17787, 5120), (-111, 32),
  (-17733, 5120), (-8853, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_045 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 598..610 of piece `zneg` (q = 6). -/
def q6F_zneg_046_b : List QF := [
  (-8853, 2560), (-17679, 5120), (-4413, 1280), (-3525, 1024),
  (-8799, 2560), (-17571, 5120), (-2193, 640), (-17517, 5120),
  (-1749, 512), (-17463, 5120), (-4359, 1280), (-17409, 5120),
  (-8691, 2560), (-3471, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_046 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 611..623 of piece `zneg` (q = 6). -/
def q6F_zneg_047_b : List QF := [
  (-3471, 1024), (-1083, 320), (-17301, 5120), (-8637, 2560),
  (-17247, 5120), (-861, 256), (-17193, 5120), (-8583, 2560),
  (-17139, 5120), (-2139, 640), (-3417, 1024), (-8529, 2560),
  (-17031, 5120), (-4251, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_047 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_047_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
