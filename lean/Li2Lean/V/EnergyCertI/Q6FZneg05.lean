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

/-- Breakpoints of cells 390..402 of piece `zneg` (q = 6). -/
def q6F_zneg_030_b : List QF := [
  (-11661, 2560), (-4659, 1024), (-5817, 1280), (-23241, 5120),
  (-11607, 2560), (-23187, 5120), (-579, 128), (-23133, 5120),
  (-11553, 2560), (-23079, 5120), (-5763, 1280), (-4605, 1024),
  (-11499, 2560), (-22971, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_030 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 403..415 of piece `zneg` (q = 6). -/
def q6F_zneg_031_b : List QF := [
  (-22971, 5120), (-717, 160), (-22917, 5120), (-2289, 512),
  (-22863, 5120), (-5709, 1280), (-22809, 5120), (-11391, 2560),
  (-4551, 1024), (-2841, 640), (-22701, 5120), (-11337, 2560),
  (-22647, 5120), (-1131, 256)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_031 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 416..428 of piece `zneg` (q = 6). -/
def q6F_zneg_032_b : List QF := [
  (-1131, 256), (-22593, 5120), (-11283, 2560), (-22539, 5120),
  (-1407, 320), (-4497, 1024), (-11229, 2560), (-22431, 5120),
  (-5601, 1280), (-22377, 5120), (-2235, 512), (-22323, 5120),
  (-2787, 640), (-22269, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_032 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 429..441 of piece `zneg` (q = 6). -/
def q6F_zneg_033_b : List QF := [
  (-22269, 5120), (-11121, 2560), (-4443, 1024), (-5547, 1280),
  (-22161, 5120), (-11067, 2560), (-22107, 5120), (-69, 16),
  (-22053, 5120), (-11013, 2560), (-21999, 5120), (-5493, 1280),
  (-4389, 1024), (-10959, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_033 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 442..454 of piece `zneg` (q = 6). -/
def q6F_zneg_034_b : List QF := [
  (-10959, 2560), (-21891, 5120), (-2733, 640), (-21837, 5120),
  (-2181, 512), (-21783, 5120), (-5439, 1280), (-21729, 5120),
  (-10851, 2560), (-4335, 1024), (-1353, 320), (-21621, 5120),
  (-10797, 2560), (-21567, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_034 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_034_b = true := by
  decide +kernel

/-- Breakpoints of cells 455..467 of piece `zneg` (q = 6). -/
def q6F_zneg_035_b : List QF := [
  (-21567, 5120), (-1077, 256), (-21513, 5120), (-10743, 2560),
  (-21459, 5120), (-2679, 640), (-4281, 1024), (-10689, 2560),
  (-21351, 5120), (-5331, 1280), (-21297, 5120), (-2127, 512),
  (-21243, 5120), (-663, 160)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_035 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_035_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
