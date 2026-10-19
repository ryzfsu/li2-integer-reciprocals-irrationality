/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 624..636 of piece `zneg` (q = 5). -/
def q5F_zneg_048_b : List QF := [
  (-1405, 512), (-3507, 1280), (-7003, 2560), (-437, 160),
  (-6981, 2560), (-697, 256), (-6959, 2560), (-1737, 640),
  (-6937, 2560), (-3463, 1280), (-1383, 512), (-863, 320),
  (-6893, 2560), (-3441, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_048 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_048_b = true := by
  decide +kernel

/-- Breakpoints of cells 637..649 of piece `zneg` (q = 5). -/
def q5F_zneg_049_b : List QF := [
  (-3441, 1280), (-6871, 2560), (-343, 128), (-6849, 2560),
  (-3419, 1280), (-6827, 2560), (-213, 80), (-1361, 512),
  (-3397, 1280), (-6783, 2560), (-1693, 640), (-6761, 2560),
  (-675, 256), (-6739, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_049 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..662 of piece `zneg` (q = 5). -/
def q5F_zneg_050_b : List QF := [
  (-6739, 2560), (-841, 320), (-6717, 2560), (-3353, 1280),
  (-1339, 512), (-1671, 640), (-6673, 2560), (-3331, 1280),
  (-6651, 2560), (-83, 32), (-6629, 2560), (-3309, 1280),
  (-6607, 2560), (-1649, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_050 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 663..675 of piece `zneg` (q = 5). -/
def q5F_zneg_051_b : List QF := [
  (-1649, 640), (-1317, 512), (-3287, 1280), (-6563, 2560),
  (-819, 320), (-6541, 2560), (-653, 256), (-6519, 2560),
  (-1627, 640), (-6497, 2560), (-3243, 1280), (-1295, 512),
  (-101, 40), (-6453, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_051 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 676..688 of piece `zneg` (q = 5). -/
def q5F_zneg_052_b : List QF := [
  (-6453, 2560), (-3221, 1280), (-6431, 2560), (-321, 128),
  (-6409, 2560), (-3199, 1280), (-6387, 2560), (-797, 320),
  (-1273, 512), (-3177, 1280), (-6343, 2560), (-1583, 640),
  (-6321, 2560), (-631, 256)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_052 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 689..701 of piece `zneg` (q = 5). -/
def q5F_zneg_053_b : List QF := [
  (-631, 256), (-6299, 2560), (-393, 160), (-6277, 2560),
  (-3133, 1280), (-1251, 512), (-1561, 640), (-6233, 2560),
  (-3111, 1280), (-6211, 2560), (-155, 64), (-6189, 2560),
  (-3089, 1280), (-6167, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_053 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_053_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
