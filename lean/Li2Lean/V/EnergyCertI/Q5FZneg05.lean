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

/-- Breakpoints of cells 390..402 of piece `zneg` (q = 5). -/
def q5F_zneg_030_b : List QF := [
  (-9599, 2560), (-2397, 640), (-9577, 2560), (-4783, 1280),
  (-1911, 512), (-1193, 320), (-9533, 2560), (-4761, 1280),
  (-9511, 2560), (-475, 128), (-9489, 2560), (-4739, 1280),
  (-9467, 2560), (-591, 160)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_030 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 403..415 of piece `zneg` (q = 5). -/
def q5F_zneg_031_b : List QF := [
  (-591, 160), (-1889, 512), (-4717, 1280), (-9423, 2560),
  (-2353, 640), (-9401, 2560), (-939, 256), (-9379, 2560),
  (-1171, 320), (-9357, 2560), (-4673, 1280), (-1867, 512),
  (-2331, 640), (-9313, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_031 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 416..428 of piece `zneg` (q = 5). -/
def q5F_zneg_032_b : List QF := [
  (-9313, 2560), (-4651, 1280), (-9291, 2560), (-29, 8),
  (-9269, 2560), (-4629, 1280), (-9247, 2560), (-2309, 640),
  (-1845, 512), (-4607, 1280), (-9203, 2560), (-1149, 320),
  (-9181, 2560), (-917, 256)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_032 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 429..441 of piece `zneg` (q = 5). -/
def q5F_zneg_033_b : List QF := [
  (-917, 256), (-9159, 2560), (-2287, 640), (-9137, 2560),
  (-4563, 1280), (-1823, 512), (-569, 160), (-9093, 2560),
  (-4541, 1280), (-9071, 2560), (-453, 128), (-9049, 2560),
  (-4519, 1280), (-9027, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_033 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 442..454 of piece `zneg` (q = 5). -/
def q5F_zneg_034_b : List QF := [
  (-9027, 2560), (-1127, 320), (-1801, 512), (-4497, 1280),
  (-8983, 2560), (-2243, 640), (-8961, 2560), (-895, 256),
  (-8939, 2560), (-279, 80), (-8917, 2560), (-4453, 1280),
  (-1779, 512), (-2221, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_034 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_034_b = true := by
  decide +kernel

/-- Breakpoints of cells 455..467 of piece `zneg` (q = 5). -/
def q5F_zneg_035_b : List QF := [
  (-2221, 640), (-8873, 2560), (-4431, 1280), (-8851, 2560),
  (-221, 64), (-8829, 2560), (-4409, 1280), (-8807, 2560),
  (-2199, 640), (-1757, 512), (-4387, 1280), (-8763, 2560),
  (-547, 160), (-8741, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_035 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_035_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
