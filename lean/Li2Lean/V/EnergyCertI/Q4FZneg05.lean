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

/-- Breakpoints of cells 420..431 of piece `zneg` (q = 4). -/
def q4F_zneg_035_b : List QF := [
  (-14649, 5120), (-1829, 640), (-2923, 1024), (-7299, 2560),
  (-14581, 5120), (-3641, 1280), (-14547, 5120), (-1453, 512),
  (-14513, 5120), (-453, 160), (-14479, 5120), (-7231, 2560),
  (-2889, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_035 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 432..443 of piece `zneg` (q = 4). -/
def q4F_zneg_036_b : List QF := [
  (-2889, 1024), (-3607, 1280), (-14411, 5120), (-7197, 2560),
  (-14377, 5120), (-359, 128), (-14343, 5120), (-7163, 2560),
  (-14309, 5120), (-3573, 1280), (-2855, 1024), (-7129, 2560),
  (-14241, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_036 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 444..455 of piece `zneg` (q = 4). -/
def q4F_zneg_037_b : List QF := [
  (-14241, 5120), (-889, 320), (-14207, 5120), (-1419, 512),
  (-14173, 5120), (-3539, 1280), (-14139, 5120), (-7061, 2560),
  (-2821, 1024), (-1761, 640), (-14071, 5120), (-7027, 2560),
  (-14037, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_037 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 456..467 of piece `zneg` (q = 4). -/
def q4F_zneg_038_b : List QF := [
  (-14037, 5120), (-701, 256), (-14003, 5120), (-6993, 2560),
  (-13969, 5120), (-109, 40), (-2787, 1024), (-6959, 2560),
  (-13901, 5120), (-3471, 1280), (-13867, 5120), (-1385, 512),
  (-13833, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_038 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 468..479 of piece `zneg` (q = 4). -/
def q4F_zneg_039_b : List QF := [
  (-13833, 5120), (-1727, 640), (-13799, 5120), (-6891, 2560),
  (-2753, 1024), (-3437, 1280), (-13731, 5120), (-6857, 2560),
  (-13697, 5120), (-171, 64), (-13663, 5120), (-6823, 2560),
  (-13629, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_039 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 480..491 of piece `zneg` (q = 4). -/
def q4F_zneg_040_b : List QF := [
  (-13629, 5120), (-3403, 1280), (-2719, 1024), (-6789, 2560),
  (-13561, 5120), (-1693, 640), (-13527, 5120), (-1351, 512),
  (-13493, 5120), (-3369, 1280), (-13459, 5120), (-6721, 2560),
  (-2685, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_040 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 492..503 of piece `zneg` (q = 4). -/
def q4F_zneg_041_b : List QF := [
  (-2685, 1024), (-419, 160), (-13391, 5120), (-6687, 2560),
  (-13357, 5120), (-667, 256), (-13323, 5120), (-6653, 2560),
  (-13289, 5120), (-1659, 640), (-2651, 1024), (-6619, 2560),
  (-13221, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_041 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
