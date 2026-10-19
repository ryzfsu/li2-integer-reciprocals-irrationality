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

/-- Breakpoints of cells 702..714 of piece `zneg` (q = 6). -/
def q6F_zneg_054_b : List QF := [
  (-7449, 2560), (-14871, 5120), (-3711, 1280), (-14817, 5120),
  (-1479, 512), (-14763, 5120), (-921, 320), (-14709, 5120),
  (-7341, 2560), (-2931, 1024), (-3657, 1280), (-14601, 5120),
  (-7287, 2560), (-14547, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_054 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 715..727 of piece `zneg` (q = 6). -/
def q6F_zneg_055_b : List QF := [
  (-14547, 5120), (-363, 128), (-14493, 5120), (-7233, 2560),
  (-14439, 5120), (-3603, 1280), (-2877, 1024), (-7179, 2560),
  (-14331, 5120), (-447, 160), (-14277, 5120), (-1425, 512),
  (-14223, 5120), (-3549, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_055 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_055_b = true := by
  decide +kernel

/-- Breakpoints of cells 728..740 of piece `zneg` (q = 6). -/
def q6F_zneg_056_b : List QF := [
  (-3549, 1280), (-14169, 5120), (-7071, 2560), (-2823, 1024),
  (-1761, 640), (-14061, 5120), (-7017, 2560), (-14007, 5120),
  (-699, 256), (-13953, 5120), (-6963, 2560), (-13899, 5120),
  (-867, 320), (-2769, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_056 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 741..753 of piece `zneg` (q = 6). -/
def q6F_zneg_057_b : List QF := [
  (-2769, 1024), (-6909, 2560), (-13791, 5120), (-3441, 1280),
  (-13737, 5120), (-1371, 512), (-13683, 5120), (-1707, 640),
  (-13629, 5120), (-6801, 2560), (-2715, 1024), (-3387, 1280),
  (-13521, 5120), (-6747, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_057 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 754..766 of piece `zneg` (q = 6). -/
def q6F_zneg_058_b : List QF := [
  (-6747, 2560), (-13467, 5120), (-21, 8), (-13413, 5120),
  (-6693, 2560), (-13359, 5120), (-3333, 1280), (-2661, 1024),
  (-6639, 2560), (-13251, 5120), (-1653, 640), (-13197, 5120),
  (-1317, 512), (-13143, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_058 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 767..779 of piece `zneg` (q = 6). -/
def q6F_zneg_059_b : List QF := [
  (-13143, 5120), (-3279, 1280), (-13089, 5120), (-6531, 2560),
  (-2607, 1024), (-813, 320), (-12981, 5120), (-6477, 2560),
  (-12927, 5120), (-645, 256), (-12873, 5120), (-6423, 2560),
  (-12819, 5120), (-1599, 640)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_059 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_059_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
