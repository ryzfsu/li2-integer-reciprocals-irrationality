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

/-- Breakpoints of cells 78..90 of piece `zneg` (q = 6). -/
def q6F_zneg_006_b : List QF := [
  (-1509, 256), (-60333, 10240), (-30153, 5120), (-60279, 10240),
  (-15063, 2560), (-12045, 2048), (-30099, 5120), (-60171, 10240),
  (-3759, 640), (-60117, 10240), (-6009, 1024), (-60063, 10240),
  (-15009, 2560), (-60009, 10240)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_006 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_006_b = true := by
  decide +kernel

/-- Breakpoints of cells 91..103 of piece `zneg` (q = 6). -/
def q6F_zneg_007_b : List QF := [
  (-60009, 10240), (-29991, 5120), (-11991, 2048), (-7491, 1280),
  (-59901, 10240), (-29937, 5120), (-59847, 10240), (-2991, 512),
  (-59793, 10240), (-29883, 5120), (-59739, 10240), (-933, 160),
  (-11937, 2048), (-29829, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_007 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 104..116 of piece `zneg` (q = 6). -/
def q6F_zneg_008_b : List QF := [
  (-29829, 5120), (-59631, 10240), (-14901, 2560), (-59577, 10240),
  (-5955, 1024), (-59523, 10240), (-7437, 1280), (-59469, 10240),
  (-29721, 5120), (-11883, 2048), (-14847, 2560), (-59361, 10240),
  (-29667, 5120), (-59307, 10240)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_008 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 117..129 of piece `zneg` (q = 6). -/
def q6F_zneg_009_b : List QF := [
  (-59307, 10240), (-741, 128), (-59253, 10240), (-29613, 5120),
  (-59199, 10240), (-14793, 2560), (-11829, 2048), (-29559, 5120),
  (-59091, 10240), (-7383, 1280), (-59037, 10240), (-5901, 1024),
  (-58983, 10240), (-14739, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_009 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..142 of piece `zneg` (q = 6). -/
def q6F_zneg_010_b : List QF := [
  (-14739, 2560), (-58929, 10240), (-29451, 5120), (-11775, 2048),
  (-1839, 320), (-58821, 10240), (-29397, 5120), (-58767, 10240),
  (-2937, 512), (-58713, 10240), (-29343, 5120), (-58659, 10240),
  (-7329, 1280), (-11721, 2048)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_010 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 143..155 of piece `zneg` (q = 6). -/
def q6F_zneg_011_b : List QF := [
  (-11721, 2048), (-29289, 5120), (-58551, 10240), (-14631, 2560),
  (-58497, 10240), (-5847, 1024), (-58443, 10240), (-3651, 640),
  (-58389, 10240), (-29181, 5120), (-11667, 2048), (-14577, 2560),
  (-58281, 10240), (-29127, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_011 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_011_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
