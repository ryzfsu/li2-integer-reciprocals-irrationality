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

/-- Breakpoints of cells 156..168 of piece `zneg` (q = 6). -/
def q6F_zneg_012_b : List QF := [
  (-29127, 5120), (-58227, 10240), (-1455, 256), (-58173, 10240),
  (-29073, 5120), (-58119, 10240), (-14523, 2560), (-11613, 2048),
  (-29019, 5120), (-58011, 10240), (-453, 80), (-57957, 10240),
  (-5793, 1024), (-57903, 10240)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_012 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 169..181 of piece `zneg` (q = 6). -/
def q6F_zneg_013_b : List QF := [
  (-57903, 10240), (-14469, 2560), (-57849, 10240), (-28911, 5120),
  (-11559, 2048), (-7221, 1280), (-57741, 10240), (-28857, 5120),
  (-57687, 10240), (-2883, 512), (-57633, 10240), (-28803, 5120),
  (-57579, 10240), (-3597, 640)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_013 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_013_b = true := by
  decide +kernel

/-- Breakpoints of cells 182..194 of piece `zneg` (q = 6). -/
def q6F_zneg_014_b : List QF := [
  (-3597, 640), (-11505, 2048), (-28749, 5120), (-57471, 10240),
  (-14361, 2560), (-57417, 10240), (-5739, 1024), (-57363, 10240),
  (-7167, 1280), (-57309, 10240), (-28641, 5120), (-11451, 2048),
  (-14307, 2560), (-28587, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_014 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 195..207 of piece `zneg` (q = 6). -/
def q6F_zneg_015_b : List QF := [
  (-28587, 5120), (-357, 64), (-28533, 5120), (-14253, 2560),
  (-28479, 5120), (-7113, 1280), (-5685, 1024), (-14199, 2560),
  (-28371, 5120), (-3543, 640), (-28317, 5120), (-2829, 512),
  (-28263, 5120), (-7059, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_015 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 208..220 of piece `zneg` (q = 6). -/
def q6F_zneg_016_b : List QF := [
  (-7059, 1280), (-28209, 5120), (-14091, 2560), (-5631, 1024),
  (-879, 160), (-28101, 5120), (-14037, 2560), (-28047, 5120),
  (-1401, 256), (-27993, 5120), (-13983, 2560), (-27939, 5120),
  (-3489, 640), (-5577, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_016 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 221..233 of piece `zneg` (q = 6). -/
def q6F_zneg_017_b : List QF := [
  (-5577, 1024), (-13929, 2560), (-27831, 5120), (-6951, 1280),
  (-27777, 5120), (-2775, 512), (-27723, 5120), (-1731, 320),
  (-27669, 5120), (-13821, 2560), (-5523, 1024), (-6897, 1280),
  (-27561, 5120), (-13767, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_017 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_017_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
