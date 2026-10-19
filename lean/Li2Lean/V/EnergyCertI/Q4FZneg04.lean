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

/-- Breakpoints of cells 336..347 of piece `zneg` (q = 4). -/
def q4F_zneg_028_b : List QF := [
  (-16077, 5120), (-803, 256), (-16043, 5120), (-8013, 2560),
  (-16009, 5120), (-1999, 640), (-3195, 1024), (-7979, 2560),
  (-15941, 5120), (-3981, 1280), (-15907, 5120), (-1589, 512),
  (-15873, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_028 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 348..359 of piece `zneg` (q = 4). -/
def q4F_zneg_029_b : List QF := [
  (-15873, 5120), (-991, 320), (-15839, 5120), (-7911, 2560),
  (-3161, 1024), (-3947, 1280), (-15771, 5120), (-7877, 2560),
  (-15737, 5120), (-393, 128), (-15703, 5120), (-7843, 2560),
  (-15669, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_029 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 360..371 of piece `zneg` (q = 4). -/
def q4F_zneg_030_b : List QF := [
  (-15669, 5120), (-3913, 1280), (-3127, 1024), (-7809, 2560),
  (-15601, 5120), (-487, 160), (-15567, 5120), (-1555, 512),
  (-15533, 5120), (-3879, 1280), (-15499, 5120), (-7741, 2560),
  (-3093, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_030 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 372..383 of piece `zneg` (q = 4). -/
def q4F_zneg_031_b : List QF := [
  (-3093, 1024), (-1931, 640), (-15431, 5120), (-7707, 2560),
  (-15397, 5120), (-769, 256), (-15363, 5120), (-7673, 2560),
  (-15329, 5120), (-957, 320), (-3059, 1024), (-7639, 2560),
  (-15261, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_031 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 384..395 of piece `zneg` (q = 4). -/
def q4F_zneg_032_b : List QF := [
  (-15261, 5120), (-3811, 1280), (-15227, 5120), (-1521, 512),
  (-15193, 5120), (-1897, 640), (-15159, 5120), (-7571, 2560),
  (-3025, 1024), (-3777, 1280), (-15091, 5120), (-7537, 2560),
  (-15057, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_032 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 396..407 of piece `zneg` (q = 4). -/
def q4F_zneg_033_b : List QF := [
  (-15057, 5120), (-47, 16), (-15023, 5120), (-7503, 2560),
  (-14989, 5120), (-3743, 1280), (-2991, 1024), (-7469, 2560),
  (-14921, 5120), (-1863, 640), (-14887, 5120), (-1487, 512),
  (-14853, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_033 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 408..419 of piece `zneg` (q = 4). -/
def q4F_zneg_034_b : List QF := [
  (-14853, 5120), (-3709, 1280), (-14819, 5120), (-7401, 2560),
  (-2957, 1024), (-923, 320), (-14751, 5120), (-7367, 2560),
  (-14717, 5120), (-735, 256), (-14683, 5120), (-7333, 2560),
  (-14649, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_034 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_034_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
