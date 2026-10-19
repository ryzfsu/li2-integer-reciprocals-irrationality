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

/-- Breakpoints of cells 840..851 of piece `zneg` (q = 4). -/
def q4F_zneg_070_b : List QF := [
  (-7509, 5120), (-1873, 1280), (-1495, 1024), (-3729, 2560),
  (-7441, 5120), (-29, 20), (-7407, 5120), (-739, 512),
  (-7373, 5120), (-1839, 1280), (-7339, 5120), (-3661, 2560),
  (-1461, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_070 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_070_b = true := by
  decide +kernel

/-- Breakpoints of cells 852..863 of piece `zneg` (q = 4). -/
def q4F_zneg_071_b : List QF := [
  (-1461, 1024), (-911, 640), (-7271, 5120), (-3627, 2560),
  (-7237, 5120), (-361, 256), (-7203, 5120), (-3593, 2560),
  (-7169, 5120), (-447, 320), (-1427, 1024), (-3559, 2560),
  (-7101, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_071 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_071_b = true := by
  decide +kernel

/-- Breakpoints of cells 864..875 of piece `zneg` (q = 4). -/
def q4F_zneg_072_b : List QF := [
  (-7101, 5120), (-1771, 1280), (-7067, 5120), (-705, 512),
  (-7033, 5120), (-877, 640), (-6999, 5120), (-3491, 2560),
  (-1393, 1024), (-1737, 1280), (-6931, 5120), (-3457, 2560),
  (-6897, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_072 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_072_b = true := by
  decide +kernel

/-- Breakpoints of cells 876..887 of piece `zneg` (q = 4). -/
def q4F_zneg_073_b : List QF := [
  (-6897, 5120), (-43, 32), (-6863, 5120), (-3423, 2560),
  (-6829, 5120), (-1703, 1280), (-1359, 1024), (-3389, 2560),
  (-6761, 5120), (-843, 640), (-6727, 5120), (-671, 512),
  (-6693, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_073 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_073_b = true := by
  decide +kernel

/-- Breakpoints of cells 888..899 of piece `zneg` (q = 4). -/
def q4F_zneg_074_b : List QF := [
  (-6693, 5120), (-1669, 1280), (-6659, 5120), (-3321, 2560),
  (-1325, 1024), (-413, 320), (-6591, 5120), (-3287, 2560),
  (-6557, 5120), (-327, 256), (-6523, 5120), (-3253, 2560),
  (-6489, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_074 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_074_b = true := by
  decide +kernel

/-- Breakpoints of cells 900..911 of piece `zneg` (q = 4). -/
def q4F_zneg_075_b : List QF := [
  (-6489, 5120), (-809, 640), (-1291, 1024), (-3219, 2560),
  (-6421, 5120), (-1601, 1280), (-6387, 5120), (-637, 512),
  (-6353, 5120), (-99, 80), (-6319, 5120), (-3151, 2560),
  (-1257, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_075 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_075_b = true := by
  decide +kernel

/-- Breakpoints of cells 912..923 of piece `zneg` (q = 4). -/
def q4F_zneg_076_b : List QF := [
  (-1257, 1024), (-1567, 1280), (-6251, 5120), (-3117, 2560),
  (-6217, 5120), (-155, 128), (-6183, 5120), (-3083, 2560),
  (-6149, 5120), (-1533, 1280), (-1223, 1024), (-3049, 2560),
  (-6081, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_076 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_076_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
