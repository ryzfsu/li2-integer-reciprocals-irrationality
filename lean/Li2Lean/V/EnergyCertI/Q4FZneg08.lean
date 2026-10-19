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

/-- Breakpoints of cells 672..683 of piece `zneg` (q = 4). -/
def q4F_zneg_056_b : List QF := [
  (-2073, 1024), (-2587, 1280), (-10331, 5120), (-5157, 2560),
  (-10297, 5120), (-257, 128), (-10263, 5120), (-5123, 2560),
  (-10229, 5120), (-2553, 1280), (-2039, 1024), (-5089, 2560),
  (-10161, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_056 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 684..695 of piece `zneg` (q = 4). -/
def q4F_zneg_057_b : List QF := [
  (-10161, 5120), (-317, 160), (-10127, 5120), (-1011, 512),
  (-10093, 5120), (-2519, 1280), (-10059, 5120), (-5021, 2560),
  (-2005, 1024), (-1251, 640), (-9991, 5120), (-4987, 2560),
  (-9957, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_057 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 696..707 of piece `zneg` (q = 4). -/
def q4F_zneg_058_b : List QF := [
  (-9957, 5120), (-497, 256), (-9923, 5120), (-4953, 2560),
  (-9889, 5120), (-617, 320), (-1971, 1024), (-4919, 2560),
  (-9821, 5120), (-2451, 1280), (-9787, 5120), (-977, 512),
  (-9753, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_058 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 708..719 of piece `zneg` (q = 4). -/
def q4F_zneg_059_b : List QF := [
  (-9753, 5120), (-1217, 640), (-9719, 5120), (-4851, 2560),
  (-1937, 1024), (-2417, 1280), (-9651, 5120), (-4817, 2560),
  (-9617, 5120), (-15, 8), (-9583, 5120), (-4783, 2560),
  (-9549, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_059 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_059_b = true := by
  decide +kernel

/-- Breakpoints of cells 720..731 of piece `zneg` (q = 4). -/
def q4F_zneg_060_b : List QF := [
  (-9549, 5120), (-2383, 1280), (-1903, 1024), (-4749, 2560),
  (-9481, 5120), (-1183, 640), (-9447, 5120), (-943, 512),
  (-9413, 5120), (-2349, 1280), (-9379, 5120), (-4681, 2560),
  (-1869, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_060 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 732..743 of piece `zneg` (q = 4). -/
def q4F_zneg_061_b : List QF := [
  (-1869, 1024), (-583, 320), (-9311, 5120), (-4647, 2560),
  (-9277, 5120), (-463, 256), (-9243, 5120), (-4613, 2560),
  (-9209, 5120), (-1149, 640), (-1835, 1024), (-4579, 2560),
  (-9141, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_061 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 744..755 of piece `zneg` (q = 4). -/
def q4F_zneg_062_b : List QF := [
  (-9141, 5120), (-2281, 1280), (-9107, 5120), (-909, 512),
  (-9073, 5120), (-283, 160), (-9039, 5120), (-4511, 2560),
  (-1801, 1024), (-2247, 1280), (-8971, 5120), (-4477, 2560),
  (-8937, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_062 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_062_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
