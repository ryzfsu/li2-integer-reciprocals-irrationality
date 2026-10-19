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

/-- Breakpoints of cells 858..870 of piece `zneg` (q = 6). -/
def q6F_zneg_066_b : List QF := [
  (-5343, 2560), (-10659, 5120), (-1329, 640), (-2121, 1024),
  (-5289, 2560), (-10551, 5120), (-2631, 1280), (-10497, 5120),
  (-1047, 512), (-10443, 5120), (-651, 320), (-10389, 5120),
  (-5181, 2560), (-2067, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_066 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 871..883 of piece `zneg` (q = 6). -/
def q6F_zneg_067_b : List QF := [
  (-2067, 1024), (-2577, 1280), (-10281, 5120), (-5127, 2560),
  (-10227, 5120), (-255, 128), (-10173, 5120), (-5073, 2560),
  (-10119, 5120), (-2523, 1280), (-2013, 1024), (-5019, 2560),
  (-10011, 5120), (-39, 20)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_067 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_067_b = true := by
  decide +kernel

/-- Breakpoints of cells 884..896 of piece `zneg` (q = 6). -/
def q6F_zneg_068_b : List QF := [
  (-39, 20), (-9957, 5120), (-993, 512), (-9903, 5120),
  (-2469, 1280), (-9849, 5120), (-4911, 2560), (-1959, 1024),
  (-1221, 640), (-9741, 5120), (-4857, 2560), (-9687, 5120),
  (-483, 256), (-9633, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_068 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_068_b = true := by
  decide +kernel

/-- Breakpoints of cells 897..909 of piece `zneg` (q = 6). -/
def q6F_zneg_069_b : List QF := [
  (-9633, 5120), (-4803, 2560), (-9579, 5120), (-597, 320),
  (-1905, 1024), (-4749, 2560), (-9471, 5120), (-2361, 1280),
  (-9417, 5120), (-939, 512), (-9363, 5120), (-1167, 640),
  (-9309, 5120), (-4641, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_069 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_069_b = true := by
  decide +kernel

/-- Breakpoints of cells 910..922 of piece `zneg` (q = 6). -/
def q6F_zneg_070_b : List QF := [
  (-4641, 2560), (-1851, 1024), (-2307, 1280), (-9201, 5120),
  (-4587, 2560), (-9147, 5120), (-57, 32), (-9093, 5120),
  (-4533, 2560), (-9039, 5120), (-2253, 1280), (-1797, 1024),
  (-4479, 2560), (-8931, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_070 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_070_b = true := by
  decide +kernel

/-- Breakpoints of cells 923..935 of piece `zneg` (q = 6). -/
def q6F_zneg_071_b : List QF := [
  (-8931, 5120), (-1113, 640), (-8877, 5120), (-885, 512),
  (-8823, 5120), (-2199, 1280), (-8769, 5120), (-4371, 2560),
  (-1743, 1024), (-543, 320), (-8661, 5120), (-4317, 2560),
  (-8607, 5120), (-429, 256)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_071 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_071_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
