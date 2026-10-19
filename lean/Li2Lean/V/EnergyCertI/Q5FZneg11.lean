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

/-- Breakpoints of cells 858..870 of piece `zneg` (q = 5). -/
def q5F_zneg_066_b : List QF := [
  (-4451, 2560), (-111, 64), (-4429, 2560), (-2209, 1280),
  (-4407, 2560), (-1099, 640), (-877, 512), (-2187, 1280),
  (-4363, 2560), (-17, 10), (-4341, 2560), (-433, 256),
  (-4319, 2560), (-1077, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_066 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 871..883 of piece `zneg` (q = 5). -/
def q5F_zneg_067_b : List QF := [
  (-1077, 640), (-4297, 2560), (-2143, 1280), (-855, 512),
  (-533, 320), (-4253, 2560), (-2121, 1280), (-4231, 2560),
  (-211, 128), (-4209, 2560), (-2099, 1280), (-4187, 2560),
  (-261, 160), (-833, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_067 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_067_b = true := by
  decide +kernel

/-- Breakpoints of cells 884..896 of piece `zneg` (q = 5). -/
def q5F_zneg_068_b : List QF := [
  (-833, 512), (-2077, 1280), (-4143, 2560), (-1033, 640),
  (-4121, 2560), (-411, 256), (-4099, 2560), (-511, 320),
  (-4077, 2560), (-2033, 1280), (-811, 512), (-1011, 640),
  (-4033, 2560), (-2011, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_068 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_068_b = true := by
  decide +kernel

/-- Breakpoints of cells 897..909 of piece `zneg` (q = 5). -/
def q5F_zneg_069_b : List QF := [
  (-2011, 1280), (-4011, 2560), (-25, 16), (-3989, 2560),
  (-1989, 1280), (-3967, 2560), (-989, 640), (-789, 512),
  (-1967, 1280), (-3923, 2560), (-489, 320), (-3901, 2560),
  (-389, 256), (-3879, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_069 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_069_b = true := by
  decide +kernel

/-- Breakpoints of cells 910..922 of piece `zneg` (q = 5). -/
def q5F_zneg_070_b : List QF := [
  (-3879, 2560), (-967, 640), (-3857, 2560), (-1923, 1280),
  (-767, 512), (-239, 160), (-3813, 2560), (-1901, 1280),
  (-3791, 2560), (-189, 128), (-3769, 2560), (-1879, 1280),
  (-3747, 2560), (-467, 320)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_070 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_070_b = true := by
  decide +kernel

/-- Breakpoints of cells 923..935 of piece `zneg` (q = 5). -/
def q5F_zneg_071_b : List QF := [
  (-467, 320), (-745, 512), (-1857, 1280), (-3703, 2560),
  (-923, 640), (-3681, 2560), (-367, 256), (-3659, 2560),
  (-57, 40), (-3637, 2560), (-1813, 1280), (-723, 512),
  (-901, 640), (-3593, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_071 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_071_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
