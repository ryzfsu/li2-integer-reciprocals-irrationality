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

/-- Breakpoints of cells 0..12 of piece `zneg` (q = 5). -/
def q5F_zneg_000_b : List QF := [
  (-5, 1), (-204789, 40960), (-102389, 20480), (-204767, 40960),
  (-51189, 10240), (-102367, 20480), (-25589, 5120), (-20469, 4096),
  (-51167, 10240), (-102323, 20480), (-12789, 2560), (-102301, 20480),
  (-10229, 2048), (-102279, 20480)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_000 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 13..25 of piece `zneg` (q = 5). -/
def q5F_zneg_001_b : List QF := [
  (-102279, 20480), (-25567, 5120), (-102257, 20480), (-51123, 10240),
  (-20447, 4096), (-6389, 1280), (-102213, 20480), (-51101, 10240),
  (-5109, 1024), (-51079, 10240), (-12767, 2560), (-51057, 10240),
  (-25523, 5120), (-10207, 2048)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_001 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 26..38 of piece `zneg` (q = 5). -/
def q5F_zneg_002_b : List QF := [
  (-10207, 2048), (-3189, 640), (-51013, 10240), (-25501, 5120),
  (-50991, 10240), (-2549, 512), (-50969, 10240), (-25479, 5120),
  (-50947, 10240), (-6367, 1280), (-10185, 2048), (-25457, 5120),
  (-50903, 10240), (-12723, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_002 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 39..51 of piece `zneg` (q = 5). -/
def q5F_zneg_003_b : List QF := [
  (-12723, 2560), (-50881, 10240), (-5087, 1024), (-50859, 10240),
  (-1589, 320), (-50837, 10240), (-25413, 5120), (-12701, 2560),
  (-25391, 5120), (-50771, 10240), (-1269, 256), (-50749, 10240),
  (-25369, 5120), (-50727, 10240)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_003 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 52..64 of piece `zneg` (q = 5). -/
def q5F_zneg_004_b : List QF := [
  (-50727, 10240), (-12679, 2560), (-10141, 2048), (-25347, 5120),
  (-50683, 10240), (-3167, 640), (-50661, 10240), (-5065, 1024),
  (-12657, 2560), (-25303, 5120), (-6323, 1280), (-25281, 5120),
  (-2527, 512), (-25259, 5120)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_004 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 65..77 of piece `zneg` (q = 5). -/
def q5F_zneg_005_b : List QF := [
  (-25259, 5120), (-789, 160), (-25237, 5120), (-12613, 2560),
  (-5043, 1024), (-6301, 1280), (-25193, 5120), (-12591, 2560),
  (-25171, 5120), (-629, 128), (-25149, 5120), (-12569, 2560),
  (-25127, 5120), (-6279, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_005 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_005_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
