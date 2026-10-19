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

/-- Breakpoints of cells 468..480 of piece `zneg` (q = 5). -/
def q5F_zneg_036_b : List QF := [
  (-8741, 2560), (-873, 256), (-8719, 2560), (-2177, 640),
  (-8697, 2560), (-4343, 1280), (-1735, 512), (-1083, 320),
  (-8653, 2560), (-4321, 1280), (-8631, 2560), (-431, 128),
  (-8609, 2560), (-4299, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_036 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 481..493 of piece `zneg` (q = 5). -/
def q5F_zneg_037_b : List QF := [
  (-4299, 1280), (-8587, 2560), (-67, 20), (-1713, 512),
  (-4277, 1280), (-8543, 2560), (-2133, 640), (-8521, 2560),
  (-851, 256), (-8499, 2560), (-1061, 320), (-8477, 2560),
  (-4233, 1280), (-1691, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_037 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 494..506 of piece `zneg` (q = 5). -/
def q5F_zneg_038_b : List QF := [
  (-1691, 512), (-2111, 640), (-8433, 2560), (-4211, 1280),
  (-8411, 2560), (-105, 32), (-8389, 2560), (-4189, 1280),
  (-8367, 2560), (-2089, 640), (-1669, 512), (-4167, 1280),
  (-8323, 2560), (-1039, 320)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_038 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 507..519 of piece `zneg` (q = 5). -/
def q5F_zneg_039_b : List QF := [
  (-1039, 320), (-8301, 2560), (-829, 256), (-8279, 2560),
  (-2067, 640), (-8257, 2560), (-4123, 1280), (-1647, 512),
  (-257, 80), (-8213, 2560), (-4101, 1280), (-8191, 2560),
  (-409, 128), (-8169, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_039 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..532 of piece `zneg` (q = 5). -/
def q5F_zneg_040_b : List QF := [
  (-8169, 2560), (-4079, 1280), (-8147, 2560), (-1017, 320),
  (-1625, 512), (-4057, 1280), (-8103, 2560), (-2023, 640),
  (-8081, 2560), (-807, 256), (-8059, 2560), (-503, 160),
  (-8037, 2560), (-4013, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_040 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 533..545 of piece `zneg` (q = 5). -/
def q5F_zneg_041_b : List QF := [
  (-4013, 1280), (-1603, 512), (-2001, 640), (-7993, 2560),
  (-3991, 1280), (-7971, 2560), (-199, 64), (-7949, 2560),
  (-3969, 1280), (-7927, 2560), (-1979, 640), (-1581, 512),
  (-3947, 1280), (-7883, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_041 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
