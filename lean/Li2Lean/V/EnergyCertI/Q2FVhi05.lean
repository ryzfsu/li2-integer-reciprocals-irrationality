/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 300..309 of piece `vhi` (q = 2). -/
def q2F_vhi_030_b : List QF := [
  (267, 320), (1069, 1280), (107, 128), (1071, 1280),
  (67, 80), (1073, 1280), (537, 640), (215, 256),
  (269, 320), (1077, 1280), (539, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_030 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 310..319 of piece `vhi` (q = 2). -/
def q2F_vhi_031_b : List QF := [
  (539, 640), (1079, 1280), (27, 32), (1081, 1280),
  (541, 640), (1083, 1280), (271, 320), (217, 256),
  (543, 640), (1087, 1280), (17, 20)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_031 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 320..329 of piece `vhi` (q = 2). -/
def q2F_vhi_032_b : List QF := [
  (17, 20), (1089, 1280), (109, 128), (1091, 1280),
  (273, 320), (1093, 1280), (547, 640), (219, 256),
  (137, 160), (1097, 1280), (549, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_032 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 330..339 of piece `vhi` (q = 2). -/
def q2F_vhi_033_b : List QF := [
  (549, 640), (1099, 1280), (55, 64), (1101, 1280),
  (551, 640), (1103, 1280), (69, 80), (221, 256),
  (553, 640), (1107, 1280), (277, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_033 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 340..349 of piece `vhi` (q = 2). -/
def q2F_vhi_034_b : List QF := [
  (277, 320), (1109, 1280), (111, 128), (1111, 1280),
  (139, 160), (1113, 1280), (557, 640), (223, 256),
  (279, 320), (1117, 1280), (559, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_034 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_034_b = true := by
  decide +kernel

/-- Breakpoints of cells 350..359 of piece `vhi` (q = 2). -/
def q2F_vhi_035_b : List QF := [
  (559, 640), (1119, 1280), (7, 8), (1121, 1280),
  (561, 640), (1123, 1280), (281, 320), (225, 256),
  (563, 640), (1127, 1280), (141, 160)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_035 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_035_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
