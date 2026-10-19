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

/-- Breakpoints of cells 168..173 of piece `arc2` (q = 2). -/
def q2F_arc2_028_b : List QF := [
  (21, 32), (169, 256), (85, 128), (171, 256),
  (43, 64), (173, 256), (87, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_028 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 174..179 of piece `arc2` (q = 2). -/
def q2F_arc2_029_b : List QF := [
  (87, 128), (175, 256), (11, 16), (177, 256),
  (89, 128), (179, 256), (45, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_029 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..185 of piece `arc2` (q = 2). -/
def q2F_arc2_030_b : List QF := [
  (45, 64), (181, 256), (91, 128), (183, 256),
  (23, 32), (185, 256), (93, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_030 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 186..191 of piece `arc2` (q = 2). -/
def q2F_arc2_031_b : List QF := [
  (93, 128), (187, 256), (47, 64), (189, 256),
  (95, 128), (191, 256), (3, 4)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_031 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 192..197 of piece `arc2` (q = 2). -/
def q2F_arc2_032_b : List QF := [
  (3, 4), (193, 256), (97, 128), (195, 256),
  (49, 64), (197, 256), (99, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_032 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 198..203 of piece `arc2` (q = 2). -/
def q2F_arc2_033_b : List QF := [
  (99, 128), (199, 256), (25, 32), (201, 256),
  (101, 128), (203, 256), (51, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_033 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 204..209 of piece `arc2` (q = 2). -/
def q2F_arc2_034_b : List QF := [
  (51, 64), (205, 256), (103, 128), (207, 256),
  (13, 16), (209, 256), (105, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_034 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_034_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
