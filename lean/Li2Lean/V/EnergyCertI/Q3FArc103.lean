/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 126..131 of piece `arc1` (q = 3). -/
def q3F_arc1_021_b : List QF := [
  (107, 128), (215, 256), (27, 32), (217, 256),
  (109, 128), (219, 256), (55, 64)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_021 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..137 of piece `arc1` (q = 3). -/
def q3F_arc1_022_b : List QF := [
  (55, 64), (221, 256), (111, 128), (223, 256),
  (7, 8), (225, 256), (113, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_022 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 138..143 of piece `arc1` (q = 3). -/
def q3F_arc1_023_b : List QF := [
  (113, 128), (227, 256), (57, 64), (229, 256),
  (115, 128), (231, 256), (29, 32)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_023 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..149 of piece `arc1` (q = 3). -/
def q3F_arc1_024_b : List QF := [
  (29, 32), (233, 256), (117, 128), (235, 256),
  (59, 64), (237, 256), (119, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_024 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..155 of piece `arc1` (q = 3). -/
def q3F_arc1_025_b : List QF := [
  (119, 128), (15, 16), (241, 256), (121, 128),
  (243, 256), (61, 64), (245, 256)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_025 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..161 of piece `arc1` (q = 3). -/
def q3F_arc1_026_b : List QF := [
  (245, 256), (123, 128), (31, 32), (125, 128),
  (251, 256), (63, 64), (253, 256)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc1_026 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 162..163 of piece `arc1` (q = 3). -/
def q3F_arc1_027_b : List QF := [
  (253, 256), (127, 128), (1, 1)]

/-- 2 cells, about 734 transcendental evaluations (field mode). -/
theorem q3F_arc1_027 :
    cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) q3F_arc1_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
