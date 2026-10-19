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

/-- Breakpoints of cells 42..47 of piece `arc2` (q = 3). -/
def q3F_arc2_007_b : List QF := [
  (21, 128), (43, 256), (11, 64), (45, 256),
  (23, 128), (47, 256), (3, 16)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_007 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..53 of piece `arc2` (q = 3). -/
def q3F_arc2_008_b : List QF := [
  (3, 16), (49, 256), (25, 128), (51, 256),
  (13, 64), (53, 256), (27, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_008 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 54..59 of piece `arc2` (q = 3). -/
def q3F_arc2_009_b : List QF := [
  (27, 128), (55, 256), (7, 32), (57, 256),
  (29, 128), (59, 256), (15, 64)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_009 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..65 of piece `arc2` (q = 3). -/
def q3F_arc2_010_b : List QF := [
  (15, 64), (61, 256), (31, 128), (63, 256),
  (1, 4), (65, 256), (33, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_010 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 66..71 of piece `arc2` (q = 3). -/
def q3F_arc2_011_b : List QF := [
  (33, 128), (67, 256), (17, 64), (69, 256),
  (35, 128), (71, 256), (9, 32)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_011 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..77 of piece `arc2` (q = 3). -/
def q3F_arc2_012_b : List QF := [
  (9, 32), (73, 256), (37, 128), (75, 256),
  (19, 64), (77, 256), (39, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_012 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 78..83 of piece `arc2` (q = 3). -/
def q3F_arc2_013_b : List QF := [
  (39, 128), (79, 256), (5, 16), (81, 256),
  (41, 128), (83, 256), (21, 64)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_013 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
