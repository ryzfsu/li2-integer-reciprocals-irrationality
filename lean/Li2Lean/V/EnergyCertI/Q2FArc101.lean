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

/-- Breakpoints of cells 42..47 of piece `arc1` (q = 2). -/
def q2F_arc1_007_b : List QF := [
  (113, 256), (57, 128), (115, 256), (29, 64),
  (117, 256), (59, 128), (119, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_007 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..53 of piece `arc1` (q = 2). -/
def q2F_arc1_008_b : List QF := [
  (119, 256), (15, 32), (121, 256), (61, 128),
  (123, 256), (31, 64), (125, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_008 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 54..59 of piece `arc1` (q = 2). -/
def q2F_arc1_009_b : List QF := [
  (125, 256), (63, 128), (127, 256), (1, 2),
  (129, 256), (65, 128), (131, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_009 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..65 of piece `arc1` (q = 2). -/
def q2F_arc1_010_b : List QF := [
  (131, 256), (33, 64), (133, 256), (67, 128),
  (135, 256), (17, 32), (137, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_010 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 66..71 of piece `arc1` (q = 2). -/
def q2F_arc1_011_b : List QF := [
  (137, 256), (69, 128), (139, 256), (35, 64),
  (141, 256), (71, 128), (143, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_011 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..77 of piece `arc1` (q = 2). -/
def q2F_arc1_012_b : List QF := [
  (143, 256), (9, 16), (145, 256), (73, 128),
  (147, 256), (37, 64), (149, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_012 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 78..83 of piece `arc1` (q = 2). -/
def q2F_arc1_013_b : List QF := [
  (149, 256), (75, 128), (151, 256), (19, 32),
  (153, 256), (77, 128), (155, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_013 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
