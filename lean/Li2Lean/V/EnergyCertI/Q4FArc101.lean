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

/-- Breakpoints of cells 42..47 of piece `arc1` (q = 4). -/
def q4F_arc1_007_b : List QF := [
  (141, 256), (71, 128), (143, 256), (9, 16),
  (145, 256), (73, 128), (147, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_007 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..53 of piece `arc1` (q = 4). -/
def q4F_arc1_008_b : List QF := [
  (147, 256), (37, 64), (149, 256), (75, 128),
  (151, 256), (19, 32), (153, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_008 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 54..59 of piece `arc1` (q = 4). -/
def q4F_arc1_009_b : List QF := [
  (153, 256), (77, 128), (155, 256), (39, 64),
  (157, 256), (79, 128), (159, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_009 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..65 of piece `arc1` (q = 4). -/
def q4F_arc1_010_b : List QF := [
  (159, 256), (5, 8), (161, 256), (81, 128),
  (163, 256), (41, 64), (165, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_010 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 66..71 of piece `arc1` (q = 4). -/
def q4F_arc1_011_b : List QF := [
  (165, 256), (83, 128), (167, 256), (21, 32),
  (169, 256), (85, 128), (171, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_011 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..77 of piece `arc1` (q = 4). -/
def q4F_arc1_012_b : List QF := [
  (171, 256), (43, 64), (173, 256), (87, 128),
  (175, 256), (11, 16), (177, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_012 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 78..83 of piece `arc1` (q = 4). -/
def q4F_arc1_013_b : List QF := [
  (177, 256), (89, 128), (179, 256), (45, 64),
  (181, 256), (91, 128), (183, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_013 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
