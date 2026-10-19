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

/-- Breakpoints of cells 84..89 of piece `arc1` (q = 5). -/
def q5F_arc1_014_b : List QF := [
  (193, 256), (97, 128), (195, 256), (49, 64),
  (197, 256), (99, 128), (199, 256)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_014 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..95 of piece `arc1` (q = 5). -/
def q5F_arc1_015_b : List QF := [
  (199, 256), (25, 32), (201, 256), (101, 128),
  (203, 256), (51, 64), (205, 256)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_015 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..101 of piece `arc1` (q = 5). -/
def q5F_arc1_016_b : List QF := [
  (205, 256), (103, 128), (207, 256), (13, 16),
  (209, 256), (105, 128), (211, 256)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_016 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 102..107 of piece `arc1` (q = 5). -/
def q5F_arc1_017_b : List QF := [
  (211, 256), (53, 64), (213, 256), (107, 128),
  (215, 256), (27, 32), (109, 128)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_017 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..113 of piece `arc1` (q = 5). -/
def q5F_arc1_018_b : List QF := [
  (109, 128), (219, 256), (55, 64), (221, 256),
  (111, 128), (7, 8), (113, 128)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_018 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 114..119 of piece `arc1` (q = 5). -/
def q5F_arc1_019_b : List QF := [
  (113, 128), (227, 256), (57, 64), (229, 256),
  (115, 128), (29, 32), (117, 128)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_019 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..125 of piece `arc1` (q = 5). -/
def q5F_arc1_020_b : List QF := [
  (117, 128), (59, 64), (119, 128), (15, 16),
  (121, 128), (61, 64), (123, 128)]

/-- 6 cells, about 2166 transcendental evaluations (field mode). -/
theorem q5F_arc1_020 :
    cellsOK (fieldUB q5D 5 vLogRF .arc1) (kzQ 5) q5F_arc1_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
