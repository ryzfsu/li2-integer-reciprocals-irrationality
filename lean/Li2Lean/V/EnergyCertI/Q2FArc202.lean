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

/-- Breakpoints of cells 84..89 of piece `arc2` (q = 2). -/
def q2F_arc2_014_b : List QF := [
  (21, 64), (85, 256), (43, 128), (87, 256),
  (11, 32), (89, 256), (45, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_014 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..95 of piece `arc2` (q = 2). -/
def q2F_arc2_015_b : List QF := [
  (45, 128), (91, 256), (23, 64), (93, 256),
  (47, 128), (95, 256), (3, 8)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_015 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..101 of piece `arc2` (q = 2). -/
def q2F_arc2_016_b : List QF := [
  (3, 8), (97, 256), (49, 128), (99, 256),
  (25, 64), (101, 256), (51, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_016 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 102..107 of piece `arc2` (q = 2). -/
def q2F_arc2_017_b : List QF := [
  (51, 128), (103, 256), (13, 32), (105, 256),
  (53, 128), (107, 256), (27, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_017 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..113 of piece `arc2` (q = 2). -/
def q2F_arc2_018_b : List QF := [
  (27, 64), (109, 256), (55, 128), (111, 256),
  (7, 16), (113, 256), (57, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_018 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 114..119 of piece `arc2` (q = 2). -/
def q2F_arc2_019_b : List QF := [
  (57, 128), (115, 256), (29, 64), (117, 256),
  (59, 128), (119, 256), (15, 32)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_019 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..125 of piece `arc2` (q = 2). -/
def q2F_arc2_020_b : List QF := [
  (15, 32), (121, 256), (61, 128), (123, 256),
  (31, 64), (125, 256), (63, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_020 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
