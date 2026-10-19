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

/-- Breakpoints of cells 0..5 of piece `arc1` (q = 4). -/
def q4F_arc1_000_b : List QF := [
  (0, 1), (1, 8), (1, 4), (5, 16),
  (11, 32), (3, 8), (25, 64)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_000 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 6..11 of piece `arc1` (q = 4). -/
def q4F_arc1_001_b : List QF := [
  (25, 64), (13, 32), (53, 128), (27, 64),
  (109, 256), (55, 128), (111, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_001 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..17 of piece `arc1` (q = 4). -/
def q4F_arc1_002_b : List QF := [
  (111, 256), (7, 16), (113, 256), (57, 128),
  (115, 256), (29, 64), (117, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_002 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 18..23 of piece `arc1` (q = 4). -/
def q4F_arc1_003_b : List QF := [
  (117, 256), (59, 128), (119, 256), (15, 32),
  (121, 256), (61, 128), (123, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_003 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..29 of piece `arc1` (q = 4). -/
def q4F_arc1_004_b : List QF := [
  (123, 256), (31, 64), (125, 256), (63, 128),
  (127, 256), (1, 2), (129, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_004 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..35 of piece `arc1` (q = 4). -/
def q4F_arc1_005_b : List QF := [
  (129, 256), (65, 128), (131, 256), (33, 64),
  (133, 256), (67, 128), (135, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_005 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..41 of piece `arc1` (q = 4). -/
def q4F_arc1_006_b : List QF := [
  (135, 256), (17, 32), (137, 256), (69, 128),
  (139, 256), (35, 64), (141, 256)]

/-- 6 cells, about 2190 transcendental evaluations (field mode). -/
theorem q4F_arc1_006 :
    cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) q4F_arc1_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
