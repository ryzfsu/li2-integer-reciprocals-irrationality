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

/-- Breakpoints of cells 0..5 of piece `arc1` (q = 2). -/
def q2F_arc1_000_b : List QF := [
  (0, 1), (1, 8), (3, 16), (1, 4),
  (9, 32), (19, 64), (5, 16)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_000 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 6..11 of piece `arc1` (q = 2). -/
def q2F_arc1_001_b : List QF := [
  (5, 16), (41, 128), (21, 64), (43, 128),
  (11, 32), (89, 256), (45, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_001 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..17 of piece `arc1` (q = 2). -/
def q2F_arc1_002_b : List QF := [
  (45, 128), (91, 256), (23, 64), (93, 256),
  (187, 512), (47, 128), (189, 512)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_002 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 18..23 of piece `arc1` (q = 2). -/
def q2F_arc1_003_b : List QF := [
  (189, 512), (95, 256), (191, 512), (3, 8),
  (193, 512), (97, 256), (195, 512)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_003 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..29 of piece `arc1` (q = 2). -/
def q2F_arc1_004_b : List QF := [
  (195, 512), (49, 128), (197, 512), (99, 256),
  (199, 512), (25, 64), (101, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_004 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..35 of piece `arc1` (q = 2). -/
def q2F_arc1_005_b : List QF := [
  (101, 256), (51, 128), (103, 256), (13, 32),
  (105, 256), (53, 128), (107, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_005 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..41 of piece `arc1` (q = 2). -/
def q2F_arc1_006_b : List QF := [
  (107, 256), (27, 64), (109, 256), (55, 128),
  (111, 256), (7, 16), (113, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_006 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
