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

/-- Breakpoints of cells 0..5 of piece `arc2` (q = 3). -/
def q3F_arc2_000_b : List QF := [
  (0, 1), (1, 256), (1, 128), (3, 256),
  (1, 64), (5, 256), (3, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_000 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 6..11 of piece `arc2` (q = 3). -/
def q3F_arc2_001_b : List QF := [
  (3, 128), (7, 256), (1, 32), (9, 256),
  (5, 128), (11, 256), (3, 64)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_001 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..17 of piece `arc2` (q = 3). -/
def q3F_arc2_002_b : List QF := [
  (3, 64), (13, 256), (7, 128), (15, 256),
  (1, 16), (17, 256), (9, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_002 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 18..23 of piece `arc2` (q = 3). -/
def q3F_arc2_003_b : List QF := [
  (9, 128), (19, 256), (5, 64), (21, 256),
  (11, 128), (23, 256), (3, 32)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_003 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..29 of piece `arc2` (q = 3). -/
def q3F_arc2_004_b : List QF := [
  (3, 32), (25, 256), (13, 128), (27, 256),
  (7, 64), (29, 256), (15, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_004 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..35 of piece `arc2` (q = 3). -/
def q3F_arc2_005_b : List QF := [
  (15, 128), (31, 256), (1, 8), (33, 256),
  (17, 128), (35, 256), (9, 64)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_005 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..41 of piece `arc2` (q = 3). -/
def q3F_arc2_006_b : List QF := [
  (9, 64), (37, 256), (19, 128), (39, 256),
  (5, 32), (41, 256), (21, 128)]

/-- 6 cells, about 2202 transcendental evaluations (field mode). -/
theorem q3F_arc2_006 :
    cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) q3F_arc2_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
