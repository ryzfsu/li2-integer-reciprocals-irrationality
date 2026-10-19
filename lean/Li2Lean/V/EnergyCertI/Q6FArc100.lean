/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..5 of piece `arc1` (q = 6). -/
def q6F_arc1_000_b : List QF := [
  (0, 1), (1, 4), (5, 16), (3, 8),
  (13, 32), (7, 16), (29, 64)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_000 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 6..11 of piece `arc1` (q = 6). -/
def q6F_arc1_001_b : List QF := [
  (29, 64), (59, 128), (15, 32), (61, 128),
  (31, 64), (125, 256), (63, 128)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_001 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..17 of piece `arc1` (q = 6). -/
def q6F_arc1_002_b : List QF := [
  (63, 128), (127, 256), (1, 2), (129, 256),
  (65, 128), (131, 256), (33, 64)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_002 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 18..23 of piece `arc1` (q = 6). -/
def q6F_arc1_003_b : List QF := [
  (33, 64), (133, 256), (67, 128), (135, 256),
  (17, 32), (137, 256), (69, 128)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_003 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..29 of piece `arc1` (q = 6). -/
def q6F_arc1_004_b : List QF := [
  (69, 128), (139, 256), (35, 64), (141, 256),
  (71, 128), (143, 256), (9, 16)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_004 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..35 of piece `arc1` (q = 6). -/
def q6F_arc1_005_b : List QF := [
  (9, 16), (145, 256), (73, 128), (147, 256),
  (37, 64), (149, 256), (75, 128)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_005 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..41 of piece `arc1` (q = 6). -/
def q6F_arc1_006_b : List QF := [
  (75, 128), (151, 256), (19, 32), (153, 256),
  (77, 128), (155, 256), (39, 64)]

/-- 6 cells, about 2130 transcendental evaluations (field mode). -/
theorem q6F_arc1_006 :
    cellsOK (fieldUB q6D 6 vLogRF .arc1) (kzQ 6) q6F_arc1_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
