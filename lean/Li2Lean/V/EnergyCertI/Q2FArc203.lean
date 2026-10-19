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

/-- Breakpoints of cells 126..131 of piece `arc2` (q = 2). -/
def q2F_arc2_021_b : List QF := [
  (63, 128), (127, 256), (1, 2), (129, 256),
  (65, 128), (131, 256), (33, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_021 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..137 of piece `arc2` (q = 2). -/
def q2F_arc2_022_b : List QF := [
  (33, 64), (133, 256), (67, 128), (135, 256),
  (17, 32), (137, 256), (69, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_022 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 138..143 of piece `arc2` (q = 2). -/
def q2F_arc2_023_b : List QF := [
  (69, 128), (139, 256), (35, 64), (141, 256),
  (71, 128), (143, 256), (9, 16)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_023 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..149 of piece `arc2` (q = 2). -/
def q2F_arc2_024_b : List QF := [
  (9, 16), (145, 256), (73, 128), (147, 256),
  (37, 64), (149, 256), (75, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_024 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..155 of piece `arc2` (q = 2). -/
def q2F_arc2_025_b : List QF := [
  (75, 128), (151, 256), (19, 32), (153, 256),
  (77, 128), (155, 256), (39, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_025 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..161 of piece `arc2` (q = 2). -/
def q2F_arc2_026_b : List QF := [
  (39, 64), (157, 256), (79, 128), (159, 256),
  (5, 8), (161, 256), (81, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_026 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 162..167 of piece `arc2` (q = 2). -/
def q2F_arc2_027_b : List QF := [
  (81, 128), (163, 256), (41, 64), (165, 256),
  (83, 128), (167, 256), (21, 32)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_027 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
