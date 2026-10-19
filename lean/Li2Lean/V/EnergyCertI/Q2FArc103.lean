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

/-- Breakpoints of cells 126..131 of piece `arc1` (q = 2). -/
def q2F_arc1_021_b : List QF := [
  (197, 256), (99, 128), (199, 256), (25, 32),
  (201, 256), (101, 128), (203, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_021 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..137 of piece `arc1` (q = 2). -/
def q2F_arc1_022_b : List QF := [
  (203, 256), (51, 64), (205, 256), (103, 128),
  (207, 256), (13, 16), (209, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_022 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 138..143 of piece `arc1` (q = 2). -/
def q2F_arc1_023_b : List QF := [
  (209, 256), (105, 128), (211, 256), (53, 64),
  (213, 256), (107, 128), (215, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_023 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..149 of piece `arc1` (q = 2). -/
def q2F_arc1_024_b : List QF := [
  (215, 256), (27, 32), (217, 256), (109, 128),
  (219, 256), (55, 64), (221, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_024 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..155 of piece `arc1` (q = 2). -/
def q2F_arc1_025_b : List QF := [
  (221, 256), (111, 128), (223, 256), (7, 8),
  (225, 256), (113, 128), (227, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_025 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..161 of piece `arc1` (q = 2). -/
def q2F_arc1_026_b : List QF := [
  (227, 256), (57, 64), (229, 256), (115, 128),
  (231, 256), (29, 32), (233, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_026 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 162..167 of piece `arc1` (q = 2). -/
def q2F_arc1_027_b : List QF := [
  (233, 256), (117, 128), (235, 256), (59, 64),
  (237, 256), (119, 128), (239, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_027 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
