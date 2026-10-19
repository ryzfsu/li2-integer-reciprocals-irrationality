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

/-- Breakpoints of cells 210..215 of piece `arc2` (q = 2). -/
def q2F_arc2_035_b : List QF := [
  (105, 128), (211, 256), (53, 64), (213, 256),
  (107, 128), (215, 256), (27, 32)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_035 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 216..221 of piece `arc2` (q = 2). -/
def q2F_arc2_036_b : List QF := [
  (27, 32), (217, 256), (109, 128), (219, 256),
  (55, 64), (221, 256), (111, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_036 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 222..227 of piece `arc2` (q = 2). -/
def q2F_arc2_037_b : List QF := [
  (111, 128), (223, 256), (7, 8), (225, 256),
  (113, 128), (227, 256), (57, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_037 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 228..233 of piece `arc2` (q = 2). -/
def q2F_arc2_038_b : List QF := [
  (57, 64), (229, 256), (115, 128), (231, 256),
  (29, 32), (233, 256), (117, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_038 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 234..239 of piece `arc2` (q = 2). -/
def q2F_arc2_039_b : List QF := [
  (117, 128), (235, 256), (59, 64), (237, 256),
  (119, 128), (239, 256), (15, 16)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_039 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..245 of piece `arc2` (q = 2). -/
def q2F_arc2_040_b : List QF := [
  (15, 16), (241, 256), (121, 128), (243, 256),
  (61, 64), (245, 256), (123, 128)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_040 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 246..251 of piece `arc2` (q = 2). -/
def q2F_arc2_041_b : List QF := [
  (123, 128), (247, 256), (31, 32), (249, 256),
  (125, 128), (251, 256), (63, 64)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc2_041 :
    cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) q2F_arc2_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
