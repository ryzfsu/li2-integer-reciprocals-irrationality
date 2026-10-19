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

/-- Breakpoints of cells 360..369 of piece `vlo` (q = 2). -/
def q2F_vlo_036_b : List QF := [
  (5377, 25600), (53919, 256000), (13517, 64000), (27183, 128000),
  (6833, 32000), (27481, 128000), (2763, 12800), (27779, 128000),
  (3491, 16000), (28077, 128000), (14113, 64000)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_036 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 370..379 of piece `vlo` (q = 2). -/
def q2F_vlo_037_b : List QF := [
  (14113, 64000), (227, 1024), (7131, 32000), (28673, 128000),
  (11499, 51200), (14411, 64000), (57793, 256000), (28971, 128000),
  (58091, 256000), (91, 400), (58389, 256000)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_037 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 380..389 of piece `vlo` (q = 2). -/
def q2F_vlo_038_b : List QF := [
  (58389, 256000), (29269, 128000), (14709, 64000), (29567, 128000),
  (7429, 32000), (5973, 25600), (15007, 64000), (30163, 128000),
  (3789, 16000), (30461, 128000), (3061, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_038 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 390..399 of piece `vlo` (q = 2). -/
def q2F_vlo_039_b : List QF := [
  (3061, 12800), (30759, 128000), (7727, 32000), (31057, 128000),
  (15603, 64000), (6271, 25600), (1969, 8000), (31653, 128000),
  (15901, 64000), (31951, 128000), (321, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_039 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 400..409 of piece `vlo` (q = 2). -/
def q2F_vlo_040_b : List QF := [
  (321, 1280), (32249, 128000), (16199, 64000), (32547, 128000),
  (4087, 16000), (6569, 25600), (16497, 64000), (33143, 128000),
  (8323, 32000), (33441, 128000), (3359, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_040 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 410..419 of piece `vlo` (q = 2). -/
def q2F_vlo_041_b : List QF := [
  (3359, 12800), (33739, 128000), (1059, 4000), (34037, 128000),
  (17093, 64000), (6867, 25600), (8621, 32000), (34633, 128000),
  (17391, 64000), (34931, 128000), (877, 3200)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_041 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
