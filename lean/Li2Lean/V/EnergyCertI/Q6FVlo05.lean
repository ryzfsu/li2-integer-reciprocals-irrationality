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

/-- Breakpoints of cells 350..359 of piece `vlo` (q = 6). -/
def q6F_vlo_035_b : List QF := [
  (29567, 128000), (7429, 32000), (5973, 25600), (15007, 64000),
  (30163, 128000), (3789, 16000), (30461, 128000), (3061, 12800),
  (30759, 128000), (7727, 32000), (31057, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_035 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 360..369 of piece `vlo` (q = 6). -/
def q6F_vlo_036_b : List QF := [
  (31057, 128000), (15603, 64000), (6271, 25600), (1969, 8000),
  (31653, 128000), (15901, 64000), (31951, 128000), (321, 1280),
  (32249, 128000), (16199, 64000), (32547, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_036 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 370..379 of piece `vlo` (q = 6). -/
def q6F_vlo_037_b : List QF := [
  (32547, 128000), (4087, 16000), (6569, 25600), (16497, 64000),
  (33143, 128000), (8323, 32000), (33441, 128000), (3359, 12800),
  (33739, 128000), (1059, 4000), (34037, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_037 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 380..389 of piece `vlo` (q = 6). -/
def q6F_vlo_038_b : List QF := [
  (34037, 128000), (17093, 64000), (6867, 25600), (8621, 32000),
  (34633, 128000), (17391, 64000), (34931, 128000), (877, 3200),
  (35229, 128000), (17689, 64000), (35527, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_038 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 390..399 of piece `vlo` (q = 6). -/
def q6F_vlo_039_b : List QF := [
  (35527, 128000), (8919, 32000), (1433, 5120), (17987, 64000),
  (36123, 128000), (2267, 8000), (36421, 128000), (3657, 12800),
  (36719, 128000), (9217, 32000), (37017, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_039 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 400..409 of piece `vlo` (q = 6). -/
def q6F_vlo_040_b : List QF := [
  (37017, 128000), (18583, 64000), (7463, 25600), (4683, 16000),
  (37613, 128000), (18881, 64000), (37911, 128000), (1903, 6400),
  (38209, 128000), (19179, 64000), (38507, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_040 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 410..419 of piece `vlo` (q = 6). -/
def q6F_vlo_041_b : List QF := [
  (38507, 128000), (151, 500), (7761, 25600), (19477, 64000),
  (39103, 128000), (9813, 32000), (39401, 128000), (791, 2560),
  (39699, 128000), (4981, 16000), (39997, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_041 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
