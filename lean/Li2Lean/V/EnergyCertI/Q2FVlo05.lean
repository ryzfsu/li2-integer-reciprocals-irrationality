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

/-- Breakpoints of cells 300..309 of piece `vlo` (q = 2). -/
def q2F_vlo_030_b : List QF := [
  (4483, 25600), (44979, 256000), (5641, 32000), (45277, 256000),
  (22713, 128000), (1823, 10240), (11431, 64000), (45873, 256000),
  (23011, 128000), (46171, 256000), (579, 3200)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_030 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 310..319 of piece `vlo` (q = 2). -/
def q2F_vlo_031_b : List QF := [
  (579, 3200), (46469, 256000), (23309, 128000), (46767, 256000),
  (11729, 64000), (9413, 51200), (23607, 128000), (47363, 256000),
  (5939, 32000), (47661, 256000), (4781, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_031 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 320..329 of piece `vlo` (q = 2). -/
def q2F_vlo_032_b : List QF := [
  (4781, 25600), (47959, 256000), (12027, 64000), (48257, 256000),
  (24203, 128000), (9711, 51200), (761, 4000), (48853, 256000),
  (24501, 128000), (49151, 256000), (493, 2560)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_032 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 330..339 of piece `vlo` (q = 2). -/
def q2F_vlo_033_b : List QF := [
  (493, 2560), (49449, 256000), (24799, 128000), (49747, 256000),
  (6237, 32000), (10009, 51200), (25097, 128000), (50343, 256000),
  (12623, 64000), (50641, 256000), (5079, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_033 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 340..349 of piece `vlo` (q = 2). -/
def q2F_vlo_034_b : List QF := [
  (5079, 25600), (50939, 256000), (3193, 16000), (51237, 256000),
  (25693, 128000), (10307, 51200), (12921, 64000), (51833, 256000),
  (25991, 128000), (52131, 256000), (1307, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_034 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_034_b = true := by
  decide +kernel

/-- Breakpoints of cells 350..359 of piece `vlo` (q = 2). -/
def q2F_vlo_035_b : List QF := [
  (1307, 6400), (52429, 256000), (26289, 128000), (52727, 256000),
  (13219, 64000), (2121, 10240), (26587, 128000), (53323, 256000),
  (1671, 8000), (53621, 256000), (5377, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_035 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_035_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
