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

/-- Breakpoints of cells 280..289 of piece `vlo` (q = 4). -/
def q4F_vlo_028_b : List QF := [
  (21223, 128000), (8519, 51200), (5343, 32000), (42893, 256000),
  (21521, 128000), (43191, 256000), (2167, 12800), (43489, 256000),
  (21819, 128000), (43787, 256000), (1373, 8000)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_028 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 290..299 of piece `vlo` (q = 4). -/
def q4F_vlo_029_b : List QF := [
  (1373, 8000), (8817, 51200), (22117, 128000), (44383, 256000),
  (11133, 64000), (44681, 256000), (4483, 25600), (44979, 256000),
  (5641, 32000), (45277, 256000), (22713, 128000)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_029 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_029_b = true := by
  decide +kernel

/-- Breakpoints of cells 300..309 of piece `vlo` (q = 4). -/
def q4F_vlo_030_b : List QF := [
  (22713, 128000), (1823, 10240), (11431, 64000), (45873, 256000),
  (23011, 128000), (46171, 256000), (579, 3200), (46469, 256000),
  (23309, 128000), (46767, 256000), (11729, 64000)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_030 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 310..319 of piece `vlo` (q = 4). -/
def q4F_vlo_031_b : List QF := [
  (11729, 64000), (9413, 51200), (23607, 128000), (47363, 256000),
  (5939, 32000), (4781, 25600), (12027, 64000), (24203, 128000),
  (761, 4000), (24501, 128000), (493, 2560)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_031 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 320..329 of piece `vlo` (q = 4). -/
def q4F_vlo_032_b : List QF := [
  (493, 2560), (24799, 128000), (6237, 32000), (25097, 128000),
  (50343, 256000), (12623, 64000), (50641, 256000), (5079, 25600),
  (50939, 256000), (3193, 16000), (51237, 256000)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_032 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 330..339 of piece `vlo` (q = 4). -/
def q4F_vlo_033_b : List QF := [
  (51237, 256000), (25693, 128000), (10307, 51200), (12921, 64000),
  (25991, 128000), (1307, 6400), (26289, 128000), (13219, 64000),
  (26587, 128000), (1671, 8000), (5377, 25600)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_033 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 340..349 of piece `vlo` (q = 4). -/
def q4F_vlo_034_b : List QF := [
  (5377, 25600), (13517, 64000), (27183, 128000), (6833, 32000),
  (27481, 128000), (2763, 12800), (27779, 128000), (3491, 16000),
  (28077, 128000), (14113, 64000), (227, 1024)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_034 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_034_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
