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

/-- Breakpoints of cells 630..639 of piece `vlo` (q = 4). -/
def q4F_vlo_063_b : List QF := [
  (14019, 25600), (17561, 32000), (70393, 128000), (35271, 64000),
  (70691, 128000), (1771, 3200), (70989, 128000), (35569, 64000),
  (71287, 128000), (17859, 32000), (14317, 25600)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_063 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 640..649 of piece `vlo` (q = 4). -/
def q4F_vlo_064_b : List QF := [
  (14317, 25600), (35867, 64000), (71883, 128000), (2251, 4000),
  (72181, 128000), (7233, 12800), (72479, 128000), (18157, 32000),
  (72777, 128000), (36463, 64000), (2923, 5120)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_064 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..659 of piece `vlo` (q = 4). -/
def q4F_vlo_065_b : List QF := [
  (2923, 5120), (9153, 16000), (73373, 128000), (36761, 64000),
  (73671, 128000), (3691, 6400), (73969, 128000), (37059, 64000),
  (74267, 128000), (4651, 8000), (14913, 25600)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_065 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_065_b = true := by
  decide +kernel

/-- Breakpoints of cells 660..669 of piece `vlo` (q = 4). -/
def q4F_vlo_066_b : List QF := [
  (14913, 25600), (37357, 64000), (74863, 128000), (18753, 32000),
  (75161, 128000), (7531, 12800), (75459, 128000), (9451, 16000),
  (75757, 128000), (37953, 64000), (15211, 25600)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vlo_066 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 670..674 of piece `vlo` (q = 4). -/
def q4F_vlo_067_b : List QF := [
  (15211, 25600), (19051, 32000), (76353, 128000), (38251, 64000),
  (76651, 128000), (3, 5)]

/-- 5 cells, about 1135 transcendental evaluations (field mode). -/
theorem q4F_vlo_067 :
    cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) q4F_vlo_067_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
