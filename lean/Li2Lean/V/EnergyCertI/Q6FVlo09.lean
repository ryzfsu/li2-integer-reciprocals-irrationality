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

/-- Breakpoints of cells 630..639 of piece `vlo` (q = 6). -/
def q6F_vlo_063_b : List QF := [
  (71287, 128000), (17859, 32000), (14317, 25600), (35867, 64000),
  (71883, 128000), (2251, 4000), (72181, 128000), (7233, 12800),
  (72479, 128000), (18157, 32000), (72777, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_063 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 640..649 of piece `vlo` (q = 6). -/
def q6F_vlo_064_b : List QF := [
  (72777, 128000), (36463, 64000), (2923, 5120), (9153, 16000),
  (73373, 128000), (36761, 64000), (73671, 128000), (3691, 6400),
  (73969, 128000), (37059, 64000), (74267, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_064 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..659 of piece `vlo` (q = 6). -/
def q6F_vlo_065_b : List QF := [
  (74267, 128000), (4651, 8000), (14913, 25600), (37357, 64000),
  (74863, 128000), (18753, 32000), (75161, 128000), (7531, 12800),
  (75459, 128000), (9451, 16000), (75757, 128000)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vlo_065 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_065_b = true := by
  decide +kernel

/-- Breakpoints of cells 660..666 of piece `vlo` (q = 6). -/
def q6F_vlo_066_b : List QF := [
  (75757, 128000), (37953, 64000), (15211, 25600), (19051, 32000),
  (76353, 128000), (38251, 64000), (76651, 128000), (3, 5)]

/-- 7 cells, about 1561 transcendental evaluations (field mode). -/
theorem q6F_vlo_066 :
    cellsOK (fieldUB q6D 6 vLogRF .vlo) (kvQ 6) q6F_vlo_066_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
