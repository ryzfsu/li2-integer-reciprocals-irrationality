/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 630..639 of piece `vlo` (q = 3). -/
def q3F_vlo_063_b : List QF := [
  (9153, 16000), (73373, 128000), (36761, 64000), (73671, 128000),
  (3691, 6400), (73969, 128000), (37059, 64000), (74267, 128000),
  (4651, 8000), (14913, 25600), (37357, 64000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_063 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 640..649 of piece `vlo` (q = 3). -/
def q3F_vlo_064_b : List QF := [
  (37357, 64000), (74863, 128000), (18753, 32000), (75161, 128000),
  (7531, 12800), (75459, 128000), (9451, 16000), (75757, 128000),
  (37953, 64000), (15211, 25600), (19051, 32000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_064 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..653 of piece `vlo` (q = 3). -/
def q3F_vlo_065_b : List QF := [
  (19051, 32000), (76353, 128000), (38251, 64000), (76651, 128000),
  (3, 5)]

/-- 4 cells, about 912 transcendental evaluations (field mode). -/
theorem q3F_vlo_065 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
