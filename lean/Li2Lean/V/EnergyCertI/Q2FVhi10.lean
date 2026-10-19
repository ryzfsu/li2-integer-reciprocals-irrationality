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

/-- Breakpoints of cells 600..609 of piece `vhi` (q = 2). -/
def q2F_vhi_060_b : List QF := [
  (629, 640), (2517, 2560), (1259, 1280), (2519, 2560),
  (63, 64), (2521, 2560), (1261, 1280), (2523, 2560),
  (5047, 5120), (631, 640), (5049, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_060 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 610..619 of piece `vhi` (q = 2). -/
def q2F_vhi_061_b : List QF := [
  (5049, 5120), (505, 512), (5051, 5120), (1263, 1280),
  (5053, 5120), (2527, 2560), (1011, 1024), (79, 80),
  (5057, 5120), (2529, 2560), (5059, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_061 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 620..629 of piece `vhi` (q = 2). -/
def q2F_vhi_062_b : List QF := [
  (5059, 5120), (253, 256), (5061, 5120), (2531, 2560),
  (5063, 5120), (633, 640), (1013, 1024), (2533, 2560),
  (5067, 5120), (1267, 1280), (5069, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_062 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_062_b = true := by
  decide +kernel

/-- Breakpoints of cells 630..639 of piece `vhi` (q = 2). -/
def q2F_vhi_063_b : List QF := [
  (5069, 5120), (507, 512), (5071, 5120), (317, 320),
  (5073, 5120), (2537, 2560), (1015, 1024), (1269, 1280),
  (5077, 5120), (2539, 2560), (5079, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_063 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 640..649 of piece `vhi` (q = 2). -/
def q2F_vhi_064_b : List QF := [
  (5079, 5120), (127, 128), (5081, 5120), (2541, 2560),
  (5083, 5120), (1271, 1280), (1017, 1024), (2543, 2560),
  (5087, 5120), (159, 160), (5089, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_064 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..659 of piece `vhi` (q = 2). -/
def q2F_vhi_065_b : List QF := [
  (5089, 5120), (509, 512), (5091, 5120), (1273, 1280),
  (5093, 5120), (2547, 2560), (1019, 1024), (637, 640),
  (5097, 5120), (2549, 2560), (5099, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_065 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
