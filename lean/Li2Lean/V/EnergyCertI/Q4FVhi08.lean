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

/-- Breakpoints of cells 560..569 of piece `vhi` (q = 4). -/
def q4F_vhi_056_b : List QF := [
  (499, 512), (39, 40), (2497, 2560), (1249, 1280),
  (2499, 2560), (125, 128), (2501, 2560), (1251, 1280),
  (2503, 2560), (313, 320), (501, 512)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_056 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 570..579 of piece `vhi` (q = 4). -/
def q4F_vhi_057_b : List QF := [
  (501, 512), (1253, 1280), (2507, 2560), (627, 640),
  (2509, 2560), (5019, 5120), (251, 256), (5021, 5120),
  (2511, 2560), (5023, 5120), (157, 160)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_057 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 580..589 of piece `vhi` (q = 4). -/
def q4F_vhi_058_b : List QF := [
  (157, 160), (1005, 1024), (2513, 2560), (5027, 5120),
  (1257, 1280), (5029, 5120), (503, 512), (5031, 5120),
  (629, 640), (2517, 2560), (1259, 1280)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_058 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 590..599 of piece `vhi` (q = 4). -/
def q4F_vhi_059_b : List QF := [
  (1259, 1280), (2519, 2560), (63, 64), (2521, 2560),
  (1261, 1280), (2523, 2560), (631, 640), (5049, 5120),
  (505, 512), (5051, 5120), (1263, 1280)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_059 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_059_b = true := by
  decide +kernel

/-- Breakpoints of cells 600..609 of piece `vhi` (q = 4). -/
def q4F_vhi_060_b : List QF := [
  (1263, 1280), (5053, 5120), (2527, 2560), (1011, 1024),
  (79, 80), (5057, 5120), (2529, 2560), (5059, 5120),
  (253, 256), (5061, 5120), (2531, 2560)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_060 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 610..619 of piece `vhi` (q = 4). -/
def q4F_vhi_061_b : List QF := [
  (2531, 2560), (5063, 5120), (633, 640), (1013, 1024),
  (2533, 2560), (5067, 5120), (1267, 1280), (5069, 5120),
  (507, 512), (5071, 5120), (317, 320)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_061 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 620..629 of piece `vhi` (q = 4). -/
def q4F_vhi_062_b : List QF := [
  (317, 320), (5073, 5120), (2537, 2560), (1015, 1024),
  (1269, 1280), (5077, 5120), (2539, 2560), (5079, 5120),
  (127, 128), (5081, 5120), (2541, 2560)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_062 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_062_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
