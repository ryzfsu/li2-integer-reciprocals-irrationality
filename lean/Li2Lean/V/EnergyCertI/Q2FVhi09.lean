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

/-- Breakpoints of cells 540..549 of piece `vhi` (q = 2). -/
def q2F_vhi_054_b : List QF := [
  (77, 80), (493, 512), (1233, 1280), (2467, 2560),
  (617, 640), (2469, 2560), (247, 256), (2471, 2560),
  (309, 320), (2473, 2560), (1237, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_054 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 550..559 of piece `vhi` (q = 2). -/
def q2F_vhi_055_b : List QF := [
  (1237, 1280), (495, 512), (619, 640), (2477, 2560),
  (1239, 1280), (2479, 2560), (31, 32), (2481, 2560),
  (1241, 1280), (2483, 2560), (621, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_055 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_055_b = true := by
  decide +kernel

/-- Breakpoints of cells 560..569 of piece `vhi` (q = 2). -/
def q2F_vhi_056_b : List QF := [
  (621, 640), (497, 512), (1243, 1280), (2487, 2560),
  (311, 320), (2489, 2560), (249, 256), (2491, 2560),
  (623, 640), (2493, 2560), (1247, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_056 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 570..579 of piece `vhi` (q = 2). -/
def q2F_vhi_057_b : List QF := [
  (1247, 1280), (499, 512), (39, 40), (2497, 2560),
  (1249, 1280), (2499, 2560), (125, 128), (2501, 2560),
  (1251, 1280), (2503, 2560), (313, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_057 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 580..589 of piece `vhi` (q = 2). -/
def q2F_vhi_058_b : List QF := [
  (313, 320), (501, 512), (1253, 1280), (2507, 2560),
  (627, 640), (5017, 5120), (2509, 2560), (5019, 5120),
  (251, 256), (5021, 5120), (2511, 2560)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_058 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 590..599 of piece `vhi` (q = 2). -/
def q2F_vhi_059_b : List QF := [
  (2511, 2560), (5023, 5120), (157, 160), (1005, 1024),
  (2513, 2560), (5027, 5120), (1257, 1280), (5029, 5120),
  (503, 512), (5031, 5120), (629, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_059 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_059_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
