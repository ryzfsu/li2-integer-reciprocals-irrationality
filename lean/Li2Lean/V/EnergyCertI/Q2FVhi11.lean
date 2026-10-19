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

/-- Breakpoints of cells 660..669 of piece `vhi` (q = 2). -/
def q2F_vhi_066_b : List QF := [
  (5099, 5120), (255, 256), (5101, 5120), (2551, 2560),
  (5103, 5120), (319, 320), (1021, 1024), (2553, 2560),
  (10213, 10240), (5107, 5120), (2043, 2048)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_066 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 670..679 of piece `vhi` (q = 2). -/
def q2F_vhi_067_b : List QF := [
  (2043, 2048), (1277, 1280), (10217, 10240), (5109, 5120),
  (10219, 10240), (511, 512), (10221, 10240), (5111, 5120),
  (4089, 4096), (10223, 10240), (20447, 20480)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_067 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_067_b = true := by
  decide +kernel

/-- Breakpoints of cells 680..689 of piece `vhi` (q = 2). -/
def q2F_vhi_068_b : List QF := [
  (20447, 20480), (639, 640), (20449, 20480), (2045, 2048),
  (20451, 20480), (5113, 5120), (20453, 20480), (10227, 10240),
  (4091, 4096), (2557, 2560), (20457, 20480)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_068 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_068_b = true := by
  decide +kernel

/-- Breakpoints of cells 690..699 of piece `vhi` (q = 2). -/
def q2F_vhi_069_b : List QF := [
  (20457, 20480), (10229, 10240), (1023, 1024), (10231, 10240),
  (1279, 1280), (10233, 10240), (5117, 5120), (2047, 2048),
  (20471, 20480), (2559, 2560), (20473, 20480)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_069 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_069_b = true := by
  decide +kernel

/-- Breakpoints of cells 700..708 of piece `vhi` (q = 2). -/
def q2F_vhi_070_b : List QF := [
  (20473, 20480), (10237, 10240), (4095, 4096), (5119, 5120),
  (20477, 20480), (10239, 10240), (40957, 40960), (20479, 20480),
  (40959, 40960), (1, 1)]

/-- 9 cells, about 2088 transcendental evaluations (field mode). -/
theorem q2F_vhi_070 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_070_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
