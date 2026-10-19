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

/-- Breakpoints of cells 120..129 of piece `vlo` (q = 2). -/
def q2F_vlo_012_b : List QF := [
  (1801, 25600), (18159, 256000), (4577, 64000), (18457, 256000),
  (9303, 128000), (3751, 51200), (2363, 32000), (19053, 256000),
  (9601, 128000), (19351, 256000), (39, 512)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_012 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..139 of piece `vlo` (q = 2). -/
def q2F_vlo_013_b : List QF := [
  (39, 512), (19649, 256000), (9899, 128000), (19947, 256000),
  (157, 2000), (4049, 51200), (10197, 128000), (20543, 256000),
  (5173, 64000), (20841, 256000), (2099, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_013 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_013_b = true := by
  decide +kernel

/-- Breakpoints of cells 140..149 of piece `vlo` (q = 2). -/
def q2F_vlo_014_b : List QF := [
  (2099, 25600), (21139, 256000), (2661, 32000), (21437, 256000),
  (10793, 128000), (4347, 51200), (5471, 64000), (22033, 256000),
  (11091, 128000), (22331, 256000), (281, 3200)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_014 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..159 of piece `vlo` (q = 2). -/
def q2F_vlo_015_b : List QF := [
  (281, 3200), (22629, 256000), (11389, 128000), (22927, 256000),
  (5769, 64000), (929, 10240), (11687, 128000), (23523, 256000),
  (2959, 32000), (23821, 256000), (2397, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_015 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 160..169 of piece `vlo` (q = 2). -/
def q2F_vlo_016_b : List QF := [
  (2397, 25600), (24119, 256000), (6067, 64000), (24417, 256000),
  (12283, 128000), (4943, 51200), (777, 8000), (25013, 256000),
  (12581, 128000), (25311, 256000), (1273, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_016 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 170..179 of piece `vlo` (q = 2). -/
def q2F_vlo_017_b : List QF := [
  (1273, 12800), (25609, 256000), (12879, 128000), (25907, 256000),
  (3257, 32000), (5241, 51200), (13177, 128000), (26503, 256000),
  (6663, 64000), (26801, 256000), (539, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_017 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_017_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
