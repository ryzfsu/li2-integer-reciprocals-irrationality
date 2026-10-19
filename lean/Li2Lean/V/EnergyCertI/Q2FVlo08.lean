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

/-- Breakpoints of cells 480..489 of piece `vlo` (q = 2). -/
def q2F_vlo_048_b : List QF := [
  (2201, 6400), (44169, 128000), (22159, 64000), (44467, 128000),
  (5577, 16000), (8953, 25600), (22457, 64000), (45063, 128000),
  (11303, 32000), (45361, 128000), (4551, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_048 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_048_b = true := by
  decide +kernel

/-- Breakpoints of cells 490..499 of piece `vlo` (q = 2). -/
def q2F_vlo_049_b : List QF := [
  (4551, 12800), (45659, 128000), (2863, 8000), (45957, 128000),
  (23053, 64000), (9251, 25600), (11601, 32000), (46553, 128000),
  (23351, 64000), (46851, 128000), (47, 128)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_049 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 500..509 of piece `vlo` (q = 2). -/
def q2F_vlo_050_b : List QF := [
  (47, 128), (47149, 128000), (23649, 64000), (47447, 128000),
  (11899, 32000), (9549, 25600), (23947, 64000), (48043, 128000),
  (753, 2000), (48341, 128000), (4849, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_050 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 510..519 of piece `vlo` (q = 2). -/
def q2F_vlo_051_b : List QF := [
  (4849, 12800), (48639, 128000), (12197, 32000), (48937, 128000),
  (24543, 64000), (9847, 25600), (6173, 16000), (49533, 128000),
  (24841, 64000), (49831, 128000), (2499, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_051 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..529 of piece `vlo` (q = 2). -/
def q2F_vlo_052_b : List QF := [
  (2499, 6400), (50129, 128000), (25139, 64000), (50427, 128000),
  (3161, 8000), (2029, 5120), (25437, 64000), (51023, 128000),
  (12793, 32000), (51321, 128000), (5147, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_052 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 530..539 of piece `vlo` (q = 2). -/
def q2F_vlo_053_b : List QF := [
  (5147, 12800), (51619, 128000), (6471, 16000), (51917, 128000),
  (26033, 64000), (10443, 25600), (13091, 32000), (52513, 128000),
  (26331, 64000), (52811, 128000), (331, 800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_053 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_053_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
