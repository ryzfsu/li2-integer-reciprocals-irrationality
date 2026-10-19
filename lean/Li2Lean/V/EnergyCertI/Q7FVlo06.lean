/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 420..429 of piece `vlo` (q = 7). -/
def q7F_vlo_042_b : List QF := [
  (40891, 128000), (513, 1600), (41189, 128000), (20669, 64000),
  (41487, 128000), (10409, 32000), (8357, 25600), (20967, 64000),
  (42083, 128000), (5279, 16000), (42381, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_042 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 430..439 of piece `vlo` (q = 7). -/
def q7F_vlo_043_b : List QF := [
  (42381, 128000), (4253, 12800), (42679, 128000), (10707, 32000),
  (42977, 128000), (21563, 64000), (1731, 5120), (1357, 4000),
  (43573, 128000), (21861, 64000), (43871, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_043 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 440..449 of piece `vlo` (q = 7). -/
def q7F_vlo_044_b : List QF := [
  (43871, 128000), (2201, 6400), (44169, 128000), (22159, 64000),
  (44467, 128000), (5577, 16000), (8953, 25600), (22457, 64000),
  (45063, 128000), (11303, 32000), (45361, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_044 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 450..459 of piece `vlo` (q = 7). -/
def q7F_vlo_045_b : List QF := [
  (45361, 128000), (4551, 12800), (45659, 128000), (2863, 8000),
  (45957, 128000), (23053, 64000), (9251, 25600), (11601, 32000),
  (46553, 128000), (23351, 64000), (46851, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_045 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 460..469 of piece `vlo` (q = 7). -/
def q7F_vlo_046_b : List QF := [
  (46851, 128000), (47, 128), (47149, 128000), (23649, 64000),
  (47447, 128000), (11899, 32000), (9549, 25600), (23947, 64000),
  (48043, 128000), (753, 2000), (48341, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_046 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 470..479 of piece `vlo` (q = 7). -/
def q7F_vlo_047_b : List QF := [
  (48341, 128000), (4849, 12800), (48639, 128000), (12197, 32000),
  (48937, 128000), (24543, 64000), (9847, 25600), (6173, 16000),
  (49533, 128000), (24841, 64000), (49831, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_047 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_047_b = true := by
  decide +kernel

/-- Breakpoints of cells 480..489 of piece `vlo` (q = 7). -/
def q7F_vlo_048_b : List QF := [
  (49831, 128000), (2499, 6400), (50129, 128000), (25139, 64000),
  (50427, 128000), (3161, 8000), (2029, 5120), (25437, 64000),
  (51023, 128000), (12793, 32000), (51321, 128000)]

/-- 10 cells, about 2200 transcendental evaluations (field mode). -/
theorem q7F_vlo_048 :
    cellsOK (fieldUB q7D 7 vLogRF .vlo) (kvQ 7) q7F_vlo_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
