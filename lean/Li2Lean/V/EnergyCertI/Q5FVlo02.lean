/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 140..149 of piece `vlo` (q = 5). -/
def q5F_vlo_014_b : List QF := [
  (4347, 51200), (5471, 64000), (22033, 256000), (11091, 128000),
  (22331, 256000), (281, 3200), (22629, 256000), (11389, 128000),
  (22927, 256000), (5769, 64000), (929, 10240)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_014 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..159 of piece `vlo` (q = 5). -/
def q5F_vlo_015_b : List QF := [
  (929, 10240), (11687, 128000), (23523, 256000), (2959, 32000),
  (23821, 256000), (2397, 25600), (24119, 256000), (6067, 64000),
  (24417, 256000), (12283, 128000), (4943, 51200)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_015 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 160..169 of piece `vlo` (q = 5). -/
def q5F_vlo_016_b : List QF := [
  (4943, 51200), (777, 8000), (25013, 256000), (12581, 128000),
  (25311, 256000), (1273, 12800), (25609, 256000), (12879, 128000),
  (25907, 256000), (3257, 32000), (5241, 51200)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_016 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 170..179 of piece `vlo` (q = 5). -/
def q5F_vlo_017_b : List QF := [
  (5241, 51200), (13177, 128000), (26503, 256000), (6663, 64000),
  (26801, 256000), (539, 5120), (27099, 256000), (1703, 16000),
  (27397, 256000), (13773, 128000), (5539, 51200)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_017 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..189 of piece `vlo` (q = 5). -/
def q5F_vlo_018_b : List QF := [
  (5539, 51200), (6961, 64000), (27993, 256000), (14071, 128000),
  (28291, 256000), (711, 6400), (28589, 256000), (14369, 128000),
  (28887, 256000), (7259, 64000), (5837, 51200)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_018 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 190..199 of piece `vlo` (q = 5). -/
def q5F_vlo_019_b : List QF := [
  (5837, 51200), (14667, 128000), (29483, 256000), (463, 4000),
  (29781, 256000), (2993, 25600), (30079, 256000), (7557, 64000),
  (30377, 256000), (15263, 128000), (1227, 10240)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_019 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 200..209 of piece `vlo` (q = 5). -/
def q5F_vlo_020_b : List QF := [
  (1227, 10240), (3853, 32000), (30973, 256000), (15561, 128000),
  (31271, 256000), (1571, 12800), (31569, 256000), (15859, 128000),
  (31867, 256000), (2001, 16000), (6433, 51200)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vlo_020 :
    cellsOK (fieldUB q5D 5 vLogRF .vlo) (kvQ 5) q5F_vlo_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
