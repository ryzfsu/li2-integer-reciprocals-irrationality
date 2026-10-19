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

/-- Breakpoints of cells 0..9 of piece `vlo` (q = 3). -/
def q3F_vlo_000_b : List QF := [
  (1, 250), (81, 12800), (959, 128000), (277, 32000),
  (473, 51200), (1257, 128000), (2663, 256000), (703, 64000),
  (2961, 256000), (311, 25600), (3259, 256000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_000 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 10..19 of piece `vlo` (q = 3). -/
def q3F_vlo_001_b : List QF := [
  (3259, 256000), (213, 16000), (3557, 256000), (7263, 512000),
  (1853, 128000), (7561, 512000), (771, 51200), (7859, 512000),
  (1001, 64000), (8157, 512000), (4153, 256000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_001 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 20..29 of piece `vlo` (q = 3). -/
def q3F_vlo_002_b : List QF := [
  (4153, 256000), (1691, 102400), (2151, 128000), (8753, 512000),
  (4451, 256000), (23, 1280), (4749, 256000), (2449, 128000),
  (5047, 256000), (1299, 64000), (1069, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_002 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..39 of piece `vlo` (q = 3). -/
def q3F_vlo_003_b : List QF := [
  (1069, 51200), (2747, 128000), (5643, 256000), (181, 8000),
  (5941, 256000), (609, 25600), (6239, 256000), (1597, 64000),
  (6537, 256000), (3343, 128000), (1367, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_003 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 40..49 of piece `vlo` (q = 3). -/
def q3F_vlo_004_b : List QF := [
  (1367, 51200), (873, 32000), (7133, 256000), (3641, 128000),
  (7431, 256000), (379, 12800), (7729, 256000), (3939, 128000),
  (8027, 256000), (511, 16000), (333, 10240)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_004 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 50..59 of piece `vlo` (q = 3). -/
def q3F_vlo_005_b : List QF := [
  (333, 10240), (4237, 128000), (8623, 256000), (2193, 64000),
  (8921, 256000), (907, 25600), (9219, 256000), (1171, 32000),
  (9517, 256000), (4833, 128000), (1963, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_005 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..69 of piece `vlo` (q = 3). -/
def q3F_vlo_006_b : List QF := [
  (1963, 51200), (2491, 64000), (10113, 256000), (5131, 128000),
  (10411, 256000), (33, 800), (10709, 256000), (5429, 128000),
  (11007, 256000), (2789, 64000), (2261, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_006 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
