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

/-- Breakpoints of cells 420..429 of piece `vlo` (q = 2). -/
def q2F_vlo_042_b : List QF := [
  (877, 3200), (35229, 128000), (17689, 64000), (35527, 128000),
  (8919, 32000), (1433, 5120), (17987, 64000), (36123, 128000),
  (2267, 8000), (36421, 128000), (3657, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_042 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 430..439 of piece `vlo` (q = 2). -/
def q2F_vlo_043_b : List QF := [
  (3657, 12800), (36719, 128000), (9217, 32000), (37017, 128000),
  (18583, 64000), (7463, 25600), (4683, 16000), (37613, 128000),
  (18881, 64000), (37911, 128000), (1903, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_043 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 440..449 of piece `vlo` (q = 2). -/
def q2F_vlo_044_b : List QF := [
  (1903, 6400), (38209, 128000), (19179, 64000), (38507, 128000),
  (151, 500), (7761, 25600), (19477, 64000), (39103, 128000),
  (9813, 32000), (39401, 128000), (791, 2560)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_044 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 450..459 of piece `vlo` (q = 2). -/
def q2F_vlo_045_b : List QF := [
  (791, 2560), (39699, 128000), (4981, 16000), (39997, 128000),
  (20073, 64000), (8059, 25600), (10111, 32000), (40593, 128000),
  (20371, 64000), (40891, 128000), (513, 1600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_045 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 460..469 of piece `vlo` (q = 2). -/
def q2F_vlo_046_b : List QF := [
  (513, 1600), (41189, 128000), (20669, 64000), (41487, 128000),
  (10409, 32000), (8357, 25600), (20967, 64000), (42083, 128000),
  (5279, 16000), (42381, 128000), (4253, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_046 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 470..479 of piece `vlo` (q = 2). -/
def q2F_vlo_047_b : List QF := [
  (4253, 12800), (42679, 128000), (10707, 32000), (42977, 128000),
  (21563, 64000), (1731, 5120), (1357, 4000), (43573, 128000),
  (21861, 64000), (43871, 128000), (2201, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_047 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_047_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
