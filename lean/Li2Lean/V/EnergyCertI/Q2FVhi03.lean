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

/-- Breakpoints of cells 180..189 of piece `vhi` (q = 2). -/
def q2F_vhi_018_b : List QF := [
  (237, 320), (949, 1280), (95, 128), (951, 1280),
  (119, 160), (953, 1280), (477, 640), (191, 256),
  (239, 320), (957, 1280), (479, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_018 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 190..199 of piece `vhi` (q = 2). -/
def q2F_vhi_019_b : List QF := [
  (479, 640), (959, 1280), (3, 4), (961, 1280),
  (481, 640), (963, 1280), (241, 320), (193, 256),
  (483, 640), (967, 1280), (121, 160)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_019 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 200..209 of piece `vhi` (q = 2). -/
def q2F_vhi_020_b : List QF := [
  (121, 160), (969, 1280), (97, 128), (971, 1280),
  (243, 320), (973, 1280), (487, 640), (195, 256),
  (61, 80), (977, 1280), (489, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_020 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_020_b = true := by
  decide +kernel

/-- Breakpoints of cells 210..219 of piece `vhi` (q = 2). -/
def q2F_vhi_021_b : List QF := [
  (489, 640), (979, 1280), (49, 64), (981, 1280),
  (491, 640), (983, 1280), (123, 160), (197, 256),
  (493, 640), (987, 1280), (247, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_021 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 220..229 of piece `vhi` (q = 2). -/
def q2F_vhi_022_b : List QF := [
  (247, 320), (989, 1280), (99, 128), (991, 1280),
  (31, 40), (993, 1280), (497, 640), (199, 256),
  (249, 320), (997, 1280), (499, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_022 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 230..239 of piece `vhi` (q = 2). -/
def q2F_vhi_023_b : List QF := [
  (499, 640), (999, 1280), (25, 32), (1001, 1280),
  (501, 640), (1003, 1280), (251, 320), (201, 256),
  (503, 640), (1007, 1280), (63, 80)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_023 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
