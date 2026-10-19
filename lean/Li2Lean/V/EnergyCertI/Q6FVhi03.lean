/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 210..219 of piece `vhi` (q = 6). -/
def q6F_vhi_021_b : List QF := [
  (489, 640), (979, 1280), (49, 64), (981, 1280),
  (491, 640), (983, 1280), (123, 160), (197, 256),
  (493, 640), (987, 1280), (247, 320)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_021 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 220..229 of piece `vhi` (q = 6). -/
def q6F_vhi_022_b : List QF := [
  (247, 320), (989, 1280), (99, 128), (991, 1280),
  (31, 40), (993, 1280), (497, 640), (199, 256),
  (249, 320), (997, 1280), (499, 640)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_022 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 230..239 of piece `vhi` (q = 6). -/
def q6F_vhi_023_b : List QF := [
  (499, 640), (999, 1280), (25, 32), (1001, 1280),
  (501, 640), (1003, 1280), (251, 320), (201, 256),
  (503, 640), (1007, 1280), (63, 80)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_023 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..249 of piece `vhi` (q = 6). -/
def q6F_vhi_024_b : List QF := [
  (63, 80), (1009, 1280), (101, 128), (1011, 1280),
  (253, 320), (1013, 1280), (507, 640), (203, 256),
  (127, 160), (1017, 1280), (509, 640)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_024 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 250..259 of piece `vhi` (q = 6). -/
def q6F_vhi_025_b : List QF := [
  (509, 640), (1019, 1280), (51, 64), (1021, 1280),
  (511, 640), (1023, 1280), (4, 5), (205, 256),
  (513, 640), (1027, 1280), (257, 320)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_025 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..269 of piece `vhi` (q = 6). -/
def q6F_vhi_026_b : List QF := [
  (257, 320), (1029, 1280), (103, 128), (1031, 1280),
  (129, 160), (1033, 1280), (517, 640), (207, 256),
  (259, 320), (1037, 1280), (519, 640)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_026 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 270..279 of piece `vhi` (q = 6). -/
def q6F_vhi_027_b : List QF := [
  (519, 640), (1039, 1280), (13, 16), (1041, 1280),
  (521, 640), (1043, 1280), (261, 320), (209, 256),
  (523, 640), (1047, 1280), (131, 160)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_027 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
