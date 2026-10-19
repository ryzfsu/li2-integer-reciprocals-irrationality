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

/-- Breakpoints of cells 240..249 of piece `vhi` (q = 2). -/
def q2F_vhi_024_b : List QF := [
  (63, 80), (1009, 1280), (101, 128), (1011, 1280),
  (253, 320), (1013, 1280), (507, 640), (203, 256),
  (127, 160), (1017, 1280), (509, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_024 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 250..259 of piece `vhi` (q = 2). -/
def q2F_vhi_025_b : List QF := [
  (509, 640), (1019, 1280), (51, 64), (1021, 1280),
  (511, 640), (1023, 1280), (4, 5), (205, 256),
  (513, 640), (1027, 1280), (257, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_025 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..269 of piece `vhi` (q = 2). -/
def q2F_vhi_026_b : List QF := [
  (257, 320), (1029, 1280), (103, 128), (1031, 1280),
  (129, 160), (1033, 1280), (517, 640), (207, 256),
  (259, 320), (1037, 1280), (519, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_026 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 270..279 of piece `vhi` (q = 2). -/
def q2F_vhi_027_b : List QF := [
  (519, 640), (1039, 1280), (13, 16), (1041, 1280),
  (521, 640), (1043, 1280), (261, 320), (209, 256),
  (523, 640), (1047, 1280), (131, 160)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_027 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_027_b = true := by
  decide +kernel

/-- Breakpoints of cells 280..289 of piece `vhi` (q = 2). -/
def q2F_vhi_028_b : List QF := [
  (131, 160), (1049, 1280), (105, 128), (1051, 1280),
  (263, 320), (1053, 1280), (527, 640), (211, 256),
  (33, 40), (1057, 1280), (529, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_028 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 290..299 of piece `vhi` (q = 2). -/
def q2F_vhi_029_b : List QF := [
  (529, 640), (1059, 1280), (53, 64), (1061, 1280),
  (531, 640), (1063, 1280), (133, 160), (213, 256),
  (533, 640), (1067, 1280), (267, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_029 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_029_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
