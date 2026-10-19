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

/-- Breakpoints of cells 350..359 of piece `vhi` (q = 6). -/
def q6F_vhi_035_b : List QF := [
  (559, 640), (1119, 1280), (7, 8), (1121, 1280),
  (561, 640), (1123, 1280), (281, 320), (225, 256),
  (563, 640), (1127, 1280), (141, 160)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_035 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 360..369 of piece `vhi` (q = 6). -/
def q6F_vhi_036_b : List QF := [
  (141, 160), (1129, 1280), (113, 128), (1131, 1280),
  (283, 320), (1133, 1280), (567, 640), (227, 256),
  (71, 80), (1137, 1280), (569, 640)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_036 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 370..379 of piece `vhi` (q = 6). -/
def q6F_vhi_037_b : List QF := [
  (569, 640), (1139, 1280), (57, 64), (1141, 1280),
  (571, 640), (1143, 1280), (143, 160), (229, 256),
  (573, 640), (1147, 1280), (287, 320)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_037 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 380..389 of piece `vhi` (q = 6). -/
def q6F_vhi_038_b : List QF := [
  (287, 320), (1149, 1280), (115, 128), (1151, 1280),
  (9, 10), (1153, 1280), (577, 640), (231, 256),
  (289, 320), (1157, 1280), (579, 640)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_038 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 390..399 of piece `vhi` (q = 6). -/
def q6F_vhi_039_b : List QF := [
  (579, 640), (1159, 1280), (29, 32), (1161, 1280),
  (581, 640), (465, 512), (1163, 1280), (2327, 2560),
  (291, 320), (2329, 2560), (233, 256)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_039 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 400..409 of piece `vhi` (q = 6). -/
def q6F_vhi_040_b : List QF := [
  (233, 256), (2331, 2560), (583, 640), (2333, 2560),
  (1167, 1280), (467, 512), (73, 80), (2337, 2560),
  (1169, 1280), (2339, 2560), (117, 128)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_040 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 410..419 of piece `vhi` (q = 6). -/
def q6F_vhi_041_b : List QF := [
  (117, 128), (2341, 2560), (1171, 1280), (2343, 2560),
  (293, 320), (469, 512), (1173, 1280), (587, 640),
  (235, 256), (147, 160), (1177, 1280)]

/-- 10 cells, about 2230 transcendental evaluations (field mode). -/
theorem q6F_vhi_041 :
    cellsOK (fieldUB q6D 6 vLogRF .vhi) (kvQ 6) q6F_vhi_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
