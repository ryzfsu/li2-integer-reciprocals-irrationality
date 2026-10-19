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

/-- Breakpoints of cells 480..489 of piece `vhi` (q = 2). -/
def q2F_vhi_048_b : List QF := [
  (601, 640), (481, 512), (1203, 1280), (2407, 2560),
  (301, 320), (2409, 2560), (241, 256), (2411, 2560),
  (603, 640), (2413, 2560), (1207, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_048 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_048_b = true := by
  decide +kernel

/-- Breakpoints of cells 490..499 of piece `vhi` (q = 2). -/
def q2F_vhi_049_b : List QF := [
  (1207, 1280), (483, 512), (151, 160), (2417, 2560),
  (1209, 1280), (2419, 2560), (121, 128), (2421, 2560),
  (1211, 1280), (2423, 2560), (303, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_049 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 500..509 of piece `vhi` (q = 2). -/
def q2F_vhi_050_b : List QF := [
  (303, 320), (485, 512), (1213, 1280), (2427, 2560),
  (607, 640), (2429, 2560), (243, 256), (2431, 2560),
  (19, 20), (2433, 2560), (1217, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_050 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 510..519 of piece `vhi` (q = 2). -/
def q2F_vhi_051_b : List QF := [
  (1217, 1280), (487, 512), (609, 640), (2437, 2560),
  (1219, 1280), (2439, 2560), (61, 64), (2441, 2560),
  (1221, 1280), (2443, 2560), (611, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_051 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..529 of piece `vhi` (q = 2). -/
def q2F_vhi_052_b : List QF := [
  (611, 640), (489, 512), (1223, 1280), (2447, 2560),
  (153, 160), (2449, 2560), (245, 256), (2451, 2560),
  (613, 640), (2453, 2560), (1227, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_052 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 530..539 of piece `vhi` (q = 2). -/
def q2F_vhi_053_b : List QF := [
  (1227, 1280), (491, 512), (307, 320), (2457, 2560),
  (1229, 1280), (2459, 2560), (123, 128), (2461, 2560),
  (1231, 1280), (2463, 2560), (77, 80)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_053 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_053_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
