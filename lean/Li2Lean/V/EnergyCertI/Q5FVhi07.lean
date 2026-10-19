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

/-- Breakpoints of cells 490..499 of piece `vhi` (q = 5). -/
def q5F_vhi_049_b : List QF := [
  (2431, 2560), (19, 20), (2433, 2560), (1217, 1280),
  (487, 512), (609, 640), (2437, 2560), (1219, 1280),
  (2439, 2560), (61, 64), (2441, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_049 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 500..509 of piece `vhi` (q = 5). -/
def q5F_vhi_050_b : List QF := [
  (2441, 2560), (1221, 1280), (2443, 2560), (611, 640),
  (489, 512), (1223, 1280), (2447, 2560), (153, 160),
  (2449, 2560), (245, 256), (2451, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_050 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 510..519 of piece `vhi` (q = 5). -/
def q5F_vhi_051_b : List QF := [
  (2451, 2560), (613, 640), (2453, 2560), (1227, 1280),
  (491, 512), (307, 320), (2457, 2560), (1229, 1280),
  (2459, 2560), (123, 128), (2461, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_051 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..529 of piece `vhi` (q = 5). -/
def q5F_vhi_052_b : List QF := [
  (2461, 2560), (1231, 1280), (2463, 2560), (77, 80),
  (493, 512), (1233, 1280), (2467, 2560), (617, 640),
  (2469, 2560), (247, 256), (2471, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_052 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 530..539 of piece `vhi` (q = 5). -/
def q5F_vhi_053_b : List QF := [
  (2471, 2560), (309, 320), (2473, 2560), (1237, 1280),
  (495, 512), (619, 640), (2477, 2560), (1239, 1280),
  (2479, 2560), (31, 32), (2481, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_053 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_053_b = true := by
  decide +kernel

/-- Breakpoints of cells 540..549 of piece `vhi` (q = 5). -/
def q5F_vhi_054_b : List QF := [
  (2481, 2560), (1241, 1280), (2483, 2560), (621, 640),
  (497, 512), (1243, 1280), (2487, 2560), (311, 320),
  (2489, 2560), (249, 256), (2491, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_054 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 550..559 of piece `vhi` (q = 5). -/
def q5F_vhi_055_b : List QF := [
  (2491, 2560), (623, 640), (2493, 2560), (1247, 1280),
  (499, 512), (39, 40), (2497, 2560), (1249, 1280),
  (2499, 2560), (125, 128), (2501, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_055 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_055_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
