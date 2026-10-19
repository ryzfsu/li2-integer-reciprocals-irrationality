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

/-- Breakpoints of cells 420..429 of piece `vhi` (q = 5). -/
def q5F_vhi_042_b : List QF := [
  (2361, 2560), (1181, 1280), (2363, 2560), (591, 640),
  (473, 512), (1183, 1280), (2367, 2560), (37, 40),
  (2369, 2560), (237, 256), (2371, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_042 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 430..439 of piece `vhi` (q = 5). -/
def q5F_vhi_043_b : List QF := [
  (2371, 2560), (593, 640), (2373, 2560), (1187, 1280),
  (475, 512), (297, 320), (2377, 2560), (1189, 1280),
  (2379, 2560), (119, 128), (2381, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_043 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 440..449 of piece `vhi` (q = 5). -/
def q5F_vhi_044_b : List QF := [
  (2381, 2560), (1191, 1280), (2383, 2560), (149, 160),
  (477, 512), (1193, 1280), (2387, 2560), (597, 640),
  (2389, 2560), (239, 256), (2391, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_044 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 450..459 of piece `vhi` (q = 5). -/
def q5F_vhi_045_b : List QF := [
  (2391, 2560), (299, 320), (2393, 2560), (1197, 1280),
  (479, 512), (599, 640), (2397, 2560), (1199, 1280),
  (2399, 2560), (15, 16), (2401, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_045 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 460..469 of piece `vhi` (q = 5). -/
def q5F_vhi_046_b : List QF := [
  (2401, 2560), (1201, 1280), (2403, 2560), (601, 640),
  (481, 512), (1203, 1280), (2407, 2560), (301, 320),
  (2409, 2560), (241, 256), (2411, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_046 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 470..479 of piece `vhi` (q = 5). -/
def q5F_vhi_047_b : List QF := [
  (2411, 2560), (603, 640), (2413, 2560), (1207, 1280),
  (483, 512), (151, 160), (2417, 2560), (1209, 1280),
  (2419, 2560), (121, 128), (2421, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_047 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_047_b = true := by
  decide +kernel

/-- Breakpoints of cells 480..489 of piece `vhi` (q = 5). -/
def q5F_vhi_048_b : List QF := [
  (2421, 2560), (1211, 1280), (2423, 2560), (303, 320),
  (485, 512), (1213, 1280), (2427, 2560), (607, 640),
  (2429, 2560), (243, 256), (2431, 2560)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_048 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
