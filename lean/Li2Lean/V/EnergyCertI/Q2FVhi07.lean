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

/-- Breakpoints of cells 420..429 of piece `vhi` (q = 2). -/
def q2F_vhi_042_b : List QF := [
  (293, 320), (469, 512), (1173, 1280), (2347, 2560),
  (587, 640), (2349, 2560), (235, 256), (2351, 2560),
  (147, 160), (2353, 2560), (1177, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_042 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 430..439 of piece `vhi` (q = 2). -/
def q2F_vhi_043_b : List QF := [
  (1177, 1280), (471, 512), (589, 640), (2357, 2560),
  (1179, 1280), (2359, 2560), (59, 64), (2361, 2560),
  (1181, 1280), (2363, 2560), (591, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_043 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 440..449 of piece `vhi` (q = 2). -/
def q2F_vhi_044_b : List QF := [
  (591, 640), (473, 512), (1183, 1280), (2367, 2560),
  (37, 40), (2369, 2560), (237, 256), (2371, 2560),
  (593, 640), (2373, 2560), (1187, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_044 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 450..459 of piece `vhi` (q = 2). -/
def q2F_vhi_045_b : List QF := [
  (1187, 1280), (475, 512), (297, 320), (2377, 2560),
  (1189, 1280), (2379, 2560), (119, 128), (2381, 2560),
  (1191, 1280), (2383, 2560), (149, 160)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_045 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 460..469 of piece `vhi` (q = 2). -/
def q2F_vhi_046_b : List QF := [
  (149, 160), (477, 512), (1193, 1280), (2387, 2560),
  (597, 640), (2389, 2560), (239, 256), (2391, 2560),
  (299, 320), (2393, 2560), (1197, 1280)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_046 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 470..479 of piece `vhi` (q = 2). -/
def q2F_vhi_047_b : List QF := [
  (1197, 1280), (479, 512), (599, 640), (2397, 2560),
  (1199, 1280), (2399, 2560), (15, 16), (2401, 2560),
  (1201, 1280), (2403, 2560), (601, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_047 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_047_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
