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

/-- Breakpoints of cells 490..499 of piece `vlo` (q = 3). -/
def q3F_vlo_049_b : List QF := [
  (13091, 32000), (52513, 128000), (26331, 64000), (52811, 128000),
  (331, 800), (53109, 128000), (26629, 64000), (53407, 128000),
  (13389, 32000), (10741, 25600), (26927, 64000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_049 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 500..509 of piece `vlo` (q = 3). -/
def q3F_vlo_050_b : List QF := [
  (26927, 64000), (54003, 128000), (6769, 16000), (54301, 128000),
  (1089, 2560), (54599, 128000), (13687, 32000), (54897, 128000),
  (27523, 64000), (11039, 25600), (3459, 8000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_050 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 510..519 of piece `vlo` (q = 3). -/
def q3F_vlo_051_b : List QF := [
  (3459, 8000), (55493, 128000), (27821, 64000), (55791, 128000),
  (2797, 6400), (56089, 128000), (28119, 64000), (56387, 128000),
  (7067, 16000), (11337, 25600), (28417, 64000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_051 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..529 of piece `vlo` (q = 3). -/
def q3F_vlo_052_b : List QF := [
  (28417, 64000), (56983, 128000), (14283, 32000), (57281, 128000),
  (5743, 12800), (57579, 128000), (451, 1000), (57877, 128000),
  (29013, 64000), (2327, 5120), (14581, 32000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_052 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 530..539 of piece `vlo` (q = 3). -/
def q3F_vlo_053_b : List QF := [
  (14581, 32000), (58473, 128000), (29311, 64000), (58771, 128000),
  (1473, 3200), (59069, 128000), (29609, 64000), (59367, 128000),
  (14879, 32000), (11933, 25600), (29907, 64000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_053 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_053_b = true := by
  decide +kernel

/-- Breakpoints of cells 540..549 of piece `vlo` (q = 3). -/
def q3F_vlo_054_b : List QF := [
  (29907, 64000), (59963, 128000), (3757, 8000), (60261, 128000),
  (6041, 12800), (60559, 128000), (15177, 32000), (60857, 128000),
  (30503, 64000), (12231, 25600), (7663, 16000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_054 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 550..559 of piece `vlo` (q = 3). -/
def q3F_vlo_055_b : List QF := [
  (7663, 16000), (61453, 128000), (30801, 64000), (61751, 128000),
  (619, 1280), (62049, 128000), (31099, 64000), (62347, 128000),
  (1953, 4000), (12529, 25600), (31397, 64000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_055 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_055_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
