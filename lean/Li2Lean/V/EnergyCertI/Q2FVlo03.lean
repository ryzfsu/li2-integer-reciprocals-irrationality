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

/-- Breakpoints of cells 180..189 of piece `vlo` (q = 2). -/
def q2F_vlo_018_b : List QF := [
  (539, 5120), (27099, 256000), (1703, 16000), (27397, 256000),
  (13773, 128000), (5539, 51200), (6961, 64000), (27993, 256000),
  (14071, 128000), (28291, 256000), (711, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_018 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 190..199 of piece `vlo` (q = 2). -/
def q2F_vlo_019_b : List QF := [
  (711, 6400), (28589, 256000), (14369, 128000), (28887, 256000),
  (7259, 64000), (5837, 51200), (14667, 128000), (29483, 256000),
  (463, 4000), (29781, 256000), (2993, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_019 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 200..209 of piece `vlo` (q = 2). -/
def q2F_vlo_020_b : List QF := [
  (2993, 25600), (30079, 256000), (7557, 64000), (30377, 256000),
  (15263, 128000), (1227, 10240), (3853, 32000), (30973, 256000),
  (15561, 128000), (31271, 256000), (1571, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_020 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_020_b = true := by
  decide +kernel

/-- Breakpoints of cells 210..219 of piece `vlo` (q = 2). -/
def q2F_vlo_021_b : List QF := [
  (1571, 12800), (31569, 256000), (15859, 128000), (31867, 256000),
  (2001, 16000), (6433, 51200), (16157, 128000), (32463, 256000),
  (8153, 64000), (32761, 256000), (3291, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_021 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 220..229 of piece `vlo` (q = 2). -/
def q2F_vlo_022_b : List QF := [
  (3291, 25600), (33059, 256000), (4151, 32000), (33357, 256000),
  (16753, 128000), (6731, 51200), (8451, 64000), (33953, 256000),
  (17051, 128000), (34251, 256000), (43, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_022 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 230..239 of piece `vlo` (q = 2). -/
def q2F_vlo_023_b : List QF := [
  (43, 320), (34549, 256000), (17349, 128000), (34847, 256000),
  (8749, 64000), (7029, 51200), (17647, 128000), (35443, 256000),
  (4449, 32000), (35741, 256000), (3589, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_023 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
