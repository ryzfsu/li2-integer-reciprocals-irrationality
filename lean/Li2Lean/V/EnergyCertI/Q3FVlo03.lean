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

/-- Breakpoints of cells 210..219 of piece `vlo` (q = 3). -/
def q3F_vlo_021_b : List QF := [
  (6433, 51200), (16157, 128000), (32463, 256000), (8153, 64000),
  (32761, 256000), (3291, 25600), (33059, 256000), (4151, 32000),
  (33357, 256000), (16753, 128000), (6731, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_021 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 220..229 of piece `vlo` (q = 3). -/
def q3F_vlo_022_b : List QF := [
  (6731, 51200), (8451, 64000), (33953, 256000), (17051, 128000),
  (34251, 256000), (43, 320), (34549, 256000), (17349, 128000),
  (34847, 256000), (8749, 64000), (7029, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_022 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 230..239 of piece `vlo` (q = 3). -/
def q3F_vlo_023_b : List QF := [
  (7029, 51200), (17647, 128000), (35443, 256000), (4449, 32000),
  (35741, 256000), (3589, 25600), (36039, 256000), (9047, 64000),
  (36337, 256000), (18243, 128000), (7327, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_023 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..249 of piece `vlo` (q = 3). -/
def q3F_vlo_024_b : List QF := [
  (7327, 51200), (2299, 16000), (36933, 256000), (18541, 128000),
  (37231, 256000), (1869, 12800), (37529, 256000), (18839, 128000),
  (37827, 256000), (4747, 32000), (305, 2048)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_024 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 250..259 of piece `vlo` (q = 3). -/
def q3F_vlo_025_b : List QF := [
  (305, 2048), (19137, 128000), (38423, 256000), (9643, 64000),
  (38721, 256000), (3887, 25600), (39019, 256000), (153, 1000),
  (39317, 256000), (19733, 128000), (7923, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_025 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..269 of piece `vlo` (q = 3). -/
def q3F_vlo_026_b : List QF := [
  (7923, 51200), (9941, 64000), (39913, 256000), (20031, 128000),
  (40211, 256000), (1009, 6400), (40509, 256000), (20329, 128000),
  (40807, 256000), (10239, 64000), (8221, 51200)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_026 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 270..279 of piece `vlo` (q = 3). -/
def q3F_vlo_027_b : List QF := [
  (8221, 51200), (20627, 128000), (2597, 16000), (837, 5120),
  (10537, 64000), (21223, 128000), (5343, 32000), (21521, 128000),
  (2167, 12800), (21819, 128000), (43787, 256000)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vlo_027 :
    cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) q3F_vlo_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
