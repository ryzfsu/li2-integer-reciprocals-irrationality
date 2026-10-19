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

/-- Breakpoints of cells 240..249 of piece `vlo` (q = 2). -/
def q2F_vlo_024_b : List QF := [
  (3589, 25600), (36039, 256000), (9047, 64000), (36337, 256000),
  (18243, 128000), (7327, 51200), (2299, 16000), (36933, 256000),
  (18541, 128000), (37231, 256000), (1869, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_024 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 250..259 of piece `vlo` (q = 2). -/
def q2F_vlo_025_b : List QF := [
  (1869, 12800), (37529, 256000), (18839, 128000), (37827, 256000),
  (4747, 32000), (305, 2048), (19137, 128000), (38423, 256000),
  (9643, 64000), (38721, 256000), (3887, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_025 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..269 of piece `vlo` (q = 2). -/
def q2F_vlo_026_b : List QF := [
  (3887, 25600), (39019, 256000), (153, 1000), (39317, 256000),
  (19733, 128000), (7923, 51200), (9941, 64000), (39913, 256000),
  (20031, 128000), (40211, 256000), (1009, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_026 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 270..279 of piece `vlo` (q = 2). -/
def q2F_vlo_027_b : List QF := [
  (1009, 6400), (40509, 256000), (20329, 128000), (40807, 256000),
  (10239, 64000), (8221, 51200), (20627, 128000), (41403, 256000),
  (2597, 16000), (41701, 256000), (837, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_027 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_027_b = true := by
  decide +kernel

/-- Breakpoints of cells 280..289 of piece `vlo` (q = 2). -/
def q2F_vlo_028_b : List QF := [
  (837, 5120), (41999, 256000), (10537, 64000), (42297, 256000),
  (21223, 128000), (8519, 51200), (5343, 32000), (42893, 256000),
  (21521, 128000), (43191, 256000), (2167, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_028 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 290..299 of piece `vlo` (q = 2). -/
def q2F_vlo_029_b : List QF := [
  (2167, 12800), (43489, 256000), (21819, 128000), (43787, 256000),
  (1373, 8000), (8817, 51200), (22117, 128000), (44383, 256000),
  (11133, 64000), (44681, 256000), (4483, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_029 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_029_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
