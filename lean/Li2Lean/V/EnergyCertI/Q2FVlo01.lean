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

/-- Breakpoints of cells 60..69 of piece `vlo` (q = 2). -/
def q2F_vlo_006_b : List QF := [
  (907, 25600), (9219, 256000), (1171, 32000), (9517, 256000),
  (4833, 128000), (1963, 51200), (2491, 64000), (10113, 256000),
  (5131, 128000), (10411, 256000), (33, 800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_006 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_006_b = true := by
  decide +kernel

/-- Breakpoints of cells 70..79 of piece `vlo` (q = 2). -/
def q2F_vlo_007_b : List QF := [
  (33, 800), (10709, 256000), (5429, 128000), (11007, 256000),
  (2789, 64000), (2261, 51200), (5727, 128000), (11603, 256000),
  (1469, 32000), (11901, 256000), (241, 5120)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_007 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 80..89 of piece `vlo` (q = 2). -/
def q2F_vlo_008_b : List QF := [
  (241, 5120), (12199, 256000), (3087, 64000), (12497, 256000),
  (6323, 128000), (2559, 51200), (809, 16000), (13093, 256000),
  (6621, 128000), (13391, 256000), (677, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_008 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..99 of piece `vlo` (q = 2). -/
def q2F_vlo_009_b : List QF := [
  (677, 12800), (13689, 256000), (6919, 128000), (13987, 256000),
  (1767, 32000), (2857, 51200), (7217, 128000), (14583, 256000),
  (3683, 64000), (14881, 256000), (1503, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_009 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 100..109 of piece `vlo` (q = 2). -/
def q2F_vlo_010_b : List QF := [
  (1503, 25600), (15179, 256000), (479, 8000), (15477, 256000),
  (7813, 128000), (631, 10240), (3981, 64000), (16073, 256000),
  (8111, 128000), (16371, 256000), (413, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_010 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 110..119 of piece `vlo` (q = 2). -/
def q2F_vlo_011_b : List QF := [
  (413, 6400), (16669, 256000), (8409, 128000), (16967, 256000),
  (4279, 64000), (3453, 51200), (8707, 128000), (17563, 256000),
  (1107, 16000), (17861, 256000), (1801, 25600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_011 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_011_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
