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

/-- Breakpoints of cells 600..609 of piece `vlo` (q = 2). -/
def q2F_vlo_060_b : List QF := [
  (619, 1280), (62049, 128000), (31099, 64000), (62347, 128000),
  (1953, 4000), (12529, 25600), (31397, 64000), (62943, 128000),
  (15773, 32000), (63241, 128000), (6339, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_060 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 610..619 of piece `vlo` (q = 2). -/
def q2F_vlo_061_b : List QF := [
  (6339, 12800), (63539, 128000), (7961, 16000), (63837, 128000),
  (31993, 64000), (12827, 25600), (16071, 32000), (64433, 128000),
  (32291, 64000), (64731, 128000), (811, 1600)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_061 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 620..629 of piece `vlo` (q = 2). -/
def q2F_vlo_062_b : List QF := [
  (811, 1600), (65029, 128000), (32589, 64000), (65327, 128000),
  (16369, 32000), (525, 1024), (32887, 64000), (65923, 128000),
  (8259, 16000), (66221, 128000), (6637, 12800)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_062 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_062_b = true := by
  decide +kernel

/-- Breakpoints of cells 630..639 of piece `vlo` (q = 2). -/
def q2F_vlo_063_b : List QF := [
  (6637, 12800), (66519, 128000), (16667, 32000), (66817, 128000),
  (33483, 64000), (13423, 25600), (1051, 2000), (67413, 128000),
  (33781, 64000), (67711, 128000), (3393, 6400)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_063 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 640..649 of piece `vlo` (q = 2). -/
def q2F_vlo_064_b : List QF := [
  (3393, 6400), (68009, 128000), (34079, 64000), (68307, 128000),
  (8557, 16000), (13721, 25600), (34377, 64000), (68903, 128000),
  (17263, 32000), (69201, 128000), (1387, 2560)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_064 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..659 of piece `vlo` (q = 2). -/
def q2F_vlo_065_b : List QF := [
  (1387, 2560), (69499, 128000), (4353, 8000), (69797, 128000),
  (34973, 64000), (14019, 25600), (17561, 32000), (70393, 128000),
  (35271, 64000), (70691, 128000), (1771, 3200)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vlo_065 :
    cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) q2F_vlo_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
