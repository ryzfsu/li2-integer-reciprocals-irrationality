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

/-- Breakpoints of cells 60..69 of piece `vhi` (q = 2). -/
def q2F_vhi_006_b : List QF := [
  (207, 320), (829, 1280), (83, 128), (831, 1280),
  (13, 20), (833, 1280), (417, 640), (167, 256),
  (209, 320), (837, 1280), (419, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_006 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_006_b = true := by
  decide +kernel

/-- Breakpoints of cells 70..79 of piece `vhi` (q = 2). -/
def q2F_vhi_007_b : List QF := [
  (419, 640), (839, 1280), (21, 32), (841, 1280),
  (421, 640), (843, 1280), (211, 320), (169, 256),
  (423, 640), (847, 1280), (53, 80)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_007 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 80..89 of piece `vhi` (q = 2). -/
def q2F_vhi_008_b : List QF := [
  (53, 80), (849, 1280), (85, 128), (851, 1280),
  (213, 320), (853, 1280), (427, 640), (171, 256),
  (107, 160), (857, 1280), (429, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_008 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..99 of piece `vhi` (q = 2). -/
def q2F_vhi_009_b : List QF := [
  (429, 640), (859, 1280), (43, 64), (861, 1280),
  (431, 640), (863, 1280), (27, 40), (173, 256),
  (433, 640), (867, 1280), (217, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_009 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 100..109 of piece `vhi` (q = 2). -/
def q2F_vhi_010_b : List QF := [
  (217, 320), (869, 1280), (87, 128), (871, 1280),
  (109, 160), (873, 1280), (437, 640), (175, 256),
  (219, 320), (877, 1280), (439, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_010 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 110..119 of piece `vhi` (q = 2). -/
def q2F_vhi_011_b : List QF := [
  (439, 640), (879, 1280), (11, 16), (881, 1280),
  (441, 640), (883, 1280), (221, 320), (177, 256),
  (443, 640), (887, 1280), (111, 160)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_011 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_011_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
