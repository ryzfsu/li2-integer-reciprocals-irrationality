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

/-- Breakpoints of cells 70..79 of piece `vhi` (q = 3). -/
def q3F_vhi_007_b : List QF := [
  (419, 640), (839, 1280), (21, 32), (841, 1280),
  (421, 640), (843, 1280), (211, 320), (169, 256),
  (423, 640), (847, 1280), (53, 80)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_007 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 80..89 of piece `vhi` (q = 3). -/
def q3F_vhi_008_b : List QF := [
  (53, 80), (849, 1280), (85, 128), (851, 1280),
  (213, 320), (853, 1280), (427, 640), (171, 256),
  (107, 160), (857, 1280), (429, 640)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_008 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..99 of piece `vhi` (q = 3). -/
def q3F_vhi_009_b : List QF := [
  (429, 640), (859, 1280), (43, 64), (861, 1280),
  (431, 640), (863, 1280), (27, 40), (173, 256),
  (433, 640), (867, 1280), (217, 320)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_009 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 100..109 of piece `vhi` (q = 3). -/
def q3F_vhi_010_b : List QF := [
  (217, 320), (869, 1280), (87, 128), (871, 1280),
  (109, 160), (873, 1280), (437, 640), (175, 256),
  (219, 320), (877, 1280), (439, 640)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_010 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 110..119 of piece `vhi` (q = 3). -/
def q3F_vhi_011_b : List QF := [
  (439, 640), (879, 1280), (11, 16), (881, 1280),
  (441, 640), (883, 1280), (221, 320), (177, 256),
  (443, 640), (887, 1280), (111, 160)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_011 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..129 of piece `vhi` (q = 3). -/
def q3F_vhi_012_b : List QF := [
  (111, 160), (889, 1280), (89, 128), (891, 1280),
  (223, 320), (893, 1280), (447, 640), (179, 256),
  (7, 10), (897, 1280), (449, 640)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_012 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..139 of piece `vhi` (q = 3). -/
def q3F_vhi_013_b : List QF := [
  (449, 640), (899, 1280), (45, 64), (901, 1280),
  (451, 640), (903, 1280), (113, 160), (181, 256),
  (453, 640), (907, 1280), (227, 320)]

/-- 10 cells, about 2280 transcendental evaluations (field mode). -/
theorem q3F_vhi_013 :
    cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) q3F_vhi_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
