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

/-- Breakpoints of cells 120..129 of piece `vhi` (q = 2). -/
def q2F_vhi_012_b : List QF := [
  (111, 160), (889, 1280), (89, 128), (891, 1280),
  (223, 320), (893, 1280), (447, 640), (179, 256),
  (7, 10), (897, 1280), (449, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_012 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..139 of piece `vhi` (q = 2). -/
def q2F_vhi_013_b : List QF := [
  (449, 640), (899, 1280), (45, 64), (901, 1280),
  (451, 640), (903, 1280), (113, 160), (181, 256),
  (453, 640), (907, 1280), (227, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_013 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_013_b = true := by
  decide +kernel

/-- Breakpoints of cells 140..149 of piece `vhi` (q = 2). -/
def q2F_vhi_014_b : List QF := [
  (227, 320), (909, 1280), (91, 128), (911, 1280),
  (57, 80), (913, 1280), (457, 640), (183, 256),
  (229, 320), (917, 1280), (459, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_014 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..159 of piece `vhi` (q = 2). -/
def q2F_vhi_015_b : List QF := [
  (459, 640), (919, 1280), (23, 32), (921, 1280),
  (461, 640), (923, 1280), (231, 320), (185, 256),
  (463, 640), (927, 1280), (29, 40)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_015 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 160..169 of piece `vhi` (q = 2). -/
def q2F_vhi_016_b : List QF := [
  (29, 40), (929, 1280), (93, 128), (931, 1280),
  (233, 320), (933, 1280), (467, 640), (187, 256),
  (117, 160), (937, 1280), (469, 640)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_016 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 170..179 of piece `vhi` (q = 2). -/
def q2F_vhi_017_b : List QF := [
  (469, 640), (939, 1280), (47, 64), (941, 1280),
  (471, 640), (943, 1280), (59, 80), (189, 256),
  (473, 640), (947, 1280), (237, 320)]

/-- 10 cells, about 2320 transcendental evaluations (field mode). -/
theorem q2F_vhi_017 :
    cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) q2F_vhi_017_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
