/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 140..149 of piece `vhi` (q = 4). -/
def q4F_vhi_014_b : List QF := [
  (227, 320), (909, 1280), (91, 128), (911, 1280),
  (57, 80), (913, 1280), (457, 640), (183, 256),
  (229, 320), (917, 1280), (459, 640)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_014 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 150..159 of piece `vhi` (q = 4). -/
def q4F_vhi_015_b : List QF := [
  (459, 640), (919, 1280), (23, 32), (921, 1280),
  (461, 640), (923, 1280), (231, 320), (185, 256),
  (463, 640), (927, 1280), (29, 40)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_015 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 160..169 of piece `vhi` (q = 4). -/
def q4F_vhi_016_b : List QF := [
  (29, 40), (929, 1280), (93, 128), (931, 1280),
  (233, 320), (933, 1280), (467, 640), (187, 256),
  (117, 160), (937, 1280), (469, 640)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_016 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 170..179 of piece `vhi` (q = 4). -/
def q4F_vhi_017_b : List QF := [
  (469, 640), (939, 1280), (47, 64), (941, 1280),
  (471, 640), (943, 1280), (59, 80), (189, 256),
  (473, 640), (947, 1280), (237, 320)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_017 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..189 of piece `vhi` (q = 4). -/
def q4F_vhi_018_b : List QF := [
  (237, 320), (949, 1280), (95, 128), (951, 1280),
  (119, 160), (953, 1280), (477, 640), (191, 256),
  (239, 320), (957, 1280), (479, 640)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_018 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 190..199 of piece `vhi` (q = 4). -/
def q4F_vhi_019_b : List QF := [
  (479, 640), (959, 1280), (3, 4), (961, 1280),
  (481, 640), (963, 1280), (241, 320), (193, 256),
  (483, 640), (967, 1280), (121, 160)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_019 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 200..209 of piece `vhi` (q = 4). -/
def q4F_vhi_020_b : List QF := [
  (121, 160), (969, 1280), (97, 128), (971, 1280),
  (243, 320), (973, 1280), (487, 640), (195, 256),
  (61, 80), (977, 1280), (489, 640)]

/-- 10 cells, about 2270 transcendental evaluations (field mode). -/
theorem q4F_vhi_020 :
    cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) q4F_vhi_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
