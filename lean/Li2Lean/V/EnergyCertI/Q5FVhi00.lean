/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..9 of piece `vhi` (q = 5). -/
def q5F_vhi_000_b : List QF := [
  (3, 5), (769, 1280), (77, 128), (771, 1280),
  (193, 320), (773, 1280), (387, 640), (155, 256),
  (97, 160), (777, 1280), (389, 640)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_000 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 10..19 of piece `vhi` (q = 5). -/
def q5F_vhi_001_b : List QF := [
  (389, 640), (779, 1280), (39, 64), (781, 1280),
  (391, 640), (783, 1280), (49, 80), (157, 256),
  (393, 640), (787, 1280), (197, 320)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_001 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 20..29 of piece `vhi` (q = 5). -/
def q5F_vhi_002_b : List QF := [
  (197, 320), (789, 1280), (79, 128), (791, 1280),
  (99, 160), (793, 1280), (397, 640), (159, 256),
  (199, 320), (797, 1280), (399, 640)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_002 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 30..39 of piece `vhi` (q = 5). -/
def q5F_vhi_003_b : List QF := [
  (399, 640), (799, 1280), (5, 8), (801, 1280),
  (401, 640), (803, 1280), (201, 320), (161, 256),
  (403, 640), (807, 1280), (101, 160)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_003 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 40..49 of piece `vhi` (q = 5). -/
def q5F_vhi_004_b : List QF := [
  (101, 160), (809, 1280), (81, 128), (811, 1280),
  (203, 320), (813, 1280), (407, 640), (163, 256),
  (51, 80), (817, 1280), (409, 640)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_004 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 50..59 of piece `vhi` (q = 5). -/
def q5F_vhi_005_b : List QF := [
  (409, 640), (819, 1280), (41, 64), (821, 1280),
  (411, 640), (823, 1280), (103, 160), (165, 256),
  (413, 640), (827, 1280), (207, 320)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_005 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..69 of piece `vhi` (q = 5). -/
def q5F_vhi_006_b : List QF := [
  (207, 320), (829, 1280), (83, 128), (831, 1280),
  (13, 20), (833, 1280), (417, 640), (167, 256),
  (209, 320), (837, 1280), (419, 640)]

/-- 10 cells, about 2240 transcendental evaluations (field mode). -/
theorem q5F_vhi_006 :
    cellsOK (fieldUB q5D 5 vLogRF .vhi) (kvQ 5) q5F_vhi_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
