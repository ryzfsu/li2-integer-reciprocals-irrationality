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

/-- Breakpoints of cells 84..89 of piece `arc1` (q = 2). -/
def q2F_arc1_014_b : List QF := [
  (155, 256), (39, 64), (157, 256), (79, 128),
  (159, 256), (5, 8), (161, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_014 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 90..95 of piece `arc1` (q = 2). -/
def q2F_arc1_015_b : List QF := [
  (161, 256), (81, 128), (163, 256), (41, 64),
  (165, 256), (83, 128), (167, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_015 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..101 of piece `arc1` (q = 2). -/
def q2F_arc1_016_b : List QF := [
  (167, 256), (21, 32), (169, 256), (85, 128),
  (171, 256), (43, 64), (173, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_016 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 102..107 of piece `arc1` (q = 2). -/
def q2F_arc1_017_b : List QF := [
  (173, 256), (87, 128), (175, 256), (11, 16),
  (177, 256), (89, 128), (179, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_017 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..113 of piece `arc1` (q = 2). -/
def q2F_arc1_018_b : List QF := [
  (179, 256), (45, 64), (181, 256), (91, 128),
  (183, 256), (23, 32), (185, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_018 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 114..119 of piece `arc1` (q = 2). -/
def q2F_arc1_019_b : List QF := [
  (185, 256), (93, 128), (187, 256), (47, 64),
  (189, 256), (95, 128), (191, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_019 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..125 of piece `arc1` (q = 2). -/
def q2F_arc1_020_b : List QF := [
  (191, 256), (3, 4), (193, 256), (97, 128),
  (195, 256), (49, 64), (197, 256)]

/-- 6 cells, about 2238 transcendental evaluations (field mode). -/
theorem q2F_arc1_020 :
    cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) q2F_arc1_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
