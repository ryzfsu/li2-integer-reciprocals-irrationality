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

/-- Breakpoints of cells 84..95 of piece `zneg` (q = 2). -/
def q2F_zneg_007_b : List QF := [
  (-2469, 1280), (-9869, 5120), (-4931, 2560), (-1971, 1024),
  (-1231, 640), (-9841, 5120), (-4917, 2560), (-9827, 5120),
  (-491, 256), (-9813, 5120), (-4903, 2560), (-9799, 5120),
  (-153, 80)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_007 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..107 of piece `zneg` (q = 2). -/
def q2F_zneg_008_b : List QF := [
  (-153, 80), (-1957, 1024), (-4889, 2560), (-9771, 5120),
  (-2441, 1280), (-9757, 5120), (-975, 512), (-9743, 5120),
  (-1217, 640), (-9729, 5120), (-4861, 2560), (-1943, 1024),
  (-2427, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_008 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..119 of piece `zneg` (q = 2). -/
def q2F_zneg_009_b : List QF := [
  (-2427, 1280), (-9701, 5120), (-4847, 2560), (-9687, 5120),
  (-121, 64), (-9673, 5120), (-4833, 2560), (-9659, 5120),
  (-2413, 1280), (-1929, 1024), (-4819, 2560), (-9631, 5120),
  (-1203, 640)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_009 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..131 of piece `zneg` (q = 2). -/
def q2F_zneg_010_b : List QF := [
  (-1203, 640), (-9617, 5120), (-961, 512), (-9603, 5120),
  (-2399, 1280), (-9589, 5120), (-4791, 2560), (-1915, 1024),
  (-299, 160), (-9561, 5120), (-4777, 2560), (-9547, 5120),
  (-477, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_010 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..143 of piece `zneg` (q = 2). -/
def q2F_zneg_011_b : List QF := [
  (-477, 256), (-9533, 5120), (-4763, 2560), (-9519, 5120),
  (-1189, 640), (-1901, 1024), (-4749, 2560), (-9491, 5120),
  (-2371, 1280), (-9477, 5120), (-947, 512), (-9463, 5120),
  (-591, 320)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_011 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..155 of piece `zneg` (q = 2). -/
def q2F_zneg_012_b : List QF := [
  (-591, 320), (-9449, 5120), (-4721, 2560), (-1887, 1024),
  (-2357, 1280), (-9421, 5120), (-4707, 2560), (-9407, 5120),
  (-235, 128), (-9393, 5120), (-4693, 2560), (-9379, 5120),
  (-2343, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_012 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..167 of piece `zneg` (q = 2). -/
def q2F_zneg_013_b : List QF := [
  (-2343, 1280), (-1873, 1024), (-4679, 2560), (-9351, 5120),
  (-73, 40), (-9337, 5120), (-933, 512), (-9323, 5120),
  (-2329, 1280), (-9309, 5120), (-4651, 2560), (-1859, 1024),
  (-1161, 640)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_013 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
