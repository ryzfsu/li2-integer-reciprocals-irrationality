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

/-- Breakpoints of cells 780..792 of piece `zneg` (q = 5). -/
def q5F_zneg_060_b : List QF := [
  (-5309, 2560), (-2649, 1280), (-5287, 2560), (-1319, 640),
  (-1053, 512), (-2627, 1280), (-5243, 2560), (-327, 160),
  (-5221, 2560), (-521, 256), (-5199, 2560), (-1297, 640),
  (-5177, 2560), (-2583, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_060 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 793..805 of piece `zneg` (q = 5). -/
def q5F_zneg_061_b : List QF := [
  (-2583, 1280), (-1031, 512), (-643, 320), (-5133, 2560),
  (-2561, 1280), (-5111, 2560), (-255, 128), (-5089, 2560),
  (-2539, 1280), (-5067, 2560), (-79, 40), (-1009, 512),
  (-2517, 1280), (-5023, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_061 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 806..818 of piece `zneg` (q = 5). -/
def q5F_zneg_062_b : List QF := [
  (-5023, 2560), (-1253, 640), (-5001, 2560), (-499, 256),
  (-4979, 2560), (-621, 320), (-4957, 2560), (-2473, 1280),
  (-987, 512), (-1231, 640), (-4913, 2560), (-2451, 1280),
  (-4891, 2560), (-61, 32)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_062 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_062_b = true := by
  decide +kernel

/-- Breakpoints of cells 819..831 of piece `zneg` (q = 5). -/
def q5F_zneg_063_b : List QF := [
  (-61, 32), (-4869, 2560), (-2429, 1280), (-4847, 2560),
  (-1209, 640), (-965, 512), (-2407, 1280), (-4803, 2560),
  (-599, 320), (-4781, 2560), (-477, 256), (-4759, 2560),
  (-1187, 640), (-4737, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_063 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 832..844 of piece `zneg` (q = 5). -/
def q5F_zneg_064_b : List QF := [
  (-4737, 2560), (-2363, 1280), (-943, 512), (-147, 80),
  (-4693, 2560), (-2341, 1280), (-4671, 2560), (-233, 128),
  (-4649, 2560), (-2319, 1280), (-4627, 2560), (-577, 320),
  (-921, 512), (-2297, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_064 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 845..857 of piece `zneg` (q = 5). -/
def q5F_zneg_065_b : List QF := [
  (-2297, 1280), (-4583, 2560), (-1143, 640), (-4561, 2560),
  (-455, 256), (-4539, 2560), (-283, 160), (-4517, 2560),
  (-2253, 1280), (-899, 512), (-1121, 640), (-4473, 2560),
  (-2231, 1280), (-4451, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_065 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
