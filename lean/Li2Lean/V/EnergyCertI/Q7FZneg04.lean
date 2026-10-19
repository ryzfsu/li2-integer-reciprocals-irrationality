/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 312..324 of piece `zneg` (q = 7). -/
def q7F_zneg_024_b : List QF := [
  (-937, 160), (-117, 20), (-187, 32), (-467, 80),
  (-933, 160), (-233, 40), (-931, 160), (-93, 16),
  (-929, 160), (-29, 5), (-927, 160), (-463, 80),
  (-185, 32), (-231, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_024 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 325..337 of piece `zneg` (q = 7). -/
def q7F_zneg_025_b : List QF := [
  (-231, 40), (-923, 160), (-461, 80), (-921, 160),
  (-23, 4), (-919, 160), (-459, 80), (-917, 160),
  (-229, 40), (-183, 32), (-457, 80), (-913, 160),
  (-57, 10), (-911, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_025 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 338..350 of piece `zneg` (q = 7). -/
def q7F_zneg_026_b : List QF := [
  (-911, 160), (-91, 16), (-909, 160), (-227, 40),
  (-907, 160), (-453, 80), (-181, 32), (-113, 20),
  (-903, 160), (-451, 80), (-901, 160), (-45, 8),
  (-899, 160), (-449, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_026 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 351..363 of piece `zneg` (q = 7). -/
def q7F_zneg_027_b : List QF := [
  (-449, 80), (-897, 160), (-28, 5), (-179, 32),
  (-447, 80), (-893, 160), (-223, 40), (-891, 160),
  (-89, 16), (-889, 160), (-111, 20), (-887, 160),
  (-443, 80), (-177, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_027 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_027_b = true := by
  decide +kernel

/-- Breakpoints of cells 364..376 of piece `zneg` (q = 7). -/
def q7F_zneg_028_b : List QF := [
  (-177, 32), (-221, 40), (-883, 160), (-441, 80),
  (-881, 160), (-11, 2), (-879, 160), (-439, 80),
  (-877, 160), (-219, 40), (-175, 32), (-437, 80),
  (-873, 160), (-109, 20)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_028 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 377..389 of piece `zneg` (q = 7). -/
def q7F_zneg_029_b : List QF := [
  (-109, 20), (-871, 160), (-87, 16), (-869, 160),
  (-217, 40), (-867, 160), (-433, 80), (-173, 32),
  (-27, 5), (-863, 160), (-431, 80), (-861, 160),
  (-43, 8), (-859, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_029 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_029_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
