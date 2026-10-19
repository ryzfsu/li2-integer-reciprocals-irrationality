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

/-- Breakpoints of cells 780..792 of piece `zneg` (q = 7). -/
def q7F_zneg_060_b : List QF := [
  (-469, 160), (-117, 40), (-467, 160), (-233, 80),
  (-93, 32), (-29, 10), (-463, 160), (-231, 80),
  (-461, 160), (-23, 8), (-459, 160), (-229, 80),
  (-457, 160), (-57, 20)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_060 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 793..805 of piece `zneg` (q = 7). -/
def q7F_zneg_061_b : List QF := [
  (-57, 20), (-91, 32), (-227, 80), (-453, 160),
  (-113, 40), (-451, 160), (-45, 16), (-449, 160),
  (-14, 5), (-447, 160), (-223, 80), (-89, 32),
  (-111, 40), (-443, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_061 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_061_b = true := by
  decide +kernel

/-- Breakpoints of cells 806..818 of piece `zneg` (q = 7). -/
def q7F_zneg_062_b : List QF := [
  (-443, 160), (-221, 80), (-441, 160), (-11, 4),
  (-439, 160), (-219, 80), (-437, 160), (-109, 40),
  (-87, 32), (-217, 80), (-433, 160), (-27, 10),
  (-431, 160), (-43, 16)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_062 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_062_b = true := by
  decide +kernel

/-- Breakpoints of cells 819..831 of piece `zneg` (q = 7). -/
def q7F_zneg_063_b : List QF := [
  (-43, 16), (-429, 160), (-107, 40), (-427, 160),
  (-213, 80), (-85, 32), (-53, 20), (-423, 160),
  (-211, 80), (-421, 160), (-21, 8), (-419, 160),
  (-209, 80), (-417, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_063 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 832..844 of piece `zneg` (q = 7). -/
def q7F_zneg_064_b : List QF := [
  (-417, 160), (-13, 5), (-83, 32), (-207, 80),
  (-413, 160), (-103, 40), (-411, 160), (-41, 16),
  (-409, 160), (-51, 20), (-407, 160), (-203, 80),
  (-81, 32), (-101, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_064 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 845..857 of piece `zneg` (q = 7). -/
def q7F_zneg_065_b : List QF := [
  (-101, 40), (-403, 160), (-201, 80), (-401, 160),
  (-5, 2), (-399, 160), (-199, 80), (-397, 160),
  (-99, 40), (-79, 32), (-197, 80), (-393, 160),
  (-49, 20), (-391, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_065 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_065_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
