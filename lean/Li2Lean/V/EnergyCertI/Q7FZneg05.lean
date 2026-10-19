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

/-- Breakpoints of cells 390..402 of piece `zneg` (q = 7). -/
def q7F_zneg_030_b : List QF := [
  (-859, 160), (-429, 80), (-857, 160), (-107, 20),
  (-171, 32), (-427, 80), (-853, 160), (-213, 40),
  (-851, 160), (-85, 16), (-849, 160), (-53, 10),
  (-847, 160), (-423, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_030 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_030_b = true := by
  decide +kernel

/-- Breakpoints of cells 403..415 of piece `zneg` (q = 7). -/
def q7F_zneg_031_b : List QF := [
  (-423, 80), (-169, 32), (-211, 40), (-843, 160),
  (-421, 80), (-841, 160), (-21, 4), (-839, 160),
  (-419, 80), (-837, 160), (-209, 40), (-167, 32),
  (-417, 80), (-833, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_031 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_031_b = true := by
  decide +kernel

/-- Breakpoints of cells 416..428 of piece `zneg` (q = 7). -/
def q7F_zneg_032_b : List QF := [
  (-833, 160), (-26, 5), (-831, 160), (-83, 16),
  (-829, 160), (-207, 40), (-827, 160), (-413, 80),
  (-165, 32), (-103, 20), (-823, 160), (-411, 80),
  (-821, 160), (-41, 8)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_032 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_032_b = true := by
  decide +kernel

/-- Breakpoints of cells 429..441 of piece `zneg` (q = 7). -/
def q7F_zneg_033_b : List QF := [
  (-41, 8), (-819, 160), (-409, 80), (-817, 160),
  (-51, 10), (-163, 32), (-407, 80), (-813, 160),
  (-203, 40), (-811, 160), (-81, 16), (-809, 160),
  (-101, 20), (-807, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_033 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_033_b = true := by
  decide +kernel

/-- Breakpoints of cells 442..454 of piece `zneg` (q = 7). -/
def q7F_zneg_034_b : List QF := [
  (-807, 160), (-403, 80), (-161, 32), (-201, 40),
  (-803, 160), (-401, 80), (-801, 160), (-5, 1),
  (-799, 160), (-399, 80), (-797, 160), (-199, 40),
  (-159, 32), (-397, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_034 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_034_b = true := by
  decide +kernel

/-- Breakpoints of cells 455..467 of piece `zneg` (q = 7). -/
def q7F_zneg_035_b : List QF := [
  (-397, 80), (-793, 160), (-99, 20), (-791, 160),
  (-79, 16), (-789, 160), (-197, 40), (-787, 160),
  (-393, 80), (-157, 32), (-49, 10), (-783, 160),
  (-391, 80), (-781, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_035 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_035_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
