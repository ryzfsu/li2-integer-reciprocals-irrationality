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

/-- Breakpoints of cells 546..558 of piece `zneg` (q = 7). -/
def q7F_zneg_042_b : List QF := [
  (-703, 160), (-351, 80), (-701, 160), (-35, 8),
  (-699, 160), (-349, 80), (-697, 160), (-87, 20),
  (-139, 32), (-347, 80), (-693, 160), (-173, 40),
  (-691, 160), (-69, 16)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_042 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 559..571 of piece `zneg` (q = 7). -/
def q7F_zneg_043_b : List QF := [
  (-69, 16), (-689, 160), (-43, 10), (-687, 160),
  (-343, 80), (-137, 32), (-171, 40), (-683, 160),
  (-341, 80), (-681, 160), (-17, 4), (-679, 160),
  (-339, 80), (-677, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_043 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 572..584 of piece `zneg` (q = 7). -/
def q7F_zneg_044_b : List QF := [
  (-677, 160), (-169, 40), (-135, 32), (-337, 80),
  (-673, 160), (-21, 5), (-671, 160), (-67, 16),
  (-669, 160), (-167, 40), (-667, 160), (-333, 80),
  (-133, 32), (-83, 20)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_044 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 585..597 of piece `zneg` (q = 7). -/
def q7F_zneg_045_b : List QF := [
  (-83, 20), (-663, 160), (-331, 80), (-661, 160),
  (-33, 8), (-659, 160), (-329, 80), (-657, 160),
  (-41, 10), (-131, 32), (-327, 80), (-653, 160),
  (-163, 40), (-651, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_045 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 598..610 of piece `zneg` (q = 7). -/
def q7F_zneg_046_b : List QF := [
  (-651, 160), (-65, 16), (-649, 160), (-81, 20),
  (-647, 160), (-323, 80), (-129, 32), (-161, 40),
  (-643, 160), (-321, 80), (-641, 160), (-4, 1),
  (-639, 160), (-319, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_046 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 611..623 of piece `zneg` (q = 7). -/
def q7F_zneg_047_b : List QF := [
  (-319, 80), (-637, 160), (-159, 40), (-127, 32),
  (-317, 80), (-633, 160), (-79, 20), (-631, 160),
  (-63, 16), (-629, 160), (-157, 40), (-627, 160),
  (-313, 80), (-125, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_047 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_047_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
