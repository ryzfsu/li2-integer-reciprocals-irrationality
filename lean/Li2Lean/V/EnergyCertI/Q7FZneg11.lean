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

/-- Breakpoints of cells 858..870 of piece `zneg` (q = 7). -/
def q7F_zneg_066_b : List QF := [
  (-391, 160), (-39, 16), (-389, 160), (-97, 40),
  (-387, 160), (-193, 80), (-77, 32), (-12, 5),
  (-383, 160), (-191, 80), (-381, 160), (-19, 8),
  (-379, 160), (-189, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_066 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 871..883 of piece `zneg` (q = 7). -/
def q7F_zneg_067_b : List QF := [
  (-189, 80), (-377, 160), (-47, 20), (-75, 32),
  (-187, 80), (-373, 160), (-93, 40), (-371, 160),
  (-37, 16), (-369, 160), (-23, 10), (-367, 160),
  (-183, 80), (-73, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_067 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_067_b = true := by
  decide +kernel

/-- Breakpoints of cells 884..896 of piece `zneg` (q = 7). -/
def q7F_zneg_068_b : List QF := [
  (-73, 32), (-91, 40), (-363, 160), (-181, 80),
  (-361, 160), (-9, 4), (-359, 160), (-179, 80),
  (-357, 160), (-89, 40), (-71, 32), (-177, 80),
  (-353, 160), (-11, 5)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_068 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_068_b = true := by
  decide +kernel

/-- Breakpoints of cells 897..909 of piece `zneg` (q = 7). -/
def q7F_zneg_069_b : List QF := [
  (-11, 5), (-351, 160), (-35, 16), (-349, 160),
  (-87, 40), (-347, 160), (-173, 80), (-69, 32),
  (-43, 20), (-343, 160), (-171, 80), (-341, 160),
  (-17, 8), (-339, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_069 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_069_b = true := by
  decide +kernel

/-- Breakpoints of cells 910..922 of piece `zneg` (q = 7). -/
def q7F_zneg_070_b : List QF := [
  (-339, 160), (-169, 80), (-337, 160), (-21, 10),
  (-67, 32), (-167, 80), (-333, 160), (-83, 40),
  (-331, 160), (-33, 16), (-329, 160), (-41, 20),
  (-327, 160), (-163, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_070 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_070_b = true := by
  decide +kernel

/-- Breakpoints of cells 923..935 of piece `zneg` (q = 7). -/
def q7F_zneg_071_b : List QF := [
  (-163, 80), (-65, 32), (-81, 40), (-323, 160),
  (-161, 80), (-321, 160), (-2, 1), (-319, 160),
  (-159, 80), (-317, 160), (-79, 40), (-63, 32),
  (-157, 80), (-313, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_071 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_071_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
