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

/-- Breakpoints of cells 1014..1026 of piece `zneg` (q = 7). -/
def q7F_zneg_078_b : List QF := [
  (-47, 32), (-117, 80), (-233, 160), (-29, 20),
  (-231, 160), (-23, 16), (-229, 160), (-57, 40),
  (-227, 160), (-113, 80), (-45, 32), (-7, 5),
  (-223, 160), (-111, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_078 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_078_b = true := by
  decide +kernel

/-- Breakpoints of cells 1027..1039 of piece `zneg` (q = 7). -/
def q7F_zneg_079_b : List QF := [
  (-111, 80), (-221, 160), (-11, 8), (-219, 160),
  (-109, 80), (-217, 160), (-27, 20), (-43, 32),
  (-107, 80), (-213, 160), (-53, 40), (-211, 160),
  (-21, 16), (-209, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_079 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_079_b = true := by
  decide +kernel

/-- Breakpoints of cells 1040..1052 of piece `zneg` (q = 7). -/
def q7F_zneg_080_b : List QF := [
  (-209, 160), (-13, 10), (-207, 160), (-103, 80),
  (-41, 32), (-51, 40), (-203, 160), (-101, 80),
  (-201, 160), (-5, 4), (-199, 160), (-99, 80),
  (-197, 160), (-49, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_080 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_080_b = true := by
  decide +kernel

/-- Breakpoints of cells 1053..1065 of piece `zneg` (q = 7). -/
def q7F_zneg_081_b : List QF := [
  (-49, 40), (-39, 32), (-97, 80), (-193, 160),
  (-6, 5), (-191, 160), (-19, 16), (-189, 160),
  (-47, 40), (-187, 160), (-93, 80), (-37, 32),
  (-23, 20), (-183, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_081 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_081_b = true := by
  decide +kernel

/-- Breakpoints of cells 1066..1078 of piece `zneg` (q = 7). -/
def q7F_zneg_082_b : List QF := [
  (-183, 160), (-91, 80), (-181, 160), (-9, 8),
  (-179, 160), (-89, 80), (-177, 160), (-11, 10),
  (-35, 32), (-87, 80), (-173, 160), (-43, 40),
  (-171, 160), (-17, 16)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_082 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_082_b = true := by
  decide +kernel

/-- Breakpoints of cells 1079..1091 of piece `zneg` (q = 7). -/
def q7F_zneg_083_b : List QF := [
  (-17, 16), (-169, 160), (-21, 20), (-167, 160),
  (-83, 80), (-33, 32), (-41, 40), (-163, 160),
  (-81, 80), (-161, 160), (-1, 1), (-159, 160),
  (-79, 80), (-157, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_083 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_083_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
