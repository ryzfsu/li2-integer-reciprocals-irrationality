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

/-- Breakpoints of cells 468..480 of piece `zneg` (q = 7). -/
def q7F_zneg_036_b : List QF := [
  (-781, 160), (-39, 8), (-779, 160), (-389, 80),
  (-777, 160), (-97, 20), (-155, 32), (-387, 80),
  (-773, 160), (-193, 40), (-771, 160), (-77, 16),
  (-769, 160), (-24, 5)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_036 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 481..493 of piece `zneg` (q = 7). -/
def q7F_zneg_037_b : List QF := [
  (-24, 5), (-767, 160), (-383, 80), (-153, 32),
  (-191, 40), (-763, 160), (-381, 80), (-761, 160),
  (-19, 4), (-759, 160), (-379, 80), (-757, 160),
  (-189, 40), (-151, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_037 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 494..506 of piece `zneg` (q = 7). -/
def q7F_zneg_038_b : List QF := [
  (-151, 32), (-377, 80), (-753, 160), (-47, 10),
  (-751, 160), (-75, 16), (-749, 160), (-187, 40),
  (-747, 160), (-373, 80), (-149, 32), (-93, 20),
  (-743, 160), (-371, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_038 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 507..519 of piece `zneg` (q = 7). -/
def q7F_zneg_039_b : List QF := [
  (-371, 80), (-741, 160), (-37, 8), (-739, 160),
  (-369, 80), (-737, 160), (-23, 5), (-147, 32),
  (-367, 80), (-733, 160), (-183, 40), (-731, 160),
  (-73, 16), (-729, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_039 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..532 of piece `zneg` (q = 7). -/
def q7F_zneg_040_b : List QF := [
  (-729, 160), (-91, 20), (-727, 160), (-363, 80),
  (-145, 32), (-181, 40), (-723, 160), (-361, 80),
  (-721, 160), (-9, 2), (-719, 160), (-359, 80),
  (-717, 160), (-179, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_040 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 533..545 of piece `zneg` (q = 7). -/
def q7F_zneg_041_b : List QF := [
  (-179, 40), (-143, 32), (-357, 80), (-713, 160),
  (-89, 20), (-711, 160), (-71, 16), (-709, 160),
  (-177, 40), (-707, 160), (-353, 80), (-141, 32),
  (-22, 5), (-703, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_041 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
