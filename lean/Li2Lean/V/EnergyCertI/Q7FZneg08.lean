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

/-- Breakpoints of cells 624..636 of piece `zneg` (q = 7). -/
def q7F_zneg_048_b : List QF := [
  (-125, 32), (-39, 10), (-623, 160), (-311, 80),
  (-621, 160), (-31, 8), (-619, 160), (-309, 80),
  (-617, 160), (-77, 20), (-123, 32), (-307, 80),
  (-613, 160), (-153, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_048 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_048_b = true := by
  decide +kernel

/-- Breakpoints of cells 637..649 of piece `zneg` (q = 7). -/
def q7F_zneg_049_b : List QF := [
  (-153, 40), (-611, 160), (-61, 16), (-609, 160),
  (-19, 5), (-607, 160), (-303, 80), (-121, 32),
  (-151, 40), (-603, 160), (-301, 80), (-601, 160),
  (-15, 4), (-599, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_049 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..662 of piece `zneg` (q = 7). -/
def q7F_zneg_050_b : List QF := [
  (-599, 160), (-299, 80), (-597, 160), (-149, 40),
  (-119, 32), (-297, 80), (-593, 160), (-37, 10),
  (-591, 160), (-59, 16), (-589, 160), (-147, 40),
  (-587, 160), (-293, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_050 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 663..675 of piece `zneg` (q = 7). -/
def q7F_zneg_051_b : List QF := [
  (-293, 80), (-117, 32), (-73, 20), (-583, 160),
  (-291, 80), (-581, 160), (-29, 8), (-579, 160),
  (-289, 80), (-577, 160), (-18, 5), (-115, 32),
  (-287, 80), (-573, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_051 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 676..688 of piece `zneg` (q = 7). -/
def q7F_zneg_052_b : List QF := [
  (-573, 160), (-143, 40), (-571, 160), (-57, 16),
  (-569, 160), (-71, 20), (-567, 160), (-283, 80),
  (-113, 32), (-141, 40), (-563, 160), (-281, 80),
  (-561, 160), (-7, 2)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_052 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 689..701 of piece `zneg` (q = 7). -/
def q7F_zneg_053_b : List QF := [
  (-7, 2), (-559, 160), (-279, 80), (-557, 160),
  (-139, 40), (-111, 32), (-277, 80), (-553, 160),
  (-69, 20), (-551, 160), (-55, 16), (-549, 160),
  (-137, 40), (-547, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_053 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_053_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
