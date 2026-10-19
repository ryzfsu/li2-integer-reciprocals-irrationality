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

/-- Breakpoints of cells 1092..1104 of piece `zneg` (q = 7). -/
def q7F_zneg_084_b : List QF := [
  (-157, 160), (-39, 40), (-31, 32), (-77, 80),
  (-153, 160), (-19, 20), (-151, 160), (-15, 16),
  (-149, 160), (-37, 40), (-147, 160), (-73, 80),
  (-29, 32), (-9, 10)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_084 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_084_b = true := by
  decide +kernel

/-- Breakpoints of cells 1105..1117 of piece `zneg` (q = 7). -/
def q7F_zneg_085_b : List QF := [
  (-9, 10), (-143, 160), (-71, 80), (-141, 160),
  (-7, 8), (-139, 160), (-69, 80), (-137, 160),
  (-17, 20), (-27, 32), (-67, 80), (-267, 320),
  (-133, 160), (-53, 64)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_085 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_085_b = true := by
  decide +kernel

/-- Breakpoints of cells 1118..1130 of piece `zneg` (q = 7). -/
def q7F_zneg_086_b : List QF := [
  (-53, 64), (-33, 40), (-263, 320), (-131, 160),
  (-261, 320), (-13, 16), (-259, 320), (-129, 160),
  (-257, 320), (-4, 5), (-51, 64), (-127, 160),
  (-253, 320), (-63, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_086 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_086_b = true := by
  decide +kernel

/-- Breakpoints of cells 1131..1143 of piece `zneg` (q = 7). -/
def q7F_zneg_087_b : List QF := [
  (-63, 80), (-251, 320), (-25, 32), (-249, 320),
  (-31, 40), (-247, 320), (-123, 160), (-49, 64),
  (-61, 80), (-243, 320), (-121, 160), (-241, 320),
  (-3, 4), (-239, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_087 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_087_b = true := by
  decide +kernel

/-- Breakpoints of cells 1144..1156 of piece `zneg` (q = 7). -/
def q7F_zneg_088_b : List QF := [
  (-239, 320), (-119, 160), (-237, 320), (-59, 80),
  (-47, 64), (-117, 160), (-233, 320), (-29, 40),
  (-231, 320), (-23, 32), (-229, 320), (-57, 80),
  (-227, 320), (-113, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_088 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_088_b = true := by
  decide +kernel

/-- Breakpoints of cells 1157..1169 of piece `zneg` (q = 7). -/
def q7F_zneg_089_b : List QF := [
  (-113, 160), (-45, 64), (-7, 10), (-223, 320),
  (-111, 160), (-221, 320), (-11, 16), (-219, 320),
  (-109, 160), (-217, 320), (-27, 40), (-43, 64),
  (-107, 160), (-213, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_089 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_089_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
