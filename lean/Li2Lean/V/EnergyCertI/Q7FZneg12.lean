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

/-- Breakpoints of cells 936..948 of piece `zneg` (q = 7). -/
def q7F_zneg_072_b : List QF := [
  (-313, 160), (-39, 20), (-311, 160), (-31, 16),
  (-309, 160), (-77, 40), (-307, 160), (-153, 80),
  (-61, 32), (-19, 10), (-303, 160), (-151, 80),
  (-301, 160), (-15, 8)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_072 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_072_b = true := by
  decide +kernel

/-- Breakpoints of cells 949..961 of piece `zneg` (q = 7). -/
def q7F_zneg_073_b : List QF := [
  (-15, 8), (-299, 160), (-149, 80), (-297, 160),
  (-37, 20), (-59, 32), (-147, 80), (-293, 160),
  (-73, 40), (-291, 160), (-29, 16), (-289, 160),
  (-9, 5), (-287, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_073 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_073_b = true := by
  decide +kernel

/-- Breakpoints of cells 962..974 of piece `zneg` (q = 7). -/
def q7F_zneg_074_b : List QF := [
  (-287, 160), (-143, 80), (-57, 32), (-71, 40),
  (-283, 160), (-141, 80), (-281, 160), (-7, 4),
  (-279, 160), (-139, 80), (-277, 160), (-69, 40),
  (-55, 32), (-137, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_074 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_074_b = true := by
  decide +kernel

/-- Breakpoints of cells 975..987 of piece `zneg` (q = 7). -/
def q7F_zneg_075_b : List QF := [
  (-137, 80), (-273, 160), (-17, 10), (-271, 160),
  (-27, 16), (-269, 160), (-67, 40), (-267, 160),
  (-133, 80), (-53, 32), (-33, 20), (-263, 160),
  (-131, 80), (-261, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_075 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_075_b = true := by
  decide +kernel

/-- Breakpoints of cells 988..1000 of piece `zneg` (q = 7). -/
def q7F_zneg_076_b : List QF := [
  (-261, 160), (-13, 8), (-259, 160), (-129, 80),
  (-257, 160), (-8, 5), (-51, 32), (-127, 80),
  (-253, 160), (-63, 40), (-251, 160), (-25, 16),
  (-249, 160), (-31, 20)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_076 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_076_b = true := by
  decide +kernel

/-- Breakpoints of cells 1001..1013 of piece `zneg` (q = 7). -/
def q7F_zneg_077_b : List QF := [
  (-31, 20), (-247, 160), (-123, 80), (-49, 32),
  (-61, 40), (-243, 160), (-121, 80), (-241, 160),
  (-3, 2), (-239, 160), (-119, 80), (-237, 160),
  (-59, 40), (-47, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_077 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_077_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
