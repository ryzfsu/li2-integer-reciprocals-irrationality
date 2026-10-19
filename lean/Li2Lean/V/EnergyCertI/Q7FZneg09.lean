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

/-- Breakpoints of cells 702..714 of piece `zneg` (q = 7). -/
def q7F_zneg_054_b : List QF := [
  (-547, 160), (-273, 80), (-109, 32), (-17, 5),
  (-543, 160), (-271, 80), (-541, 160), (-27, 8),
  (-539, 160), (-269, 80), (-537, 160), (-67, 20),
  (-107, 32), (-267, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_054 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_054_b = true := by
  decide +kernel

/-- Breakpoints of cells 715..727 of piece `zneg` (q = 7). -/
def q7F_zneg_055_b : List QF := [
  (-267, 80), (-533, 160), (-133, 40), (-531, 160),
  (-53, 16), (-529, 160), (-33, 10), (-527, 160),
  (-263, 80), (-105, 32), (-131, 40), (-523, 160),
  (-261, 80), (-521, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_055 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_055_b = true := by
  decide +kernel

/-- Breakpoints of cells 728..740 of piece `zneg` (q = 7). -/
def q7F_zneg_056_b : List QF := [
  (-521, 160), (-13, 4), (-519, 160), (-259, 80),
  (-517, 160), (-129, 40), (-103, 32), (-257, 80),
  (-513, 160), (-16, 5), (-511, 160), (-51, 16),
  (-509, 160), (-127, 40)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_056 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 741..753 of piece `zneg` (q = 7). -/
def q7F_zneg_057_b : List QF := [
  (-127, 40), (-507, 160), (-253, 80), (-101, 32),
  (-63, 20), (-503, 160), (-251, 80), (-501, 160),
  (-25, 8), (-499, 160), (-249, 80), (-497, 160),
  (-31, 10), (-99, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_057 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 754..766 of piece `zneg` (q = 7). -/
def q7F_zneg_058_b : List QF := [
  (-99, 32), (-247, 80), (-493, 160), (-123, 40),
  (-491, 160), (-49, 16), (-489, 160), (-61, 20),
  (-487, 160), (-243, 80), (-97, 32), (-121, 40),
  (-483, 160), (-241, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_058 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 767..779 of piece `zneg` (q = 7). -/
def q7F_zneg_059_b : List QF := [
  (-241, 80), (-481, 160), (-3, 1), (-479, 160),
  (-239, 80), (-477, 160), (-119, 40), (-95, 32),
  (-237, 80), (-473, 160), (-59, 20), (-471, 160),
  (-47, 16), (-469, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_059 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_059_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
