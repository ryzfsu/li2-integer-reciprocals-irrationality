/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 672..683 of piece `zneg` (q = 3). -/
def q3F_zneg_056_b : List QF := [
  (-9, 10), (-573, 640), (-57, 64), (-567, 640),
  (-141, 160), (-561, 640), (-279, 320), (-111, 128),
  (-69, 80), (-549, 640), (-273, 320), (-543, 640),
  (-27, 32)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_056 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_056_b = true := by
  decide +kernel

/-- Breakpoints of cells 684..695 of piece `zneg` (q = 3). -/
def q3F_zneg_057_b : List QF := [
  (-27, 32), (-537, 640), (-267, 320), (-531, 640),
  (-33, 40), (-105, 128), (-261, 320), (-519, 640),
  (-129, 160), (-513, 640), (-51, 64), (-507, 640),
  (-63, 80)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_057 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_057_b = true := by
  decide +kernel

/-- Breakpoints of cells 696..707 of piece `zneg` (q = 3). -/
def q3F_zneg_058_b : List QF := [
  (-63, 80), (-501, 640), (-249, 320), (-99, 128),
  (-123, 160), (-489, 640), (-243, 320), (-483, 640),
  (-3, 4), (-477, 640), (-237, 320), (-471, 640),
  (-117, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_058 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_058_b = true := by
  decide +kernel

/-- Breakpoints of cells 708..719 of piece `zneg` (q = 3). -/
def q3F_zneg_059_b : List QF := [
  (-117, 160), (-93, 128), (-231, 320), (-459, 640),
  (-57, 80), (-453, 640), (-45, 64), (-447, 640),
  (-111, 160), (-441, 640), (-219, 320), (-87, 128),
  (-27, 40)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_059 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_059_b = true := by
  decide +kernel

/-- Breakpoints of cells 720..731 of piece `zneg` (q = 3). -/
def q3F_zneg_060_b : List QF := [
  (-27, 40), (-429, 640), (-213, 320), (-423, 640),
  (-21, 32), (-417, 640), (-207, 320), (-411, 640),
  (-51, 80), (-81, 128), (-201, 320), (-399, 640),
  (-99, 160)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_060 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_060_b = true := by
  decide +kernel

/-- Breakpoints of cells 732..735 of piece `zneg` (q = 3). -/
def q3F_zneg_061_b : List QF := [
  (-99, 160), (-393, 640), (-39, 64), (-387, 640),
  (-3, 5)]

/-- 4 cells, about 748 transcendental evaluations (field mode). -/
theorem q3F_zneg_061 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_061_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
