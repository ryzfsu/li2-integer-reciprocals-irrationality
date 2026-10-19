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

/-- Breakpoints of cells 84..95 of piece `zneg` (q = 3). -/
def q3F_zneg_007_b : List QF := [
  (-3747, 1280), (-7491, 2560), (-117, 40), (-1497, 512),
  (-3741, 1280), (-7479, 2560), (-1869, 640), (-7473, 2560),
  (-747, 256), (-7467, 2560), (-933, 320), (-7461, 2560),
  (-3729, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_007 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..107 of piece `zneg` (q = 3). -/
def q3F_zneg_008_b : List QF := [
  (-3729, 1280), (-1863, 640), (-7449, 2560), (-3723, 1280),
  (-7443, 2560), (-93, 32), (-7437, 2560), (-3717, 1280),
  (-7431, 2560), (-1857, 640), (-1485, 512), (-3711, 1280),
  (-7419, 2560)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_008 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..119 of piece `zneg` (q = 3). -/
def q3F_zneg_009_b : List QF := [
  (-7419, 2560), (-927, 320), (-741, 256), (-1851, 640),
  (-3699, 1280), (-231, 80), (-3693, 1280), (-369, 128),
  (-3687, 1280), (-921, 320), (-3681, 1280), (-1839, 640),
  (-735, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_009 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..131 of piece `zneg` (q = 3). -/
def q3F_zneg_010_b : List QF := [
  (-735, 256), (-459, 160), (-3669, 1280), (-1833, 640),
  (-3663, 1280), (-183, 64), (-3657, 1280), (-1827, 640),
  (-3651, 1280), (-57, 20), (-729, 256), (-1821, 640),
  (-3639, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_010 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..143 of piece `zneg` (q = 3). -/
def q3F_zneg_011_b : List QF := [
  (-3639, 1280), (-909, 320), (-3633, 1280), (-363, 128),
  (-3627, 1280), (-453, 160), (-3621, 1280), (-1809, 640),
  (-723, 256), (-903, 320), (-3609, 1280), (-1803, 640),
  (-3603, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_011 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..155 of piece `zneg` (q = 3). -/
def q3F_zneg_012_b : List QF := [
  (-3603, 1280), (-45, 16), (-3597, 1280), (-1797, 640),
  (-3591, 1280), (-897, 320), (-717, 256), (-1791, 640),
  (-3579, 1280), (-447, 160), (-3573, 1280), (-357, 128),
  (-3567, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_012 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..167 of piece `zneg` (q = 3). -/
def q3F_zneg_013_b : List QF := [
  (-3567, 1280), (-891, 320), (-3561, 1280), (-1779, 640),
  (-711, 256), (-111, 40), (-3549, 1280), (-1773, 640),
  (-3543, 1280), (-177, 64), (-3537, 1280), (-1767, 640),
  (-3531, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_013 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
