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

/-- Breakpoints of cells 252..263 of piece `zneg` (q = 3). -/
def q3F_zneg_021_b : List QF := [
  (-3279, 1280), (-819, 320), (-3273, 1280), (-327, 128),
  (-3267, 1280), (-51, 20), (-3261, 1280), (-1629, 640),
  (-651, 256), (-813, 320), (-3249, 1280), (-1623, 640),
  (-3243, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_021 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 264..275 of piece `zneg` (q = 3). -/
def q3F_zneg_022_b : List QF := [
  (-3243, 1280), (-81, 32), (-3237, 1280), (-1617, 640),
  (-3231, 1280), (-807, 320), (-645, 256), (-1611, 640),
  (-3219, 1280), (-201, 80), (-3213, 1280), (-321, 128),
  (-3207, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_022 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 276..287 of piece `zneg` (q = 3). -/
def q3F_zneg_023_b : List QF := [
  (-3207, 1280), (-801, 320), (-3201, 1280), (-1599, 640),
  (-639, 256), (-399, 160), (-3189, 1280), (-1593, 640),
  (-3183, 1280), (-159, 64), (-3177, 1280), (-1587, 640),
  (-3171, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_023 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 288..299 of piece `zneg` (q = 3). -/
def q3F_zneg_024_b : List QF := [
  (-3171, 1280), (-99, 40), (-633, 256), (-1581, 640),
  (-3159, 1280), (-789, 320), (-3153, 1280), (-315, 128),
  (-3147, 1280), (-393, 160), (-3141, 1280), (-1569, 640),
  (-627, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_024 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 300..311 of piece `zneg` (q = 3). -/
def q3F_zneg_025_b : List QF := [
  (-627, 256), (-783, 320), (-3129, 1280), (-1563, 640),
  (-3123, 1280), (-39, 16), (-3117, 1280), (-1557, 640),
  (-3111, 1280), (-777, 320), (-621, 256), (-1551, 640),
  (-3099, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_025 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 312..323 of piece `zneg` (q = 3). -/
def q3F_zneg_026_b : List QF := [
  (-3099, 1280), (-387, 160), (-3093, 1280), (-309, 128),
  (-3087, 1280), (-771, 320), (-3081, 1280), (-1539, 640),
  (-615, 256), (-12, 5), (-3069, 1280), (-1533, 640),
  (-3063, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_026 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 324..335 of piece `zneg` (q = 3). -/
def q3F_zneg_027_b : List QF := [
  (-3063, 1280), (-153, 64), (-3057, 1280), (-1527, 640),
  (-3051, 1280), (-381, 160), (-609, 256), (-1521, 640),
  (-3039, 1280), (-759, 320), (-3033, 1280), (-303, 128),
  (-3027, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_027 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
