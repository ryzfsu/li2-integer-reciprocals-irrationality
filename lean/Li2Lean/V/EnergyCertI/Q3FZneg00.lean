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

/-- Breakpoints of cells 0..11 of piece `zneg` (q = 3). -/
def q3F_zneg_000_b : List QF := [
  (-3, 1), (-61437, 20480), (-30717, 10240), (-15357, 5120),
  (-30711, 10240), (-7677, 2560), (-6141, 2048), (-15351, 5120),
  (-30699, 10240), (-3837, 1280), (-30693, 10240), (-3069, 1024),
  (-30687, 10240)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_000 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..23 of piece `zneg` (q = 3). -/
def q3F_zneg_001_b : List QF := [
  (-30687, 10240), (-7671, 2560), (-30681, 10240), (-15339, 5120),
  (-1917, 640), (-15333, 5120), (-1533, 512), (-15327, 5120),
  (-3831, 1280), (-15321, 5120), (-7659, 2560), (-3063, 1024),
  (-957, 320)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_001 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..35 of piece `zneg` (q = 3). -/
def q3F_zneg_002_b : List QF := [
  (-957, 320), (-15309, 5120), (-7653, 2560), (-15303, 5120),
  (-765, 256), (-15297, 5120), (-7647, 2560), (-15291, 5120),
  (-1911, 640), (-3057, 1024), (-7641, 2560), (-15279, 5120),
  (-3819, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_002 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..47 of piece `zneg` (q = 3). -/
def q3F_zneg_003_b : List QF := [
  (-3819, 1280), (-1527, 512), (-477, 160), (-7629, 2560),
  (-3813, 1280), (-7623, 2560), (-381, 128), (-7617, 2560),
  (-3807, 1280), (-7611, 2560), (-951, 320), (-1521, 512),
  (-3801, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_003 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..59 of piece `zneg` (q = 3). -/
def q3F_zneg_004_b : List QF := [
  (-3801, 1280), (-7599, 2560), (-1899, 640), (-7593, 2560),
  (-759, 256), (-7587, 2560), (-237, 80), (-7581, 2560),
  (-3789, 1280), (-1515, 512), (-1893, 640), (-7569, 2560),
  (-3783, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_004 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..71 of piece `zneg` (q = 3). -/
def q3F_zneg_005_b : List QF := [
  (-3783, 1280), (-7563, 2560), (-189, 64), (-7557, 2560),
  (-3777, 1280), (-7551, 2560), (-1887, 640), (-1509, 512),
  (-3771, 1280), (-7539, 2560), (-471, 160), (-7533, 2560),
  (-753, 256)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_005 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..83 of piece `zneg` (q = 3). -/
def q3F_zneg_006_b : List QF := [
  (-753, 256), (-7527, 2560), (-1881, 640), (-7521, 2560),
  (-3759, 1280), (-1503, 512), (-939, 320), (-7509, 2560),
  (-3753, 1280), (-7503, 2560), (-375, 128), (-7497, 2560),
  (-3747, 1280)]

/-- 12 cells, about 2244 transcendental evaluations (field mode). -/
theorem q3F_zneg_006 :
    cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) q3F_zneg_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
