/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 312..324 of piece `zneg` (q = 5). -/
def q5F_zneg_024_b : List QF := [
  (-10457, 2560), (-5223, 1280), (-2087, 512), (-1303, 320),
  (-10413, 2560), (-5201, 1280), (-10391, 2560), (-519, 128),
  (-10369, 2560), (-5179, 1280), (-10347, 2560), (-323, 80),
  (-2065, 512), (-5157, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_024 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 325..337 of piece `zneg` (q = 5). -/
def q5F_zneg_025_b : List QF := [
  (-5157, 1280), (-10303, 2560), (-2573, 640), (-10281, 2560),
  (-1027, 256), (-10259, 2560), (-1281, 320), (-10237, 2560),
  (-5113, 1280), (-2043, 512), (-2551, 640), (-10193, 2560),
  (-5091, 1280), (-10171, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_025 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 338..350 of piece `zneg` (q = 5). -/
def q5F_zneg_026_b : List QF := [
  (-10171, 2560), (-127, 32), (-10149, 2560), (-5069, 1280),
  (-10127, 2560), (-2529, 640), (-2021, 512), (-5047, 1280),
  (-10083, 2560), (-1259, 320), (-10061, 2560), (-1005, 256),
  (-10039, 2560), (-2507, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_026 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 351..363 of piece `zneg` (q = 5). -/
def q5F_zneg_027_b : List QF := [
  (-2507, 640), (-10017, 2560), (-5003, 1280), (-1999, 512),
  (-39, 10), (-9973, 2560), (-4981, 1280), (-9951, 2560),
  (-497, 128), (-9929, 2560), (-4959, 1280), (-9907, 2560),
  (-1237, 320), (-1977, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_027 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_027_b = true := by
  decide +kernel

/-- Breakpoints of cells 364..376 of piece `zneg` (q = 5). -/
def q5F_zneg_028_b : List QF := [
  (-1977, 512), (-4937, 1280), (-9863, 2560), (-2463, 640),
  (-9841, 2560), (-983, 256), (-9819, 2560), (-613, 160),
  (-9797, 2560), (-4893, 1280), (-1955, 512), (-2441, 640),
  (-9753, 2560), (-4871, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_028 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 377..389 of piece `zneg` (q = 5). -/
def q5F_zneg_029_b : List QF := [
  (-4871, 1280), (-9731, 2560), (-243, 64), (-9709, 2560),
  (-4849, 1280), (-9687, 2560), (-2419, 640), (-1933, 512),
  (-4827, 1280), (-9643, 2560), (-301, 80), (-9621, 2560),
  (-961, 256), (-9599, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_029 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_029_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
