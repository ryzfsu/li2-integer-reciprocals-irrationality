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

/-- Breakpoints of cells 156..168 of piece `zneg` (q = 5). -/
def q5F_zneg_012_b : List QF := [
  (-12129, 2560), (-24247, 5120), (-6059, 1280), (-4845, 1024),
  (-12107, 2560), (-189, 40), (-2417, 512), (-6037, 1280),
  (-12063, 2560), (-3013, 640), (-12041, 2560), (-1203, 256),
  (-24049, 5120), (-12019, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_012 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 169..181 of piece `zneg` (q = 5). -/
def q5F_zneg_013_b : List QF := [
  (-12019, 2560), (-24027, 5120), (-1501, 320), (-11997, 2560),
  (-5993, 1280), (-2395, 512), (-2991, 640), (-11953, 2560),
  (-5971, 1280), (-11931, 2560), (-149, 32), (-11909, 2560),
  (-5949, 1280), (-11887, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_013 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_013_b = true := by
  decide +kernel

/-- Breakpoints of cells 182..194 of piece `zneg` (q = 5). -/
def q5F_zneg_014_b : List QF := [
  (-11887, 2560), (-2969, 640), (-2373, 512), (-5927, 1280),
  (-11843, 2560), (-1479, 320), (-11821, 2560), (-1181, 256),
  (-11799, 2560), (-2947, 640), (-11777, 2560), (-5883, 1280),
  (-2351, 512), (-367, 80)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_014 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 195..207 of piece `zneg` (q = 5). -/
def q5F_zneg_015_b : List QF := [
  (-367, 80), (-11733, 2560), (-5861, 1280), (-11711, 2560),
  (-585, 128), (-11689, 2560), (-5839, 1280), (-11667, 2560),
  (-1457, 320), (-2329, 512), (-5817, 1280), (-11623, 2560),
  (-2903, 640), (-11601, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_015 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 208..220 of piece `zneg` (q = 5). -/
def q5F_zneg_016_b : List QF := [
  (-11601, 2560), (-1159, 256), (-11579, 2560), (-723, 160),
  (-11557, 2560), (-5773, 1280), (-2307, 512), (-2881, 640),
  (-11513, 2560), (-5751, 1280), (-11491, 2560), (-287, 64),
  (-11469, 2560), (-5729, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_016 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 221..233 of piece `zneg` (q = 5). -/
def q5F_zneg_017_b : List QF := [
  (-5729, 1280), (-11447, 2560), (-2859, 640), (-2285, 512),
  (-5707, 1280), (-11403, 2560), (-89, 20), (-11381, 2560),
  (-1137, 256), (-11359, 2560), (-2837, 640), (-11337, 2560),
  (-5663, 1280), (-2263, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_017 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_017_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
