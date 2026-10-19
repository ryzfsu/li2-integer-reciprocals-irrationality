/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 420..431 of piece `zneg` (q = 2). -/
def q2F_zneg_035_b : List QF := [
  (-1489, 1280), (-2971, 2560), (-741, 640), (-2957, 2560),
  (-295, 256), (-2943, 2560), (-367, 320), (-2929, 2560),
  (-1461, 1280), (-583, 512), (-727, 640), (-2901, 2560),
  (-1447, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_035 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_035_b = true := by
  decide +kernel

/-- Breakpoints of cells 432..443 of piece `zneg` (q = 2). -/
def q2F_zneg_036_b : List QF := [
  (-1447, 1280), (-2887, 2560), (-9, 8), (-2873, 2560),
  (-1433, 1280), (-2859, 2560), (-713, 640), (-569, 512),
  (-1419, 1280), (-2831, 2560), (-353, 320), (-2817, 2560),
  (-281, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_036 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 444..455 of piece `zneg` (q = 2). -/
def q2F_zneg_037_b : List QF := [
  (-281, 256), (-2803, 2560), (-699, 640), (-2789, 2560),
  (-1391, 1280), (-555, 512), (-173, 160), (-2761, 2560),
  (-1377, 1280), (-2747, 2560), (-137, 128), (-2733, 2560),
  (-1363, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_037 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 456..467 of piece `zneg` (q = 2). -/
def q2F_zneg_038_b : List QF := [
  (-1363, 1280), (-2719, 2560), (-339, 320), (-541, 512),
  (-1349, 1280), (-2691, 2560), (-671, 640), (-2677, 2560),
  (-267, 256), (-2663, 2560), (-83, 80), (-2649, 2560),
  (-1321, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_038 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 468..479 of piece `zneg` (q = 2). -/
def q2F_zneg_039_b : List QF := [
  (-1321, 1280), (-527, 512), (-657, 640), (-2621, 2560),
  (-1307, 1280), (-2607, 2560), (-65, 64), (-2593, 2560),
  (-1293, 1280), (-2579, 2560), (-643, 640), (-513, 512),
  (-1279, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_039 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 480..491 of piece `zneg` (q = 2). -/
def q2F_zneg_040_b : List QF := [
  (-1279, 1280), (-2551, 2560), (-159, 160), (-2537, 2560),
  (-253, 256), (-2523, 2560), (-629, 640), (-2509, 2560),
  (-1251, 1280), (-499, 512), (-311, 320), (-2481, 2560),
  (-1237, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_040 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 492..503 of piece `zneg` (q = 2). -/
def q2F_zneg_041_b : List QF := [
  (-1237, 1280), (-2467, 2560), (-123, 128), (-2453, 2560),
  (-1223, 1280), (-2439, 2560), (-19, 20), (-485, 512),
  (-1209, 1280), (-2411, 2560), (-601, 640), (-2397, 2560),
  (-239, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_041 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
