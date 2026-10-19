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

/-- Breakpoints of cells 936..948 of piece `zneg` (q = 5). -/
def q5F_zneg_072_b : List QF := [
  (-3593, 2560), (-1791, 1280), (-3571, 2560), (-89, 64),
  (-3549, 2560), (-1769, 1280), (-3527, 2560), (-879, 640),
  (-701, 512), (-1747, 1280), (-3483, 2560), (-217, 160),
  (-3461, 2560), (-345, 256)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_072 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_072_b = true := by
  decide +kernel

/-- Breakpoints of cells 949..961 of piece `zneg` (q = 5). -/
def q5F_zneg_073_b : List QF := [
  (-345, 256), (-3439, 2560), (-857, 640), (-3417, 2560),
  (-1703, 1280), (-679, 512), (-423, 320), (-3373, 2560),
  (-1681, 1280), (-3351, 2560), (-167, 128), (-3329, 2560),
  (-1659, 1280), (-3307, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_073 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_073_b = true := by
  decide +kernel

/-- Breakpoints of cells 962..974 of piece `zneg` (q = 5). -/
def q5F_zneg_074_b : List QF := [
  (-3307, 2560), (-103, 80), (-657, 512), (-1637, 1280),
  (-3263, 2560), (-813, 640), (-3241, 2560), (-323, 256),
  (-3219, 2560), (-401, 320), (-3197, 2560), (-1593, 1280),
  (-635, 512), (-791, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_074 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_074_b = true := by
  decide +kernel

/-- Breakpoints of cells 975..987 of piece `zneg` (q = 5). -/
def q5F_zneg_075_b : List QF := [
  (-791, 640), (-3153, 2560), (-1571, 1280), (-3131, 2560),
  (-39, 32), (-3109, 2560), (-1549, 1280), (-3087, 2560),
  (-769, 640), (-613, 512), (-1527, 1280), (-3043, 2560),
  (-379, 320), (-3021, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_075 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_075_b = true := by
  decide +kernel

/-- Breakpoints of cells 988..1000 of piece `zneg` (q = 5). -/
def q5F_zneg_076_b : List QF := [
  (-3021, 2560), (-301, 256), (-2999, 2560), (-747, 640),
  (-2977, 2560), (-1483, 1280), (-591, 512), (-23, 20),
  (-2933, 2560), (-1461, 1280), (-2911, 2560), (-145, 128),
  (-2889, 2560), (-1439, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_076 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_076_b = true := by
  decide +kernel

/-- Breakpoints of cells 1001..1013 of piece `zneg` (q = 5). -/
def q5F_zneg_077_b : List QF := [
  (-1439, 1280), (-2867, 2560), (-357, 320), (-569, 512),
  (-1417, 1280), (-2823, 2560), (-703, 640), (-2801, 2560),
  (-279, 256), (-2779, 2560), (-173, 160), (-2757, 2560),
  (-1373, 1280), (-547, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_077 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_077_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
