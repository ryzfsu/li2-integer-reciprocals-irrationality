/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 468..480 of piece `zneg` (q = 6). -/
def q6F_zneg_036_b : List QF := [
  (-663, 160), (-21189, 5120), (-10581, 2560), (-4227, 1024),
  (-5277, 1280), (-21081, 5120), (-10527, 2560), (-21027, 5120),
  (-525, 128), (-20973, 5120), (-10473, 2560), (-20919, 5120),
  (-5223, 1280), (-4173, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_036 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_036_b = true := by
  decide +kernel

/-- Breakpoints of cells 481..493 of piece `zneg` (q = 6). -/
def q6F_zneg_037_b : List QF := [
  (-4173, 1024), (-10419, 2560), (-20811, 5120), (-1299, 320),
  (-20757, 5120), (-2073, 512), (-20703, 5120), (-5169, 1280),
  (-20649, 5120), (-10311, 2560), (-4119, 1024), (-2571, 640),
  (-20541, 5120), (-10257, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_037 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_037_b = true := by
  decide +kernel

/-- Breakpoints of cells 494..506 of piece `zneg` (q = 6). -/
def q6F_zneg_038_b : List QF := [
  (-10257, 2560), (-20487, 5120), (-1023, 256), (-20433, 5120),
  (-10203, 2560), (-20379, 5120), (-159, 40), (-4065, 1024),
  (-10149, 2560), (-20271, 5120), (-5061, 1280), (-20217, 5120),
  (-2019, 512), (-20163, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_038 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_038_b = true := by
  decide +kernel

/-- Breakpoints of cells 507..519 of piece `zneg` (q = 6). -/
def q6F_zneg_039_b : List QF := [
  (-20163, 5120), (-2517, 640), (-20109, 5120), (-10041, 2560),
  (-4011, 1024), (-5007, 1280), (-20001, 5120), (-9987, 2560),
  (-19947, 5120), (-249, 64), (-19893, 5120), (-9933, 2560),
  (-19839, 5120), (-4953, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_039 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_039_b = true := by
  decide +kernel

/-- Breakpoints of cells 520..532 of piece `zneg` (q = 6). -/
def q6F_zneg_040_b : List QF := [
  (-4953, 1280), (-3957, 1024), (-9879, 2560), (-19731, 5120),
  (-2463, 640), (-19677, 5120), (-1965, 512), (-19623, 5120),
  (-4899, 1280), (-19569, 5120), (-9771, 2560), (-3903, 1024),
  (-609, 160), (-19461, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_040 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_040_b = true := by
  decide +kernel

/-- Breakpoints of cells 533..545 of piece `zneg` (q = 6). -/
def q6F_zneg_041_b : List QF := [
  (-19461, 5120), (-9717, 2560), (-19407, 5120), (-969, 256),
  (-19353, 5120), (-9663, 2560), (-19299, 5120), (-2409, 640),
  (-3849, 1024), (-9609, 2560), (-19191, 5120), (-4791, 1280),
  (-19137, 5120), (-1911, 512)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_041 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_041_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
