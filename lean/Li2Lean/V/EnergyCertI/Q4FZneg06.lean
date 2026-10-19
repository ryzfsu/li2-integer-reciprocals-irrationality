/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 504..515 of piece `zneg` (q = 4). -/
def q4F_zneg_042_b : List QF := [
  (-13221, 5120), (-3301, 1280), (-13187, 5120), (-1317, 512),
  (-13153, 5120), (-821, 320), (-13119, 5120), (-6551, 2560),
  (-2617, 1024), (-3267, 1280), (-13051, 5120), (-6517, 2560),
  (-13017, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_042 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 516..527 of piece `zneg` (q = 4). -/
def q4F_zneg_043_b : List QF := [
  (-13017, 5120), (-325, 128), (-12983, 5120), (-6483, 2560),
  (-12949, 5120), (-3233, 1280), (-2583, 1024), (-6449, 2560),
  (-12881, 5120), (-201, 80), (-12847, 5120), (-1283, 512),
  (-12813, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_043 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 528..539 of piece `zneg` (q = 4). -/
def q4F_zneg_044_b : List QF := [
  (-12813, 5120), (-3199, 1280), (-12779, 5120), (-6381, 2560),
  (-2549, 1024), (-1591, 640), (-12711, 5120), (-6347, 2560),
  (-12677, 5120), (-633, 256), (-12643, 5120), (-6313, 2560),
  (-12609, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_044 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 540..551 of piece `zneg` (q = 4). -/
def q4F_zneg_045_b : List QF := [
  (-12609, 5120), (-787, 320), (-2515, 1024), (-6279, 2560),
  (-12541, 5120), (-3131, 1280), (-12507, 5120), (-1249, 512),
  (-12473, 5120), (-1557, 640), (-12439, 5120), (-6211, 2560),
  (-2481, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_045 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 552..563 of piece `zneg` (q = 4). -/
def q4F_zneg_046_b : List QF := [
  (-2481, 1024), (-3097, 1280), (-12371, 5120), (-6177, 2560),
  (-12337, 5120), (-77, 32), (-12303, 5120), (-6143, 2560),
  (-12269, 5120), (-3063, 1280), (-2447, 1024), (-6109, 2560),
  (-12201, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_046 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 564..575 of piece `zneg` (q = 4). -/
def q4F_zneg_047_b : List QF := [
  (-12201, 5120), (-1523, 640), (-12167, 5120), (-1215, 512),
  (-12133, 5120), (-3029, 1280), (-12099, 5120), (-6041, 2560),
  (-2413, 1024), (-753, 320), (-12031, 5120), (-6007, 2560),
  (-11997, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_047 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_047_b = true := by
  decide +kernel

/-- Breakpoints of cells 576..587 of piece `zneg` (q = 4). -/
def q4F_zneg_048_b : List QF := [
  (-11997, 5120), (-599, 256), (-11963, 5120), (-5973, 2560),
  (-11929, 5120), (-1489, 640), (-2379, 1024), (-5939, 2560),
  (-11861, 5120), (-2961, 1280), (-11827, 5120), (-1181, 512),
  (-11793, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_048 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
