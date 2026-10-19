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

/-- Breakpoints of cells 504..515 of piece `zneg` (q = 2). -/
def q2F_zneg_042_b : List QF := [
  (-239, 256), (-2383, 2560), (-297, 320), (-2369, 2560),
  (-1181, 1280), (-471, 512), (-587, 640), (-2341, 2560),
  (-1167, 1280), (-2327, 2560), (-29, 32), (-2313, 2560),
  (-1153, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_042 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 516..527 of piece `zneg` (q = 2). -/
def q2F_zneg_043_b : List QF := [
  (-1153, 1280), (-2299, 2560), (-573, 640), (-457, 512),
  (-1139, 1280), (-2271, 2560), (-283, 320), (-2257, 2560),
  (-225, 256), (-2243, 2560), (-559, 640), (-2229, 2560),
  (-1111, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_043 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 528..539 of piece `zneg` (q = 2). -/
def q2F_zneg_044_b : List QF := [
  (-1111, 1280), (-443, 512), (-69, 80), (-2201, 2560),
  (-1097, 1280), (-2187, 2560), (-109, 128), (-2173, 2560),
  (-1083, 1280), (-2159, 2560), (-269, 320), (-429, 512),
  (-1069, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_044 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_044_b = true := by
  decide +kernel

/-- Breakpoints of cells 540..551 of piece `zneg` (q = 2). -/
def q2F_zneg_045_b : List QF := [
  (-1069, 1280), (-2131, 2560), (-531, 640), (-2117, 2560),
  (-211, 256), (-2103, 2560), (-131, 160), (-2089, 2560),
  (-1041, 1280), (-415, 512), (-517, 640), (-2061, 2560),
  (-1027, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_045 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_045_b = true := by
  decide +kernel

/-- Breakpoints of cells 552..563 of piece `zneg` (q = 2). -/
def q2F_zneg_046_b : List QF := [
  (-1027, 1280), (-2047, 2560), (-51, 64), (-2033, 2560),
  (-1013, 1280), (-2019, 2560), (-503, 640), (-401, 512),
  (-999, 1280), (-1991, 2560), (-31, 40), (-1977, 2560),
  (-197, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_046 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_046_b = true := by
  decide +kernel

/-- Breakpoints of cells 564..575 of piece `zneg` (q = 2). -/
def q2F_zneg_047_b : List QF := [
  (-197, 256), (-1963, 2560), (-489, 640), (-1949, 2560),
  (-971, 1280), (-387, 512), (-241, 320), (-1921, 2560),
  (-957, 1280), (-1907, 2560), (-95, 128), (-1893, 2560),
  (-943, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_047 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_047_b = true := by
  decide +kernel

/-- Breakpoints of cells 576..587 of piece `zneg` (q = 2). -/
def q2F_zneg_048_b : List QF := [
  (-943, 1280), (-1879, 2560), (-117, 160), (-373, 512),
  (-929, 1280), (-1851, 2560), (-461, 640), (-1837, 2560),
  (-183, 256), (-1823, 2560), (-227, 320), (-1809, 2560),
  (-901, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_048 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_048_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
