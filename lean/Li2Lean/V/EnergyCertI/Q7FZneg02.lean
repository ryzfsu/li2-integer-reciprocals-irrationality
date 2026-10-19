/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 156..168 of piece `zneg` (q = 7). -/
def q7F_zneg_012_b : List QF := [
  (-531, 80), (-2123, 320), (-1061, 160), (-2121, 320),
  (-53, 8), (-2119, 320), (-1059, 160), (-2117, 320),
  (-529, 80), (-423, 64), (-1057, 160), (-2113, 320),
  (-33, 5), (-2111, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_012 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 169..181 of piece `zneg` (q = 7). -/
def q7F_zneg_013_b : List QF := [
  (-2111, 320), (-211, 32), (-2109, 320), (-527, 80),
  (-2107, 320), (-1053, 160), (-421, 64), (-263, 40),
  (-2103, 320), (-1051, 160), (-2101, 320), (-105, 16),
  (-2099, 320), (-1049, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_013 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_013_b = true := by
  decide +kernel

/-- Breakpoints of cells 182..194 of piece `zneg` (q = 7). -/
def q7F_zneg_014_b : List QF := [
  (-1049, 160), (-2097, 320), (-131, 20), (-419, 64),
  (-1047, 160), (-2093, 320), (-523, 80), (-2091, 320),
  (-209, 32), (-2089, 320), (-261, 40), (-2087, 320),
  (-1043, 160), (-417, 64)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_014 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 195..207 of piece `zneg` (q = 7). -/
def q7F_zneg_015_b : List QF := [
  (-417, 64), (-521, 80), (-2083, 320), (-1041, 160),
  (-2081, 320), (-13, 2), (-2079, 320), (-1039, 160),
  (-2077, 320), (-519, 80), (-1037, 160), (-259, 40),
  (-207, 32), (-517, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_015 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 208..220 of piece `zneg` (q = 7). -/
def q7F_zneg_016_b : List QF := [
  (-517, 80), (-2067, 320), (-1033, 160), (-413, 64),
  (-129, 20), (-2063, 320), (-1031, 160), (-2061, 320),
  (-103, 16), (-2059, 320), (-1029, 160), (-2057, 320),
  (-257, 40), (-411, 64)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_016 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 221..233 of piece `zneg` (q = 7). -/
def q7F_zneg_017_b : List QF := [
  (-411, 64), (-1027, 160), (-513, 80), (-205, 32),
  (-32, 5), (-1023, 160), (-511, 80), (-1021, 160),
  (-51, 8), (-1019, 160), (-509, 80), (-1017, 160),
  (-127, 20), (-203, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_017 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_017_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
