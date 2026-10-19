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

/-- Breakpoints of cells 78..90 of piece `zneg` (q = 7). -/
def q7F_zneg_006_b : List QF := [
  (-1101, 160), (-2201, 320), (-55, 8), (-2199, 320),
  (-1099, 160), (-2197, 320), (-549, 80), (-439, 64),
  (-1097, 160), (-2193, 320), (-137, 20), (-2191, 320),
  (-219, 32), (-2189, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_006 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_006_b = true := by
  decide +kernel

/-- Breakpoints of cells 91..103 of piece `zneg` (q = 7). -/
def q7F_zneg_007_b : List QF := [
  (-2189, 320), (-547, 80), (-2187, 320), (-1093, 160),
  (-437, 64), (-273, 40), (-2183, 320), (-1091, 160),
  (-2181, 320), (-109, 16), (-2179, 320), (-1089, 160),
  (-2177, 320), (-34, 5)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_007 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 104..116 of piece `zneg` (q = 7). -/
def q7F_zneg_008_b : List QF := [
  (-34, 5), (-435, 64), (-1087, 160), (-2173, 320),
  (-543, 80), (-2171, 320), (-217, 32), (-2169, 320),
  (-271, 40), (-2167, 320), (-1083, 160), (-433, 64),
  (-541, 80), (-2163, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_008 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 117..129 of piece `zneg` (q = 7). -/
def q7F_zneg_009_b : List QF := [
  (-2163, 320), (-1081, 160), (-2161, 320), (-27, 4),
  (-2159, 320), (-1079, 160), (-2157, 320), (-539, 80),
  (-431, 64), (-1077, 160), (-2153, 320), (-269, 40),
  (-2151, 320), (-215, 32)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_009 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..142 of piece `zneg` (q = 7). -/
def q7F_zneg_010_b : List QF := [
  (-215, 32), (-2149, 320), (-537, 80), (-2147, 320),
  (-1073, 160), (-429, 64), (-67, 10), (-2143, 320),
  (-1071, 160), (-2141, 320), (-107, 16), (-2139, 320),
  (-1069, 160), (-2137, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_010 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 143..155 of piece `zneg` (q = 7). -/
def q7F_zneg_011_b : List QF := [
  (-2137, 320), (-267, 40), (-427, 64), (-1067, 160),
  (-2133, 320), (-533, 80), (-2131, 320), (-213, 32),
  (-2129, 320), (-133, 20), (-2127, 320), (-1063, 160),
  (-425, 64), (-531, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_011 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_011_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
