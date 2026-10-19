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

/-- Breakpoints of cells 924..935 of piece `zneg` (q = 4). -/
def q4F_zneg_077_b : List QF := [
  (-6081, 5120), (-379, 320), (-6047, 5120), (-603, 512),
  (-6013, 5120), (-1499, 1280), (-5979, 5120), (-2981, 2560),
  (-1189, 1024), (-741, 640), (-5911, 5120), (-2947, 2560),
  (-5877, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_077 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_077_b = true := by
  decide +kernel

/-- Breakpoints of cells 936..947 of piece `zneg` (q = 4). -/
def q4F_zneg_078_b : List QF := [
  (-5877, 5120), (-293, 256), (-5843, 5120), (-2913, 2560),
  (-5809, 5120), (-181, 160), (-1155, 1024), (-2879, 2560),
  (-5741, 5120), (-1431, 1280), (-5707, 5120), (-569, 512),
  (-5673, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_078 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_078_b = true := by
  decide +kernel

/-- Breakpoints of cells 948..959 of piece `zneg` (q = 4). -/
def q4F_zneg_079_b : List QF := [
  (-5673, 5120), (-707, 640), (-5639, 5120), (-2811, 2560),
  (-1121, 1024), (-1397, 1280), (-5571, 5120), (-2777, 2560),
  (-5537, 5120), (-69, 64), (-5503, 5120), (-2743, 2560),
  (-5469, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_079 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_079_b = true := by
  decide +kernel

/-- Breakpoints of cells 960..971 of piece `zneg` (q = 4). -/
def q4F_zneg_080_b : List QF := [
  (-5469, 5120), (-1363, 1280), (-1087, 1024), (-2709, 2560),
  (-5401, 5120), (-673, 640), (-5367, 5120), (-535, 512),
  (-5333, 5120), (-1329, 1280), (-5299, 5120), (-2641, 2560),
  (-1053, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_080 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_080_b = true := by
  decide +kernel

/-- Breakpoints of cells 972..983 of piece `zneg` (q = 4). -/
def q4F_zneg_081_b : List QF := [
  (-1053, 1024), (-41, 40), (-5231, 5120), (-2607, 2560),
  (-5197, 5120), (-259, 256), (-5163, 5120), (-2573, 2560),
  (-5129, 5120), (-639, 640), (-1019, 1024), (-2539, 2560),
  (-5061, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_081 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_081_b = true := by
  decide +kernel

/-- Breakpoints of cells 984..995 of piece `zneg` (q = 4). -/
def q4F_zneg_082_b : List QF := [
  (-5061, 5120), (-1261, 1280), (-5027, 5120), (-501, 512),
  (-4993, 5120), (-311, 320), (-4959, 5120), (-2471, 2560),
  (-985, 1024), (-1227, 1280), (-4891, 5120), (-2437, 2560),
  (-4857, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_082 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_082_b = true := by
  decide +kernel

/-- Breakpoints of cells 996..1007 of piece `zneg` (q = 4). -/
def q4F_zneg_083_b : List QF := [
  (-4857, 5120), (-121, 128), (-4823, 5120), (-2403, 2560),
  (-4789, 5120), (-1193, 1280), (-951, 1024), (-2369, 2560),
  (-4721, 5120), (-147, 160), (-4687, 5120), (-467, 512),
  (-4653, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_083 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_083_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
