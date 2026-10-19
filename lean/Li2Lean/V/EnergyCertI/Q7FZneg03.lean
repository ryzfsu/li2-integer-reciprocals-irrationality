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

/-- Breakpoints of cells 234..246 of piece `zneg` (q = 7). -/
def q7F_zneg_018_b : List QF := [
  (-203, 32), (-507, 80), (-1013, 160), (-253, 40),
  (-1011, 160), (-101, 16), (-1009, 160), (-63, 10),
  (-1007, 160), (-503, 80), (-201, 32), (-251, 40),
  (-1003, 160), (-501, 80)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_018 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 247..259 of piece `zneg` (q = 7). -/
def q7F_zneg_019_b : List QF := [
  (-501, 80), (-1001, 160), (-25, 4), (-999, 160),
  (-499, 80), (-997, 160), (-249, 40), (-199, 32),
  (-497, 80), (-993, 160), (-31, 5), (-991, 160),
  (-99, 16), (-989, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_019 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..272 of piece `zneg` (q = 7). -/
def q7F_zneg_020_b : List QF := [
  (-989, 160), (-247, 40), (-987, 160), (-493, 80),
  (-197, 32), (-123, 20), (-983, 160), (-491, 80),
  (-981, 160), (-49, 8), (-979, 160), (-489, 80),
  (-977, 160), (-61, 10)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_020 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_020_b = true := by
  decide +kernel

/-- Breakpoints of cells 273..285 of piece `zneg` (q = 7). -/
def q7F_zneg_021_b : List QF := [
  (-61, 10), (-195, 32), (-487, 80), (-973, 160),
  (-243, 40), (-971, 160), (-97, 16), (-969, 160),
  (-121, 20), (-967, 160), (-483, 80), (-193, 32),
  (-241, 40), (-963, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_021 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 286..298 of piece `zneg` (q = 7). -/
def q7F_zneg_022_b : List QF := [
  (-963, 160), (-481, 80), (-961, 160), (-6, 1),
  (-959, 160), (-479, 80), (-957, 160), (-239, 40),
  (-191, 32), (-477, 80), (-953, 160), (-119, 20),
  (-951, 160), (-95, 16)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_022 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 299..311 of piece `zneg` (q = 7). -/
def q7F_zneg_023_b : List QF := [
  (-95, 16), (-949, 160), (-237, 40), (-947, 160),
  (-473, 80), (-189, 32), (-59, 10), (-943, 160),
  (-471, 80), (-941, 160), (-47, 8), (-939, 160),
  (-469, 80), (-937, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_023 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
