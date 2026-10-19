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

/-- Breakpoints of cells 84..95 of piece `zneg` (q = 4). -/
def q4F_zneg_007_b : List QF := [
  (-1997, 512), (-39923, 10240), (-19953, 5120), (-39889, 10240),
  (-623, 160), (-7971, 2048), (-19919, 5120), (-39821, 10240),
  (-9951, 2560), (-39787, 10240), (-3977, 1024), (-39753, 10240),
  (-4967, 1280)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_007 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 96..107 of piece `zneg` (q = 4). -/
def q4F_zneg_008_b : List QF := [
  (-4967, 1280), (-39719, 10240), (-19851, 5120), (-7937, 2048),
  (-9917, 2560), (-39651, 10240), (-19817, 5120), (-39617, 10240),
  (-495, 128), (-39583, 10240), (-19783, 5120), (-39549, 10240),
  (-9883, 2560)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_008 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 108..119 of piece `zneg` (q = 4). -/
def q4F_zneg_009_b : List QF := [
  (-9883, 2560), (-7903, 2048), (-19749, 5120), (-39481, 10240),
  (-4933, 1280), (-39447, 10240), (-3943, 1024), (-39413, 10240),
  (-9849, 2560), (-39379, 10240), (-19681, 5120), (-7869, 2048),
  (-1229, 320)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_009 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 120..131 of piece `zneg` (q = 4). -/
def q4F_zneg_010_b : List QF := [
  (-1229, 320), (-39311, 10240), (-19647, 5120), (-1963, 512),
  (-19613, 5120), (-4899, 1280), (-19579, 5120), (-39141, 10240),
  (-9781, 2560), (-39107, 10240), (-3909, 1024), (-39073, 10240),
  (-2441, 640)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_010 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 132..143 of piece `zneg` (q = 4). -/
def q4F_zneg_011_b : List QF := [
  (-2441, 640), (-39039, 10240), (-19511, 5120), (-9747, 2560),
  (-19477, 5120), (-973, 256), (-19443, 5120), (-9713, 2560),
  (-19409, 5120), (-303, 80), (-3875, 1024), (-9679, 2560),
  (-19341, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_011 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_011_b = true := by
  decide +kernel

/-- Breakpoints of cells 144..155 of piece `zneg` (q = 4). -/
def q4F_zneg_012_b : List QF := [
  (-19341, 5120), (-4831, 1280), (-19307, 5120), (-1929, 512),
  (-19273, 5120), (-2407, 640), (-19239, 5120), (-9611, 2560),
  (-3841, 1024), (-4797, 1280), (-19171, 5120), (-9577, 2560),
  (-19137, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_012 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_012_b = true := by
  decide +kernel

/-- Breakpoints of cells 156..167 of piece `zneg` (q = 4). -/
def q4F_zneg_013_b : List QF := [
  (-19137, 5120), (-239, 64), (-19103, 5120), (-9543, 2560),
  (-19069, 5120), (-4763, 1280), (-3807, 1024), (-9509, 2560),
  (-19001, 5120), (-2373, 640), (-18967, 5120), (-1895, 512),
  (-18933, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_013 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_013_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
