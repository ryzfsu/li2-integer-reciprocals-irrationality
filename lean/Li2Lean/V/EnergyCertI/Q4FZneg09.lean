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

/-- Breakpoints of cells 756..767 of piece `zneg` (q = 4). -/
def q4F_zneg_063_b : List QF := [
  (-8937, 5120), (-223, 128), (-8903, 5120), (-4443, 2560),
  (-8869, 5120), (-2213, 1280), (-1767, 1024), (-4409, 2560),
  (-8801, 5120), (-549, 320), (-8767, 5120), (-875, 512),
  (-8733, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_063 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_063_b = true := by
  decide +kernel

/-- Breakpoints of cells 768..779 of piece `zneg` (q = 4). -/
def q4F_zneg_064_b : List QF := [
  (-8733, 5120), (-2179, 1280), (-8699, 5120), (-4341, 2560),
  (-1733, 1024), (-1081, 640), (-8631, 5120), (-4307, 2560),
  (-8597, 5120), (-429, 256), (-8563, 5120), (-4273, 2560),
  (-8529, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_064 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_064_b = true := by
  decide +kernel

/-- Breakpoints of cells 780..791 of piece `zneg` (q = 4). -/
def q4F_zneg_065_b : List QF := [
  (-8529, 5120), (-133, 80), (-1699, 1024), (-4239, 2560),
  (-8461, 5120), (-2111, 1280), (-8427, 5120), (-841, 512),
  (-8393, 5120), (-1047, 640), (-8359, 5120), (-4171, 2560),
  (-1665, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_065 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_065_b = true := by
  decide +kernel

/-- Breakpoints of cells 792..803 of piece `zneg` (q = 4). -/
def q4F_zneg_066_b : List QF := [
  (-1665, 1024), (-2077, 1280), (-8291, 5120), (-4137, 2560),
  (-8257, 5120), (-103, 64), (-8223, 5120), (-4103, 2560),
  (-8189, 5120), (-2043, 1280), (-1631, 1024), (-4069, 2560),
  (-8121, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_066 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_066_b = true := by
  decide +kernel

/-- Breakpoints of cells 804..815 of piece `zneg` (q = 4). -/
def q4F_zneg_067_b : List QF := [
  (-8121, 5120), (-1013, 640), (-8087, 5120), (-807, 512),
  (-8053, 5120), (-2009, 1280), (-8019, 5120), (-4001, 2560),
  (-1597, 1024), (-249, 160), (-7951, 5120), (-3967, 2560),
  (-7917, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_067 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_067_b = true := by
  decide +kernel

/-- Breakpoints of cells 816..827 of piece `zneg` (q = 4). -/
def q4F_zneg_068_b : List QF := [
  (-7917, 5120), (-395, 256), (-7883, 5120), (-3933, 2560),
  (-7849, 5120), (-979, 640), (-1563, 1024), (-3899, 2560),
  (-7781, 5120), (-1941, 1280), (-7747, 5120), (-773, 512),
  (-7713, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_068 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_068_b = true := by
  decide +kernel

/-- Breakpoints of cells 828..839 of piece `zneg` (q = 4). -/
def q4F_zneg_069_b : List QF := [
  (-7713, 5120), (-481, 320), (-7679, 5120), (-3831, 2560),
  (-1529, 1024), (-1907, 1280), (-7611, 5120), (-3797, 2560),
  (-7577, 5120), (-189, 128), (-7543, 5120), (-3763, 2560),
  (-7509, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_069 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_069_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
