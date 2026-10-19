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

/-- Breakpoints of cells 252..263 of piece `zneg` (q = 2). -/
def q2F_zneg_021_b : List QF := [
  (-2077, 1280), (-4147, 2560), (-207, 128), (-4133, 2560),
  (-2063, 1280), (-4119, 2560), (-257, 160), (-821, 512),
  (-2049, 1280), (-4091, 2560), (-1021, 640), (-4077, 2560),
  (-407, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_021 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 264..275 of piece `zneg` (q = 2). -/
def q2F_zneg_022_b : List QF := [
  (-407, 256), (-4063, 2560), (-507, 320), (-4049, 2560),
  (-2021, 1280), (-807, 512), (-1007, 640), (-4021, 2560),
  (-2007, 1280), (-4007, 2560), (-25, 16), (-3993, 2560),
  (-1993, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_022 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 276..287 of piece `zneg` (q = 2). -/
def q2F_zneg_023_b : List QF := [
  (-1993, 1280), (-3979, 2560), (-993, 640), (-793, 512),
  (-1979, 1280), (-3951, 2560), (-493, 320), (-3937, 2560),
  (-393, 256), (-3923, 2560), (-979, 640), (-3909, 2560),
  (-1951, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_023 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 288..299 of piece `zneg` (q = 2). -/
def q2F_zneg_024_b : List QF := [
  (-1951, 1280), (-779, 512), (-243, 160), (-3881, 2560),
  (-1937, 1280), (-3867, 2560), (-193, 128), (-3853, 2560),
  (-1923, 1280), (-3839, 2560), (-479, 320), (-765, 512),
  (-1909, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_024 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 300..311 of piece `zneg` (q = 2). -/
def q2F_zneg_025_b : List QF := [
  (-1909, 1280), (-3811, 2560), (-951, 640), (-3797, 2560),
  (-379, 256), (-3783, 2560), (-59, 40), (-3769, 2560),
  (-1881, 1280), (-751, 512), (-937, 640), (-3741, 2560),
  (-1867, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_025 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 312..323 of piece `zneg` (q = 2). -/
def q2F_zneg_026_b : List QF := [
  (-1867, 1280), (-3727, 2560), (-93, 64), (-3713, 2560),
  (-1853, 1280), (-3699, 2560), (-923, 640), (-737, 512),
  (-1839, 1280), (-3671, 2560), (-229, 160), (-3657, 2560),
  (-365, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_026 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 324..335 of piece `zneg` (q = 2). -/
def q2F_zneg_027_b : List QF := [
  (-365, 256), (-3643, 2560), (-909, 640), (-3629, 2560),
  (-1811, 1280), (-723, 512), (-451, 320), (-3601, 2560),
  (-1797, 1280), (-3587, 2560), (-179, 128), (-3573, 2560),
  (-1783, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_027 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
