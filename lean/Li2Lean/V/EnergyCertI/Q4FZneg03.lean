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

/-- Breakpoints of cells 252..263 of piece `zneg` (q = 4). -/
def q4F_zneg_021_b : List QF := [
  (-3501, 1024), (-1093, 320), (-17471, 5120), (-8727, 2560),
  (-17437, 5120), (-871, 256), (-17403, 5120), (-8693, 2560),
  (-17369, 5120), (-2169, 640), (-3467, 1024), (-8659, 2560),
  (-17301, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_021 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 264..275 of piece `zneg` (q = 4). -/
def q4F_zneg_022_b : List QF := [
  (-17301, 5120), (-4321, 1280), (-17267, 5120), (-1725, 512),
  (-17233, 5120), (-269, 80), (-17199, 5120), (-8591, 2560),
  (-3433, 1024), (-4287, 1280), (-17131, 5120), (-8557, 2560),
  (-17097, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_022 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 276..287 of piece `zneg` (q = 4). -/
def q4F_zneg_023_b : List QF := [
  (-17097, 5120), (-427, 128), (-17063, 5120), (-8523, 2560),
  (-17029, 5120), (-4253, 1280), (-3399, 1024), (-8489, 2560),
  (-16961, 5120), (-1059, 320), (-16927, 5120), (-1691, 512),
  (-16893, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_023 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_023_b = true := by
  decide +kernel

/-- Breakpoints of cells 288..299 of piece `zneg` (q = 4). -/
def q4F_zneg_024_b : List QF := [
  (-16893, 5120), (-4219, 1280), (-16859, 5120), (-8421, 2560),
  (-3365, 1024), (-2101, 640), (-16791, 5120), (-8387, 2560),
  (-16757, 5120), (-837, 256), (-16723, 5120), (-8353, 2560),
  (-16689, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_024 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 300..311 of piece `zneg` (q = 4). -/
def q4F_zneg_025_b : List QF := [
  (-16689, 5120), (-521, 160), (-3331, 1024), (-8319, 2560),
  (-16621, 5120), (-4151, 1280), (-16587, 5120), (-1657, 512),
  (-16553, 5120), (-2067, 640), (-16519, 5120), (-8251, 2560),
  (-3297, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_025 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 312..323 of piece `zneg` (q = 4). -/
def q4F_zneg_026_b : List QF := [
  (-3297, 1024), (-4117, 1280), (-16451, 5120), (-8217, 2560),
  (-16417, 5120), (-205, 64), (-16383, 5120), (-8183, 2560),
  (-16349, 5120), (-4083, 1280), (-3263, 1024), (-8149, 2560),
  (-16281, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_026 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 324..335 of piece `zneg` (q = 4). -/
def q4F_zneg_027_b : List QF := [
  (-16281, 5120), (-2033, 640), (-16247, 5120), (-1623, 512),
  (-16213, 5120), (-4049, 1280), (-16179, 5120), (-8081, 2560),
  (-3229, 1024), (-63, 20), (-16111, 5120), (-8047, 2560),
  (-16077, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_027 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_027_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
