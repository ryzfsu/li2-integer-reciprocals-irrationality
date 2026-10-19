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

/-- Breakpoints of cells 168..179 of piece `zneg` (q = 4). -/
def q4F_zneg_014_b : List QF := [
  (-18933, 5120), (-4729, 1280), (-18899, 5120), (-9441, 2560),
  (-3773, 1024), (-589, 160), (-18831, 5120), (-9407, 2560),
  (-18797, 5120), (-939, 256), (-18763, 5120), (-9373, 2560),
  (-18729, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_014 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..191 of piece `zneg` (q = 4). -/
def q4F_zneg_015_b : List QF := [
  (-18729, 5120), (-2339, 640), (-3739, 1024), (-9339, 2560),
  (-18661, 5120), (-4661, 1280), (-18627, 5120), (-1861, 512),
  (-18593, 5120), (-1161, 320), (-18559, 5120), (-9271, 2560),
  (-3705, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_015 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 192..203 of piece `zneg` (q = 4). -/
def q4F_zneg_016_b : List QF := [
  (-3705, 1024), (-4627, 1280), (-18491, 5120), (-9237, 2560),
  (-18457, 5120), (-461, 128), (-18423, 5120), (-9203, 2560),
  (-18389, 5120), (-4593, 1280), (-3671, 1024), (-9169, 2560),
  (-18321, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_016 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 204..215 of piece `zneg` (q = 4). -/
def q4F_zneg_017_b : List QF := [
  (-18321, 5120), (-143, 40), (-18287, 5120), (-1827, 512),
  (-18253, 5120), (-4559, 1280), (-18219, 5120), (-9101, 2560),
  (-3637, 1024), (-2271, 640), (-18151, 5120), (-9067, 2560),
  (-18117, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_017 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 216..227 of piece `zneg` (q = 4). -/
def q4F_zneg_018_b : List QF := [
  (-18117, 5120), (-905, 256), (-18083, 5120), (-9033, 2560),
  (-18049, 5120), (-1127, 320), (-3603, 1024), (-8999, 2560),
  (-17981, 5120), (-4491, 1280), (-17947, 5120), (-1793, 512),
  (-17913, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_018 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 228..239 of piece `zneg` (q = 4). -/
def q4F_zneg_019_b : List QF := [
  (-17913, 5120), (-2237, 640), (-17879, 5120), (-8931, 2560),
  (-3569, 1024), (-4457, 1280), (-17811, 5120), (-8897, 2560),
  (-17777, 5120), (-111, 32), (-17743, 5120), (-8863, 2560),
  (-17709, 5120)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_019 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..251 of piece `zneg` (q = 4). -/
def q4F_zneg_020_b : List QF := [
  (-17709, 5120), (-4423, 1280), (-3535, 1024), (-8829, 2560),
  (-17641, 5120), (-2203, 640), (-17607, 5120), (-1759, 512),
  (-17573, 5120), (-4389, 1280), (-17539, 5120), (-8761, 2560),
  (-3501, 1024)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_020 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
