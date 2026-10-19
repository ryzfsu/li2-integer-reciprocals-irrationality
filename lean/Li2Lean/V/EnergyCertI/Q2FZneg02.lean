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

/-- Breakpoints of cells 168..179 of piece `zneg` (q = 2). -/
def q2F_zneg_014_b : List QF := [
  (-1161, 640), (-9281, 5120), (-4637, 2560), (-9267, 5120),
  (-463, 256), (-9253, 5120), (-4623, 2560), (-9239, 5120),
  (-577, 320), (-1845, 1024), (-4609, 2560), (-9211, 5120),
  (-2301, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_014 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_014_b = true := by
  decide +kernel

/-- Breakpoints of cells 180..191 of piece `zneg` (q = 2). -/
def q2F_zneg_015_b : List QF := [
  (-2301, 1280), (-9197, 5120), (-919, 512), (-9183, 5120),
  (-1147, 640), (-9169, 5120), (-4581, 2560), (-1831, 1024),
  (-2287, 1280), (-9141, 5120), (-4567, 2560), (-9127, 5120),
  (-57, 32)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_015 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_015_b = true := by
  decide +kernel

/-- Breakpoints of cells 192..203 of piece `zneg` (q = 2). -/
def q2F_zneg_016_b : List QF := [
  (-57, 32), (-9113, 5120), (-4553, 2560), (-9099, 5120),
  (-2273, 1280), (-4539, 2560), (-1133, 640), (-905, 512),
  (-2259, 1280), (-4511, 2560), (-563, 320), (-4497, 2560),
  (-449, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_016 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_016_b = true := by
  decide +kernel

/-- Breakpoints of cells 204..215 of piece `zneg` (q = 2). -/
def q2F_zneg_017_b : List QF := [
  (-449, 256), (-4483, 2560), (-1119, 640), (-4469, 2560),
  (-2231, 1280), (-891, 512), (-139, 80), (-4441, 2560),
  (-2217, 1280), (-4427, 2560), (-221, 128), (-4413, 2560),
  (-2203, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_017 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_017_b = true := by
  decide +kernel

/-- Breakpoints of cells 216..227 of piece `zneg` (q = 2). -/
def q2F_zneg_018_b : List QF := [
  (-2203, 1280), (-4399, 2560), (-549, 320), (-877, 512),
  (-2189, 1280), (-4371, 2560), (-1091, 640), (-4357, 2560),
  (-435, 256), (-4343, 2560), (-271, 160), (-4329, 2560),
  (-2161, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_018 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 228..239 of piece `zneg` (q = 2). -/
def q2F_zneg_019_b : List QF := [
  (-2161, 1280), (-863, 512), (-1077, 640), (-4301, 2560),
  (-2147, 1280), (-4287, 2560), (-107, 64), (-4273, 2560),
  (-2133, 1280), (-4259, 2560), (-1063, 640), (-849, 512),
  (-2119, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_019 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 240..251 of piece `zneg` (q = 2). -/
def q2F_zneg_020_b : List QF := [
  (-2119, 1280), (-4231, 2560), (-33, 20), (-4217, 2560),
  (-421, 256), (-4203, 2560), (-1049, 640), (-4189, 2560),
  (-2091, 1280), (-835, 512), (-521, 320), (-4161, 2560),
  (-2077, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_020 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_020_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
