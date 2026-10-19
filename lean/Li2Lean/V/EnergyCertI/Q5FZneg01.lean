/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 78..90 of piece `zneg` (q = 5). -/
def q5F_zneg_006_b : List QF := [
  (-6279, 1280), (-5021, 1024), (-12547, 2560), (-25083, 5120),
  (-1567, 320), (-25061, 5120), (-2505, 512), (-25039, 5120),
  (-6257, 1280), (-25017, 5120), (-12503, 2560), (-4999, 1024),
  (-3123, 640), (-24973, 5120)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_006 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_006_b = true := by
  decide +kernel

/-- Breakpoints of cells 91..103 of piece `zneg` (q = 5). -/
def q5F_zneg_007_b : List QF := [
  (-24973, 5120), (-12481, 2560), (-24951, 5120), (-1247, 256),
  (-24929, 5120), (-12459, 2560), (-24907, 5120), (-389, 80),
  (-4977, 1024), (-12437, 2560), (-24863, 5120), (-6213, 1280),
  (-24841, 5120), (-2483, 512)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_007 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_007_b = true := by
  decide +kernel

/-- Breakpoints of cells 104..116 of piece `zneg` (q = 5). -/
def q5F_zneg_008_b : List QF := [
  (-2483, 512), (-24819, 5120), (-3101, 640), (-24797, 5120),
  (-12393, 2560), (-4955, 1024), (-6191, 1280), (-24753, 5120),
  (-12371, 2560), (-24731, 5120), (-309, 64), (-24709, 5120),
  (-12349, 2560), (-24687, 5120)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_008 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_008_b = true := by
  decide +kernel

/-- Breakpoints of cells 117..129 of piece `zneg` (q = 5). -/
def q5F_zneg_009_b : List QF := [
  (-24687, 5120), (-6169, 1280), (-4933, 1024), (-12327, 2560),
  (-24643, 5120), (-3079, 640), (-24621, 5120), (-2461, 512),
  (-24599, 5120), (-6147, 1280), (-24577, 5120), (-12283, 2560),
  (-4911, 1024), (-767, 160)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_009 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_009_b = true := by
  decide +kernel

/-- Breakpoints of cells 130..142 of piece `zneg` (q = 5). -/
def q5F_zneg_010_b : List QF := [
  (-767, 160), (-24533, 5120), (-12261, 2560), (-24511, 5120),
  (-1225, 256), (-24489, 5120), (-12239, 2560), (-24467, 5120),
  (-3057, 640), (-4889, 1024), (-12217, 2560), (-24423, 5120),
  (-6103, 1280), (-24401, 5120)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_010 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_010_b = true := by
  decide +kernel

/-- Breakpoints of cells 143..155 of piece `zneg` (q = 5). -/
def q5F_zneg_011_b : List QF := [
  (-24401, 5120), (-2439, 512), (-24379, 5120), (-1523, 320),
  (-24357, 5120), (-12173, 2560), (-4867, 1024), (-6081, 1280),
  (-24313, 5120), (-12151, 2560), (-24291, 5120), (-607, 128),
  (-24269, 5120), (-12129, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_011 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_011_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
