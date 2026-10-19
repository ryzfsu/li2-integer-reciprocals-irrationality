/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
  q = 4 signed-V reference-data contract.

  The values in this file are the exact q=4 table headers from the v13
  reference table (`v-reference-data.tex:154-223`).  The table rows remain a
  separate certificate input: declaring this metadata does not claim that a
  row evaluator has checked any field bound.
-/

namespace Li2Lean.V.Q4ReferenceData

/-! `v-reference-data.tex:1-11`: chain lengths and Poisson rows are read with
the displayed integer scaling and accumulation conventions. -/
structure ChainSpec where
  rowCount : ℕ
  startLength : ℤ
  correctionIndex : ℕ
  correctionNumerator : ℤ

structure PoissonSpec where
  rowCount : ℕ
  prefixTriples : ℕ

def xSpec : ChainSpec :=
  ⟨40, 3349364905389, 1, 94611⟩

def ySpec : ChainSpec :=
  ⟨48, 480367989919, 1, 10081⟩

def zSpec : ChainSpec :=
  ⟨62, -200000000000000, 0, 0⟩

def poissonSpec : PoissonSpec :=
  ⟨141, 71⟩

theorem x_rowCount : xSpec.rowCount = 40 := by rfl
theorem y_rowCount : ySpec.rowCount = 48 := by rfl
theorem z_rowCount : zSpec.rowCount = 62 := by rfl
theorem poisson_rowCount : poissonSpec.rowCount = 141 := by rfl
theorem poisson_prefixTriples : poissonSpec.prefixTriples = 71 := by rfl

theorem q4_reference_row_total :
    xSpec.rowCount + ySpec.rowCount + zSpec.rowCount + poissonSpec.rowCount = 291 := by
  norm_num [xSpec, ySpec, zSpec, poissonSpec]

theorem x_header :
    (xSpec.rowCount, xSpec.startLength, xSpec.correctionIndex,
      xSpec.correctionNumerator) = (40, 3349364905389, 1, 94611) := by
  rfl

theorem y_header :
    (ySpec.rowCount, ySpec.startLength, ySpec.correctionIndex,
      ySpec.correctionNumerator) = (48, 480367989919, 1, 10081) := by
  rfl

theorem z_header :
    (zSpec.rowCount, zSpec.startLength, zSpec.correctionIndex,
      zSpec.correctionNumerator) = (62, -200000000000000, 0, 0) := by
  rfl

/-! Directed q=4 certificate targets from `v-analytic.tex:360-365,375-394`.
They are exact rational encodings of the printed strict/outward bounds. -/
def energyLower : ℚ := -(4776198 / 1000000 : ℚ)
def fieldXUpper : ℚ := -(5408 / 1000 : ℚ)
def fieldVUpper : ℚ := -(4727 / 1000 : ℚ)
def fieldZUpper : ℚ := 779 / 1000
def alphaLower : ℚ := 368211 / 100000
def tauUpper : ℚ := 355230 / 100000
def marginLower : ℚ := 12981 / 100000

theorem alpha_gt_tau : tauUpper < alphaLower := by
  norm_num [tauUpper, alphaLower]

theorem margin_positive : 0 < marginLower := by
  norm_num [marginLower]

/-!
The finite subdivision is a proof obligation, not an axiom: a future row
certificate must provide an accepted directed tree and the evaluator's field
intervals.  The thresholds and row counts are kept in one typed record so a
q=4 assembly cannot silently use another base's table.
-/
structure DirectedCertificate where
  xRows : ℕ
  yRows : ℕ
  zRows : ℕ
  poissonRows : ℕ
  energyLowerBound : ℚ
  fieldXBound : ℚ
  fieldVBound : ℚ
  fieldZBound : ℚ
  alphaBound : ℚ
  tauBound : ℚ
  rows_match : xRows = xSpec.rowCount ∧ yRows = ySpec.rowCount ∧
    zRows = zSpec.rowCount ∧ poissonRows = poissonSpec.rowCount
  bounds_match : energyLowerBound = energyLower ∧
    fieldXBound = fieldXUpper ∧ fieldVBound = fieldVUpper ∧
    fieldZBound = fieldZUpper ∧ alphaBound = alphaLower ∧ tauBound = tauUpper
  alpha_gt_tau_cert : tauBound < alphaBound

theorem directedCertificate_gap (c : DirectedCertificate) :
    0 < c.alphaBound - c.tauBound := by
  linarith [c.alpha_gt_tau_cert]

end Li2Lean.V.Q4ReferenceData
