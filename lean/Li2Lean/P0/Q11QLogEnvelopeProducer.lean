/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.Q11QLogEnvelope
import Li2Lean.P0.Q11PenaltyRows
import Li2Lean.P0.Q11CrossEnergy
import Li2Lean.P0.Q11ContourSelfIntegrability

/-!
The q = 11 Q_log producer interface. It reduces the literal reference bound
to seven component lower enclosures, finite-energy integrability, and an
integer-ratio budget check. It does not assert the component enclosures; those
remain the analytic/numerical certificate leaves.
-/

namespace Li2Lean.P0.Q11QLogEnvelopeProducer

open MeasureTheory
open Li2Lean.P0.Q11Data

noncomputable section

theorem ratioLtBool_sound {x y : IntRatio}
    (hx : 0 < x.den) (hy : 0 < y.den)
    (h : ratioLtBool x y = true) :
    ratioToReal x < ratioToReal y := by
  have hcross : x.num * (y.den : ℤ) < y.num * (x.den : ℤ) := by
    simpa [ratioLtBool] using (of_decide_eq_true h)
  have hxd : (x.den : ℝ) > 0 := by exact_mod_cast hx
  have hyd : (y.den : ℝ) > 0 := by exact_mod_cast hy
  unfold ratioToReal
  apply (div_lt_div_iff₀ hxd hyd).2
  exact_mod_cast hcross

/-- Componentwise integer-ratio bounds for the seven actual q = 11 energy
integrals. `totalLower` is a common outward lower bound for their sum, and the
last field is a Boolean cross-multiplication check against the printed qLog
threshold. The two pinned-contour integrability fields are derived from the
proved q11 cross-energy theorem rather than supplied independently. -/
structure Q11QLogEnvelopeInputs where
  pinnedSelfIntegrable :
    Integrable (fun x : ℝ => q11PinnedComplexPotential (x : ℂ))
      q11PinnedReferenceMeasure
  pinnedFrequencyIntegrable :
    Integrable (fun x : ℝ => q11ReflectedFrequencyPotential (x : ℂ))
      q11PinnedReferenceMeasure
  contourFrequencyIntegrable :
    Integrable q11ReflectedFrequencyPotential q11ContourReferenceMeasure
  lowerPinnedPinned : IntRatio
  lowerPinnedContour : IntRatio
  lowerContourPinned : IntRatio
  lowerContourContour : IntRatio
  lowerPinnedFrequency : IntRatio
  lowerContourFrequency : IntRatio
  lowerFrequencyFrequency : IntRatio
  totalLower : IntRatio
  pinnedPinned_den_pos : 0 < lowerPinnedPinned.den
  pinnedContour_den_pos : 0 < lowerPinnedContour.den
  contourPinned_den_pos : 0 < lowerContourPinned.den
  contourContour_den_pos : 0 < lowerContourContour.den
  pinnedFrequency_den_pos : 0 < lowerPinnedFrequency.den
  contourFrequency_den_pos : 0 < lowerContourFrequency.den
  frequencyFrequency_den_pos : 0 < lowerFrequencyFrequency.den
  total_den_pos : 0 < totalLower.den
  pinnedPinned_le : ratioToReal lowerPinnedPinned ≤ q11Eκκ
  pinnedContour_le : ratioToReal lowerPinnedContour ≤ q11Eκν
  contourPinned_le : ratioToReal lowerContourPinned ≤ q11Eνκ
  contourContour_le : ratioToReal lowerContourContour ≤ q11Eνν
  pinnedFrequency_le : ratioToReal lowerPinnedFrequency ≤ q11Eκμ
  contourFrequency_le : ratioToReal lowerContourFrequency ≤ q11Eνμ
  frequencyFrequency_le : ratioToReal lowerFrequencyFrequency ≤ q11Eμμ
  total_le_terms : ratioToReal totalLower ≤
    ratioToReal lowerPinnedPinned + ratioToReal lowerPinnedContour +
      ratioToReal lowerContourPinned + ratioToReal lowerContourContour +
      ratioToReal lowerFrequencyFrequency + ratioToReal lowerPinnedFrequency +
      ratioToReal lowerContourFrequency
  margin_check : ratioLtBool qLogLower totalLower = true

theorem q11FiniteEnergyData_of_envelope_inputs
    (C : Q11QLogEnvelopeInputs) : Q11FiniteEnergyData := by
  exact {
    κκ := C.pinnedSelfIntegrable
    κν := q11ContourPotential_pinned_integrable
    νκ := q11PinnedComplexPotential_contour_integrable
    νν := q11ContourPotential_contour_integrable
    κμ := C.pinnedFrequencyIntegrable
    νμ := C.contourFrequencyIntegrable
  }

/-- The q = 11 actual reference logarithmic energy clears its printed lower
bound once the seven component enclosures and their integer budget are supplied. -/
theorem q11ActualReference_qLog_lower_of_envelope
    (C : Q11QLogEnvelopeInputs) : q11QLogLower := by
  change ratioToReal qLogLower < q11ActualReference.qLog
  have htotal : ratioToReal qLogLower < ratioToReal C.totalLower :=
    ratioLtBool_sound qLog_lower_den_pos C.total_den_pos C.margin_check
  have hbudget : ratioToReal qLogLower <
      ratioToReal C.lowerPinnedPinned + ratioToReal C.lowerPinnedContour +
        ratioToReal C.lowerContourPinned + ratioToReal C.lowerContourContour +
        ratioToReal C.lowerFrequencyFrequency + ratioToReal C.lowerPinnedFrequency +
        ratioToReal C.lowerContourFrequency :=
    lt_of_lt_of_le htotal C.total_le_terms
  exact q11_qLog_lower_of_seven (q11FiniteEnergyData_of_envelope_inputs C)
    C.pinnedPinned_le C.pinnedContour_le C.contourPinned_le
    C.contourContour_le C.pinnedFrequency_le C.contourFrequency_le
    C.frequencyFrequency_le hbudget

end

end Li2Lean.P0.Q11QLogEnvelopeProducer
