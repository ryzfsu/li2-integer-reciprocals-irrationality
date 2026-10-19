/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.ProducerAssembly
import Li2Lean.AllN.Q11ShiftedDualAeAssembly
import Li2Lean.AllN.Q11PositiveEnergyDomain
import Li2Lean.AllN.Q11QLogLowerAdapter
import Li2Lean.P0.Q11PenaltyRowsProducer

namespace Li2Lean.AllNAssembly

noncomputable section

open MeasureTheory
open Li2Lean.P0
open Li2Lean.P0.Q11Data
open Li2Lean.P0.Q11QLogEnvelopeProducer

/-! The q = 11 endpoint route has four independent analytic inputs.  Keeping
them as fields makes the remaining certificate leaves visible to callers and
prevents the route from silently selecting a conclusion-shaped no-argument
definition in `ProducerAssembly`. -/
structure Q11EndpointProviderInputs where
  dom₀ : p0PositiveEnergyDomain q11AdmissibleMeasures
  cross_energy :
    ∀ M : P0.P0AdmissibleMeasures,
      p0PositiveEnergyDomain M →
      Nonempty (P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures)
  penalty : Q11PenaltyRowsV13Inputs
  qlog : Q11QLogEnvelopeInputs

/-! Assemble the endpoint input from named leaves.  The q-log lower bound is
derived from the envelope using the explicit finite-energy proof carried by
`dom₀`; the penalty rows retain their contour, pinned, and frequency leaves. -/
noncomputable def q11_endpoint_route_input_of_provider
    (P : Q11EndpointProviderInputs) :
    Q11EndpointRouteInput := by
  let R : Q11PenaltyRows :=
    q11_penalty_rows_v13_of_qlog_envelope
      P.penalty.pinned P.penalty.frequency
      P.penalty.contour P.qlog
  have hqlog :=
    q11Admissible_qLog_lower_of_envelope P.qlog P.dom₀.1
  refine
    { a11 := 153 / 200
      a11_eq := rfl
      M₀ := q11AdmissibleMeasures
      dom₀ := P.dom₀
      qLog_lower := hqlog
      caps := ?_ }
  intro M hM
  obtain ⟨hcross⟩ := P.cross_energy M hM
  exact ⟨hcross,
    q11_shifted_caps_of_penalty_rows M hM hcross R⟩

end

end Li2Lean.AllNAssembly
