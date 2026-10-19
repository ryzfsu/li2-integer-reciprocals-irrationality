/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.ProducerAssembly
import Li2Lean.AllN.Q11EndpointRouteInputProvider
import Li2Lean.AllN.Q11EndpointProviderCrossEnergy
import Li2Lean.AllN.Q11QLogRemainingBounds
import Li2Lean.AllN.R3Q11PinnedPacket
import Li2Lean.P0.Q11CA.Contour.Q11All
import Li2Lean.P0.Q11FrequencyPenaltyActual

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Q11Data

theorem q11_endpoint_route_input_of_leaves : Nonempty Q11EndpointRouteInput := by
  let penalty : Q11PenaltyRowsV13Inputs :=
    { pinned := r3_q11_pinned_penalty_rows
      frequency := q11FrequencyPenaltyRowsV13_actual
      contour := q11AllCertificate
      qLog_lower :=
        q11ActualReference_qLog_lower_proved }
  exact ⟨q11_endpoint_route_input_of_provider
    (q11_endpoint_provider_inputs_with_cross
      q11PositiveEnergyDomain penalty q11_qlog_envelope_inputs_actual)⟩

theorem p0PositiveEnergyProfileActual_endpoint_eleven :
    (77597 / 100000 : ℝ) ≤
      p0PositiveEnergyProfileActual (Real.log ((11 : ℝ) / 2)) := by
  exact q11_endpoint_of_input (Classical.choice q11_endpoint_route_input_of_leaves)

/-- Concrete AllN input. Its data is the positive-base P0 energy profile;
the four proved facts are named Prop theorems above, with no sorry-valued data. -/
noncomputable def p0Profile_producer : P0PositiveEnergyProfile where
  alpha := p0PositiveEnergyProfileActual
  concave := p0PositiveEnergyProfileActual_concave
  endpoint_two := p0PositiveEnergyProfileActual_endpoint_two
  endpoint_eleven := p0PositiveEnergyProfileActual_endpoint_eleven
  smoothing := fun q hq h3 => p0PositiveEnergyProfileActual_smoothing q hq h3

end

end Li2Lean.AllNAssembly
