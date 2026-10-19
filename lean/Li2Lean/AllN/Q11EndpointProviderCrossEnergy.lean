/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.Q11EndpointRouteInputProvider
import Li2Lean.P0.Q11CrossEnergyCaps

/-!
The q = 11 endpoint provider with its cross-energy field filled from the
support-local v13 cross-energy construction.  The finite-energy hypotheses
come from the positive-energy domains; no conclusion-shaped premise is added
to the provider.
-/

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Q11Data
open Li2Lean.P0.Q11QLogEnvelopeProducer

theorem q11_cross_energy_input_of_dom
    (dom0 : p0PositiveEnergyDomain q11AdmissibleMeasures)
    (M : P0AdmissibleMeasures)
    (hM : p0PositiveEnergyDomain M) :
    Nonempty (P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures) := by
  exact ⟨q11_L6CrossEnergy_v13 M hM.1 dom0.1⟩

noncomputable def q11_endpoint_provider_inputs_with_cross
    (dom0 : p0PositiveEnergyDomain q11AdmissibleMeasures)
    (penalty : Q11PenaltyRowsV13Inputs)
    (qlog : Q11QLogEnvelopeInputs) :
    Q11EndpointProviderInputs :=
  { dom₀ := dom0
    cross_energy := fun M hM => q11_cross_energy_input_of_dom dom0 M hM
    penalty := penalty
    qlog := qlog }

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.q11_cross_energy_input_of_dom
#print axioms Li2Lean.AllNAssembly.q11_endpoint_provider_inputs_with_cross
