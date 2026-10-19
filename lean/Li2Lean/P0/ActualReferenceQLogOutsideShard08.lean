import Li2Lean.P0.ActualReferenceQLogOutsideData
namespace Li2Lean.P0.ActualReferenceQLogOutsideCheck
open CA.Contour CA.Contour.QI
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
theorem endpoint_128 : QI.sub_le (primitiveI (edgeQ 128)) (endpointLit.getD 128 ⟨0,0⟩) = true := by
  decide +kernel
end Li2Lean.P0.ActualReferenceQLogOutsideCheck
