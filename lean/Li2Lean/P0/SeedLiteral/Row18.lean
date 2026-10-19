import Li2Lean.P0.SeedLiteral.Factors
namespace Li2Lean.P0.SeedLiteral

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000 in
theorem p0_row18 (j : Fin 64) :
    aMat (18 : Fin 64) j = (lMat * uMat) (18 : Fin 64) j := by
  fin_cases j <;> decide +kernel
end Li2Lean.P0.SeedLiteral
