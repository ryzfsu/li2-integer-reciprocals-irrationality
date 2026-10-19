/- 
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

/-
Adapters from the actual signed-V producer objects to the top-down B3
interfaces.  The constructions remain the v13 determinant
G_m(X;-q)=V.vPolynomial (m/4) (-q), with m=4n.  This file only transports
already stated producer certificates; it does not manufacture an energy,
integerizer, or Frobenius certificate.

v13 sources:
* v-arithmetic.tex:13-35, 353-421 (family, degree, integerization);
* nonvanishing.tex:200-275 (scaled Frobenius and eventual nonvanishing).
-/

import Mathlib
import Li2Lean.B3.ProducerInterfaces
import Li2Lean.V.NonvanishingPlan

namespace Li2Lean.B3

noncomputable section

/-- Map the actual integerizer certificate's rational clearing identity into
the real-valued B3 interface.  The determinant remains the fixed v13
V.vPolynomial, and the denominator rate is unchanged
(v-arithmetic.tex:353-421). -/
theorem actualIntegerizer_toVIntegerizerBound
    {q : ℕ} {tau : ℝ}
    (c : V.VActualIntegerizerCertificate q tau) :
    VIntegerizerBound q tau := by
  refine ⟨fun m => (c.D m : ℚ), ?_, ?_, ?_⟩
  · intro n hn
    change (0 : ℚ) < (c.D (4 * n) : ℚ)
    exact_mod_cast c.D_pos n hn
  · intro n hn
    obtain ⟨P, hP⟩ := c.clears n hn
    refine ⟨P, ?_⟩
    have hP' := congrArg
      (fun R : Polynomial ℚ => R.map (algebraMap ℚ ℝ)) hP
    have hcomp :
        (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
          Int.castRingHom ℝ := by
      ext z
      norm_num
    rw [vRealPoly_four_mul]
    simpa [hcomp, Polynomial.map_map] using hP'
  · intro epsilon hepsilon
    obtain ⟨N, hN⟩ := c.pnt_rate epsilon hepsilon
    refine ⟨N, ?_⟩
    intro n hn hnpos
    simpa using hN n hn hnpos

/-- A concrete integerizer certificate supplies the arithmetic plan once the
actual degree producer is supplied.  The remaining input is exactly the
PNT/rational clearing producer from v13, not a free valuation field. -/
theorem arithmeticPlan_of_actual_integerizer
    {q : ℕ} (hdegree : VDegreeBound q)
    (c : V.VActualIntegerizerCertificate q (vTau q)) :
    ArithmeticPlan q :=
  { degree := hdegree
    integerizer := actualIntegerizer_toVIntegerizerBound c }

/-- Transport the actual scaled Frobenius tower to the real-evaluation
nonvanishing interface used by the endpoint criterion
(nonvanishing.tex:200-275). -/
theorem actualTower_toVEventualNonvanishing
    {q p : ℕ} (tower : V.VActualFrobeniusTower q p) :
    VEventualNonvanishing q p := by
  intro r
  obtain ⟨k₀, hk₀⟩ :=
    V.vActualEventualNonvanishing_of_frobenius_tower tower r
  refine ⟨k₀, ?_⟩
  intro k hk
  rw [vRealPoly_eval_ratCast]
  exact_mod_cast hk₀ k hk

/-- An actual Frobenius tower supplies the nonvanishing plan for the same
base and auxiliary prime. -/
theorem nonvanishingPlan_of_actual_tower
    {q p : ℕ} (tower : V.VActualFrobeniusTower q p)
    (hp : p = vSeedPrime q) :
    NonvanishingPlan q := by
  subst p
  exact { eventual := actualTower_toVEventualNonvanishing tower }

end

end Li2Lean.B3

#print axioms Li2Lean.B3.actualIntegerizer_toVIntegerizerBound
#print axioms Li2Lean.B3.actualTower_toVEventualNonvanishing
#print axioms Li2Lean.B3.arithmeticPlan_of_actual_integerizer
