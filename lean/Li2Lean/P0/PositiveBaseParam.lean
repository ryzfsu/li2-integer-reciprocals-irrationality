/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Main
import Li2Lean.P0.Config

namespace Li2Lean.P0.PositiveBase

noncomputable section

/-- The finite positive-base range used by the v13 P0 interpolation. -/
def InRange (q : ℤ) : Prop := 2 ≤ q ∧ q ≤ 11

theorem two_inRange : InRange 2 := by
  norm_num [InRange]

theorem InRange.natAbs_ge_two {q : ℤ} (hq : InRange q) :
    2 ≤ Int.natAbs q := by
  rcases hq with ⟨hlo, hhi⟩
  have hq0 : 0 ≤ q := by omega
  have hnatCast : (2 : ℤ) ≤ (Int.natAbs q : ℤ) := by
    rw [Int.natAbs_of_nonneg hq0]
    exact hlo
  exact_mod_cast hnatCast

/-- The canonical literal P0 determinant family at the integer base `q`. -/
def family (q : ℤ) (hq : InRange q) : P0Family where
  a := q
  base_abs_ge_two := hq.natAbs_ge_two
  G := fun m => (p0CanonicalPolynomial q m).map (algebraMap ℚ ℝ)
  G_source := by
    intro m hm
    rfl

/-- The q-dependent entire source function `F_{g,q}` from v13 (3.1). -/
noncomputable def p0EntireQ (q : ℤ) (g : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (z * Complex.ofReal (Real.log (q : ℝ))) *
    (∏ r ∈ Finset.range g, (z + (r + 1 : ℕ))) / (Nat.factorial g : ℂ)

/-- The q-dependent binomial source value `U_i(q)`. -/
noncomputable def p0UComplex (q : ℤ) (g i : ℕ) : ℂ :=
  (q : ℂ) ^ i * (Nat.choose (i + g) g : ℂ)

/-- The q-dependent divided-difference source entry `C_ij(q)`. -/
noncomputable def p0CComplex (q : ℤ) (g i j : ℕ) : ℂ :=
  if i = j then
    -p0UComplex q g i * ∑ r ∈ Finset.range g, ((i + r + 1 : ℕ) : ℂ)⁻¹
  else
    (p0UComplex q g i - p0UComplex q g j) / ((j : ℂ) - (i : ℂ))

/-- The q-parameterized contour identity contract.  Its proof is a separate
analytic obligation for each allowed integer base; the q=2 regression is
proved below by definitional reduction. -/
def ContourIdentity (q : ℤ) : Prop :=
  InRange q → ∀ g i j : ℕ, i < 4 * g → j < 4 * g →
    p0CComplex q g i j =
      -p0EllipseIntegral (2 * g) (fun z =>
        p0EntireQ q g z / ((z - (i : ℂ)) * (z - (j : ℂ)))) +
        if i = j then Complex.ofReal (Real.log (q : ℝ)) *
          p0UComplex q g i else 0

theorem p0EntireQ_two (g : ℕ) (z : ℂ) :
    p0EntireQ 2 g z = p0Entire g z := by
  norm_num [p0EntireQ, p0Entire]

theorem p0UComplex_two (g i : ℕ) :
    p0UComplex 2 g i = p0U g i := by
  norm_num [p0UComplex, p0U]

theorem p0CComplex_two (g i j : ℕ) :
    p0CComplex 2 g i j = p0C g i j := by
  by_cases h : i = j <;> simp [p0CComplex, p0C, p0UComplex, p0U, h]

theorem contourIdentity_two_iff :
    ContourIdentity 2 ↔ P0ContourIdentityStatement := by
  constructor
  · intro h g i j hi hj
    simpa [ContourIdentity, p0CComplex, p0C, p0UComplex, p0U,
      p0EntireQ, p0Entire] using h two_inRange g i j hi hj
  · intro h _ g i j hi hj
    simpa [ContourIdentity, p0CComplex, p0C, p0UComplex, p0U,
      p0EntireQ, p0Entire] using h g i j hi hj

/-! The endpoint criterion itself is already base-independent.  This wrapper
records the exact consumer target for each q-specific certificate. -/
theorem irrational_of_endpoint_certificate (q : ℤ)
    (certificate : EndpointCertificate (li2InvValue q)) :
    Irrational (li2InvValue q) :=
  l1_endpoint_criterion (li2InvValue q) certificate

/-- The q-parameterized analytic input at the actual value `Li₂(1/q)`. -/
def AnalyticEstimateAt (alpha : ℝ) (q : ℤ) (F : P0Family) : Prop :=
  InRange q → F.a = q → ∀ m, 8 ≤ m → 4 ∣ m →
    |(F.G m).eval (li2InvValue q)| ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301)

/-- Shared inputs required to run the generic P0 endpoint criterion at base q.
The analytic and base-specific arithmetic estimates are kept explicit. -/
structure EndpointInputs (alpha : ℝ) (q : ℤ) (F : P0Family) : Prop where
  in_range : InRange q
  family_base : F.a = q
  analytic : AnalyticEstimateAt alpha q F
  integerizer : P0IntegerizerBound F
  rate_margin : p0TauSharp q < alpha
  nonvanishing : P0NonvanishingStatement F

/-- The logarithmic base shift in the v13 fields, `lambda = log(q/2)`. -/
def logShift (q : ℤ) : ℝ := Real.log ((q : ℝ) / 2)

/-- The contour one-body field obtained from the q=2 field by its affine shift. -/
def phi (q : ℤ) (phiTwo : ℂ → ℝ) (z : ℂ) : ℝ :=
  phiTwo z + logShift q * z.re

/-- The frequency one-body field obtained from the q=2 field by its affine shift. -/
def psi (q : ℤ) (psiTwo : ℝ → ℝ) (t : ℝ) : ℝ :=
  psiTwo t - logShift q * t

theorem logShift_two : logShift 2 = 0 := by
  norm_num [logShift]

theorem phi_two (phiTwo : ℂ → ℝ) (z : ℂ) : phi 2 phiTwo z = phiTwo z := by
  simp [phi, logShift_two]

theorem psi_two (psiTwo : ℝ → ℝ) (t : ℝ) : psi 2 psiTwo t = psiTwo t := by
  simp [psi, logShift_two]

/-- The fixed-base integerizer rate varies by the explicit logarithmic
correction obtained from the v13 arithmetic formula. -/
theorem tauSharp_affine (q : ℤ) (hq : 2 ≤ q) :
    p0TauSharp q = p0TauSharp 2 +
      (1 / 16 : ℝ) * Real.log ((q - 1 : ℤ) : ℝ) -
      (13 / 16 : ℝ) * Real.log (q : ℝ) +
      (13 / 16 : ℝ) * Real.log 2 := by
  have hq0 : 0 ≤ q := by omega
  have hq1 : 0 ≤ q - 1 := by omega
  rw [show p0TauSharp q = p0K + (1 / 16 : ℝ) * Real.log (q - 1) -
      (13 / 16 : ℝ) * Real.log q by
        simp [p0TauSharp, Int.natAbs_of_nonneg hq0,
          Int.natAbs_of_nonneg hq1]]
  rw [p0TauSharp_two_eq]
  norm_num
  ring

theorem family_two_base : (family 2 two_inRange).a = p0A2CanonicalFamily.a := by
  rfl

theorem family_two_polynomial (m : ℕ) :
    (family 2 two_inRange).G m = p0A2CanonicalFamily.G m := by
  rfl

theorem analyticEstimateAt_two_iff (alpha : ℝ) (F : P0Family) :
    AnalyticEstimateAt alpha 2 F ↔ P0AnalyticEstimateAt alpha F := by
  constructor
  · intro h
    intro hbase m hm h4
    exact h two_inRange hbase m hm h4
  · intro h hRange hbase m hm h4
    have hbase' : F.a = 2 := by simpa using hbase
    exact h hbase' m hm h4

theorem tauSharp_two_regression :
    p0TauSharp 2 = p0K - 13 / 16 * Real.log 2 :=
  p0TauSharp_two_eq

theorem sourceBeta_two_regression :
    sourceBeta 2 = li2InvValue (2 : ℤ) :=
  sourceBeta_two_eq_li2InvValue_two

end

end Li2Lean.P0.PositiveBase
