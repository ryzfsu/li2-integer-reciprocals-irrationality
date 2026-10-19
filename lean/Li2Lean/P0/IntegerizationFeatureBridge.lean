/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizerRate
import Mathlib.Algebra.Polynomial.Coeff

namespace Li2Lean.P0.Integerization

noncomputable section

/-!  A coefficient-level bridge for the integerization certificate.

The paper's rank-one expansion supplies divisibility of every coefficient of
the already integerized polynomial.  This file keeps that input explicit and
turns it into the polynomial divisibility field consumed by
`P0IntegerizerFeatureRateCertificate`.  No valuation or rank-one statement is
assumed here.
-/

theorem polynomial_C_dvd_of_coeff_dvd
    (P : Polynomial ℤ) (feature : ℕ)
    (hcoeff : ∀ n, (feature : ℤ) ∣ P.coeff n) :
    Polynomial.C (feature : ℤ) ∣ P := by
  exact (Polynomial.C_dvd_iff_dvd_coeff (feature : ℤ) P).2 hcoeff

noncomputable def p0IntegerizerFeatureDivisibility_of_coeff_witness
    (F : P0Family) (rate : ℝ)
    (D : ℕ → ℚ) (featureFactor : ℕ → ℕ)
    (hcoeff : ∀ m, 0 < m → 4 ∣ m →
      ∃ P : Polynomial ℤ,
        (∀ n, (featureFactor m : ℤ) ∣ P.coeff n) ∧
          Polynomial.map (Int.castRingHom ℝ) P =
            Polynomial.C (p0A2BaselineD m : ℝ) * F.G m)
    (hpos : ∀ m, 0 < m → 4 ∣ m → 0 < featureFactor m)
    (hfactor : ∀ m, 0 < m → 4 ∣ m →
      p0A2BaselineD m = D m * featureFactor m)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m →
      0 < m → 4 ∣ m →
        Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε) :
    P0IntegerizerFeatureRateCertificate F rate := by
  refine
    { D := D
      featureFactor := featureFactor
      featureFactor_pos := hpos
      baseline_factorization := hfactor
      featureDivisibility := ?_
      oddPrimeValuationRate := hrate }
  intro m hm h4
  rcases hcoeff m hm h4 with ⟨P, hPcoeff, hPmap⟩
  exact ⟨P, polynomial_C_dvd_of_coeff_dvd P (featureFactor m) hPcoeff, hPmap⟩

/-! The exact a-adic feature exponent from docs/6333 §8.2, encoded as the
natural feature factor expected by the certificate.  The coefficient witness
for this factor is intentionally separate: it is the rank-one expansion
obligation, not a consequence of this definition.
-/

def p0A2TwoFeatureFactor (m : ℕ) : ℕ :=
  if h : 4 ∣ m then
    2 ^ (13 * (m / 4) ^ 2 - 4 * (m / 4))
  else 1

def p0A2TwoFeatureD (m : ℕ) : ℚ :=
  p0A2BaselineD m / (p0A2TwoFeatureFactor m : ℚ)

theorem p0A2TwoFeatureFactor_pos {m : ℕ} (hm : 4 ∣ m) :
    0 < p0A2TwoFeatureFactor m := by
  simp [p0A2TwoFeatureFactor, hm]

theorem p0A2TwoFeatureD_factorization {m : ℕ} (hm : 4 ∣ m) :
    p0A2BaselineD m = p0A2TwoFeatureD m * p0A2TwoFeatureFactor m := by
  have hpos : 0 < p0A2TwoFeatureFactor m := p0A2TwoFeatureFactor_pos hm
  have hne : (p0A2TwoFeatureFactor m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  unfold p0A2TwoFeatureD
  field_simp

theorem p0A2TwoFeatureFactor_eq_explicit {m h : ℕ} (hm : m = 4 * h) :
    p0A2TwoFeatureFactor m = 2 ^ (13 * h ^ 2 - 4 * h) := by
  subst hm
  simp [p0A2TwoFeatureFactor]

theorem p0A2TwoFeatureD_factorization_explicit {m h : ℕ}
    (hm : m = 4 * h) :
    p0A2BaselineD m = p0A2TwoFeatureD m *
      (2 ^ (13 * h ^ 2 - 4 * h) : ℕ) := by
  rw [← p0A2TwoFeatureFactor_eq_explicit hm]
  exact p0A2TwoFeatureD_factorization (by
    subst hm
    simpa [Nat.mul_comm] using (dvd_mul_left 4 h))

theorem p0A2TwoFeatureD_pos {m : ℕ} (hmpos : 0 < m) (hm : 4 ∣ m) :
    0 < p0A2TwoFeatureD m := by
  unfold p0A2TwoFeatureD
  exact div_pos (p0A2BaselineD_pos hmpos)
    (by exact_mod_cast p0A2TwoFeatureFactor_pos hm)

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.polynomial_C_dvd_of_coeff_dvd
#print axioms Li2Lean.P0.Integerization.p0IntegerizerFeatureDivisibility_of_coeff_witness
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureFactor_pos
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureD_factorization
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureD_pos

namespace Li2Lean.P0.Integerization

noncomputable section

/-! A base-independent bridge from a coefficient witness to the integerizer
contract. The specialized certificate above is tied to `p0A2BaselineD`;
this theorem keeps the baseline factor explicit, so a q-parametric S08
witness can instantiate it without identifying the q-family with `a = 2`. -/
theorem p0IntegerizerBoundAt_of_generic_coeff_witness
    (F : P0Family) (rate : ℝ)
    (D baseline : ℕ → ℚ) (featureFactor : ℕ → ℕ)
    (hDpos : ∀ m, 0 < m → 4 ∣ m → 0 < D m)
    (hfeature_pos : ∀ m, 0 < m → 4 ∣ m → 0 < featureFactor m)
    (hfactor : ∀ m, 0 < m → 4 ∣ m →
      baseline m = D m * (featureFactor m : ℚ))
    (hcoeff : ∀ m, 0 < m → 4 ∣ m →
      ∃ P : Polynomial ℤ,
        Polynomial.C (featureFactor m : ℤ) ∣ P ∧
          Polynomial.map (Int.castRingHom ℝ) P =
            Polynomial.C (baseline m : ℝ) * F.G m)
    (hdegree : ∀ m, 0 < m → 4 ∣ m → (F.G m).natDegree ≤ m)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m →
      0 < m → 4 ∣ m →
        Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε) :
    P0IntegerizerBoundAt F rate := by
  refine ⟨D, hDpos, hdegree, ?_, hrate⟩
  intro m hm h4
  rcases hcoeff m hm h4 with ⟨P, hdiv, hP⟩
  obtain ⟨Q, hPQ⟩ := hdiv
  refine ⟨Q, ?_⟩
  have hmap : Polynomial.map (Int.castRingHom ℝ) P =
      Polynomial.C (featureFactor m : ℝ) *
        Polynomial.map (Int.castRingHom ℝ) Q := by
    rw [hPQ, Polynomial.map_mul, Polynomial.map_C]
    norm_num
  have hscale : (featureFactor m : ℝ) * (D m : ℝ) =
      (baseline m : ℝ) := by
    exact_mod_cast (by
      rw [mul_comm]
      exact (hfactor m hm h4).symm)
  have hscalePoly : Polynomial.C (featureFactor m : ℝ) *
      Polynomial.C (D m : ℝ) = Polynomial.C (baseline m : ℝ) := by
    calc
      _ = Polynomial.C ((featureFactor m : ℝ) * (D m : ℝ)) := by
        simp [Polynomial.C_mul]
      _ = _ := congrArg Polynomial.C hscale
  have htarget : Polynomial.C (featureFactor m : ℝ) *
      Polynomial.map (Int.castRingHom ℝ) Q =
      Polynomial.C (featureFactor m : ℝ) *
        (Polynomial.C (D m : ℝ) * F.G m) := by
    calc
      _ = Polynomial.map (Int.castRingHom ℝ) P := hmap.symm
      _ = Polynomial.C (baseline m : ℝ) * F.G m := hP
      _ = Polynomial.C (featureFactor m : ℝ) *
          (Polynomial.C (D m : ℝ) * F.G m) := by
            rw [← hscalePoly]
            ring
  have hfactor_pos : 0 < (featureFactor m : ℝ) := by
    exact_mod_cast hfeature_pos m hm h4
  exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (ne_of_gt hfactor_pos)) htarget

end

end Li2Lean.P0.Integerization
