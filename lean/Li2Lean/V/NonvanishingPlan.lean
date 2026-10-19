/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.V.VFamily

/-!
# Signed V Frobenius and nonvanishing producer

This is the arithmetic interface for the signed determinant in v13.  The
polynomial in every field below is the actual `V.vPolynomial`; there is no
free valuation function and no unrelated determinant parameter.  The finite
seed and the coefficientwise Frobenius checks remain producer fields until
the row reduction is formalized.

Source anchors:
* `nonvanishing.tex:146-198` (the six signed seed reductions),
* `nonvanishing.tex:200-258` (`P_{r,k}(X)=Q^(13Q)G_(4Q,-r)(X/Q^2)` and
  the coefficientwise Frobenius congruence),
* `nonvanishing.tex:262-275` (eventual nonvanishing at a fixed rational
  point).

The p-adic unit-constant lemma is proved here from a strict tail norm bound.
The tail bound is kept as a named field of the producer: this isolates the
actual coefficient/Frobenius work and prevents a free `vp` or a false theorem
about arbitrary polynomials.
-/

namespace Li2Lean.V

noncomputable section

open scoped BigOperators

/-! ## Actual determinant and its pinned Gauss valuation -/

/-- The signed determinant at an arbitrary paper index `m`, with the v13
parameter `a = -q` and the same `m / 4` convention as the endpoint interface.
Source: `v-arithmetic.tex:13-35`. -/
def vNonvanishingDeterminant (q m : ℕ) : Polynomial ℚ :=
  vPolynomial (m / 4) (-(q : ℤ))

theorem vNonvanishingDeterminant_four_mul (q n : ℕ) :
    vNonvanishingDeterminant q (4 * n) = vPolynomial n (-(q : ℤ)) := by
  unfold vNonvanishingDeterminant
  rw [Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]

/-- Gauss valuation of the actual determinant.  This is the valuation used by
the residue-block and outer-pole certificates; the empty-support convention
is the standard `padicValRat` convention for the zero polynomial. -/
def vNonvanishingGaussValuation (q m p : ℕ) : ℤ :=
  let P := vNonvanishingDeterminant q m
  if h : P.support.Nonempty then
    P.support.inf' h (fun i => padicValRat p (P.coeff i))
  else 0

theorem vNonvanishingGaussValuation_coeff {q m p : ℕ} {E : ℤ}
    (h : vNonvanishingGaussValuation q m p ≥ -E) :
    ∀ i : ℕ, (vNonvanishingDeterminant q m).coeff i ≠ 0 →
      -E ≤ padicValRat p ((vNonvanishingDeterminant q m).coeff i) := by
  intro i hi
  have hmem : i ∈ (vNonvanishingDeterminant q m).support :=
    Polynomial.mem_support_iff.mpr hi
  have hne : (vNonvanishingDeterminant q m).support.Nonempty := ⟨i, hmem⟩
  unfold vNonvanishingGaussValuation at h
  rw [dif_pos hne] at h
  exact le_trans h (Finset.inf'_le _ hmem)

/- The generic `a = 2` determinant remains the same source matrix as the
positive half-value route; this is the required regression instance. -/
theorem vNonvanishingDeterminant_positive_two_regression (n : ℕ) :
    vPolynomial n (2 : ℤ) = Matrix.det (vSourceMatrix n (2 : ℤ)) :=
  vPolynomial_two n

/-! ## The scaled Frobenius polynomial -/

/-- The scaled polynomial in v13 `nonvanishing.tex:200-214`.
For `Q = p^k`, this is
`Q^(13Q) * G_(4Q,-q)(X / Q^2)`, expressed using `Polynomial.comp`. -/
def vFrobeniusScaledPolynomial (q p k : ℕ) : Polynomial ℚ :=
  let Q : ℕ := p ^ k
  Polynomial.C ((Q : ℚ) ^ (13 * Q)) *
    (vPolynomial Q (-(q : ℤ))).comp
      (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X)

/-- Evaluation at the scaled argument cancels the substitution exactly.  This
is the algebraic bridge from the p-adic scaled determinant to the actual
`V.vPolynomial` value and does not use a Frobenius congruence. -/
theorem vFrobeniusScaledPolynomial_eval_scaled (q p k : ℕ) (hp : 0 < p) (r : ℚ) :
    (vFrobeniusScaledPolynomial q p k).eval (((p ^ k : ℕ) : ℚ) ^ 2 * r) =
      (((p ^ k : ℕ) : ℚ) ^ (13 * (p ^ k)) ) *
        (vPolynomial (p ^ k) (-(q : ℤ))).eval r := by
  simp [vFrobeniusScaledPolynomial, Polynomial.eval_mul]
  field_simp [show (p ^ k : ℕ) ≠ 0 by positivity]
  simp [hp.ne']

/-! ## Unit-constant p-adic nonvanishing -/

/-- A p-adic unit constant with a strictly smaller tail norm.  `P` is pinned
to the scaled determinant rather than being an arbitrary polynomial. -/
structure VUnitConstantEvaluationInput (q p k : ℕ) (x : ℚ) : Prop where
  prime : Nat.Prime p
  constant_ne_zero :
    (vFrobeniusScaledPolynomial q p k).coeff 0 ≠ 0
  constant_unit :
    padicValRat p ((vFrobeniusScaledPolynomial q p k).coeff 0) = 0
  tail_norm_lt :
    padicNorm p
        ((vFrobeniusScaledPolynomial q p k).eval x -
          (vFrobeniusScaledPolynomial q p k).coeff 0) <
      padicNorm p ((vFrobeniusScaledPolynomial q p k).coeff 0)

/- The proof only needs the nonzero constant and the strict norm inequality;
the explicit unit field above records the exact v13 p-adic obligation. -/
theorem vFrobeniusScaled_eval_ne_zero_of_unit_constant
    {q p k : ℕ} {x : ℚ}
    (h : VUnitConstantEvaluationInput q p k x) :
    (vFrobeniusScaledPolynomial q p k).eval x ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨h.prime⟩
  intro hzero
  have heq :
      padicNorm p
          ((vFrobeniusScaledPolynomial q p k).eval x -
            (vFrobeniusScaledPolynomial q p k).coeff 0) =
        padicNorm p ((vFrobeniusScaledPolynomial q p k).coeff 0) := by
    rw [hzero, zero_sub, padicNorm.neg]
  have htail := h.tail_norm_lt
  rw [heq] at htail
  exact (lt_irrefl _ htail)

/-! ## Honest Frobenius producer and its eventual conclusion -/

/-- The concrete signed Frobenius producer.  The scaled integrality and unit
constant fields are the coefficientwise content of `eq:v-frobenius`; the
`unit_input` field packages the strict p-adic tail estimate at each fixed
rational point.  Every occurrence of the polynomial is the actual scaled
`vPolynomial`, so this cannot be discharged by choosing `vp := fun _ => 0`. -/
structure VActualFrobeniusTower (q p : ℕ) : Prop where
  prime : Nat.Prime p
  seed_constant_ne_zero :
    (vPolynomial 1 (-(q : ℤ))).coeff 0 ≠ 0
  seed_constant_unit :
    padicValRat p ((vPolynomial 1 (-(q : ℤ))).coeff 0) = 0
  scaled_coefficients_integral :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (vFrobeniusScaledPolynomial q p k).coeff i ≠ 0 →
        0 ≤ padicValRat p ((vFrobeniusScaledPolynomial q p k).coeff i)
  scaled_constant_unit :
    ∀ k : ℕ, 0 < k →
      (vFrobeniusScaledPolynomial q p k).coeff 0 ≠ 0 ∧
        padicValRat p ((vFrobeniusScaledPolynomial q p k).coeff 0) = 0
  unit_input :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      VUnitConstantEvaluationInput q p k
        (((p ^ k : ℕ) : ℚ) ^ 2 * r)

def vActualEventualNonvanishing (q p : ℕ) : Prop :=
  ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    (vPolynomial (p ^ k) (-(q : ℤ))).eval r ≠ 0

/-- The v13 eventual nonvanishing conclusion `nonvanishing.tex:262-275`.
The proof uses only the actual scaling identity and the p-adic unit-constant
lemma; all seed/Frobenius reduction work remains visible in the producer. -/
theorem vActualEventualNonvanishing_of_frobenius_tower
    {q p : ℕ} (tower : VActualFrobeniusTower q p) :
    vActualEventualNonvanishing q p := by
  intro r
  obtain ⟨k₀, hk₀⟩ := tower.unit_input r
  refine ⟨k₀, fun k hk => ?_⟩
  have hunit := vFrobeniusScaled_eval_ne_zero_of_unit_constant (hk₀ k hk)
  have hscale := vFrobeniusScaledPolynomial_eval_scaled q p k tower.prime.pos r
  intro hzero
  apply hunit
  rw [hscale, hzero, mul_zero]

/-! ## Integerizer/PNT producer boundary -/

/-- The actual determinant integerizer required by v13
`v-arithmetic.tex:353-421`.  The clearing factor is existential because it is
the output of the residue/outer-pole product, but it is tied by `clears` to
the concrete signed determinant and carries the full PNT rate statement. -/
structure VActualIntegerizerCertificate (q : ℕ) (tau : ℝ) where
  D : ℕ → ℕ
  D_pos : ∀ n : ℕ, 0 < n → 0 < D (4 * n)
  clears : ∀ n : ℕ, 0 < n → ∃ P : Polynomial ℤ,
    P.map (Int.castRingHom ℚ) =
      Polynomial.C (D (4 * n) : ℚ) * vPolynomial n (-(q : ℤ))
  pnt_rate : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
    Real.log (D (4 * n) : ℝ) / ((4 * n : ℕ) : ℝ) ^ 2 ≤ tau + ε

theorem vActualIntegerizer_D_ne_zero
    {q : ℕ} {tau : ℝ} (c : VActualIntegerizerCertificate q tau)
    {n : ℕ} (hn : 0 < n) : (c.D (4 * n) : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (c.D_pos n hn))

end

end Li2Lean.V

#print axioms Li2Lean.V.vFrobeniusScaled_eval_ne_zero_of_unit_constant
#print axioms Li2Lean.V.vActualEventualNonvanishing_of_frobenius_tower
