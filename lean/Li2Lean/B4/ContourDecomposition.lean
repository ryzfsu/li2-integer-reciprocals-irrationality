/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Vendor.PNT.ResidueCalcOnRectangles

/-!
# Exponential pole decompositions for the B4 contour

The contour in `hp-tail.tex:256-410` has simple and double poles at the
integers.  The two identities below are the first two terms of the exact
`dslope` expansion of `exp (lambda * w)` at a pole `j`.  The remaining terms
are entire, so their rectangle integrals vanish by the vendored Cauchy-Goursat
interface.
-/

namespace Li2Lean.B4.ContourDecomposition

noncomputable section

open Complex
open Filter Topology

/-- The exponential phase occurring on the negative contour. -/
def expAffine (lambda : ℂ) : ℂ → ℂ := fun w => Complex.exp (lambda * w)

/-- The first divided difference at the pole `j`. -/
def expSimpleRemainder (lambda j : ℂ) : ℂ → ℂ :=
  dslope (expAffine lambda) j

/-- The second divided difference at the pole `j`. -/
def expDoubleRemainder (lambda j : ℂ) : ℂ → ℂ :=
  dslope (expSimpleRemainder lambda j) j

/-- Lower-left and upper-right corners of the scaled v13 rectangle. -/
def v13RectangleLower (n : ℕ) (beta : ℝ) : ℂ :=
  Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * beta) * Complex.I

def v13RectangleUpper (n : ℕ) (beta : ℝ) : ℂ :=
  Complex.ofReal ((n : ℝ) + 1 / 2) +
    Complex.ofReal ((n : ℝ) * beta) * Complex.I

def v13Rectangle (n : ℕ) (beta : ℝ) : Set ℂ :=
  Complex.Rectangle (v13RectangleLower n beta) (v13RectangleUpper n beta)

lemma expAffine_differentiable (lambda : ℂ) :
    Differentiable ℂ (expAffine lambda) := by
  unfold expAffine
  fun_prop

lemma expSimpleRemainder_differentiable (lambda j : ℂ) :
    Differentiable ℂ (expSimpleRemainder lambda j) := by
  have hUniv : (Set.univ : Set ℂ) ∈ 𝓝 j := by simp
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope hUniv).2
    (expAffine_differentiable lambda).differentiableOn

lemma expDoubleRemainder_differentiable (lambda j : ℂ) :
    Differentiable ℂ (expDoubleRemainder lambda j) := by
  have hUniv : (Set.univ : Set ℂ) ∈ 𝓝 j := by simp
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope hUniv).2
    (expSimpleRemainder_differentiable lambda j).differentiableOn

/-- First-order `dslope` expansion, divided by the simple pole. -/
theorem exp_simple_pole_decomp (lambda j w : ℂ) (hw : w ≠ j) :
    expAffine lambda w / (w - j) =
      expAffine lambda j / (w - j) + expSimpleRemainder lambda j w := by
  have hden : w - j ≠ 0 := sub_ne_zero.mpr hw
  have hds := sub_smul_dslope (expAffine lambda) j w
  have hds' : (w - j) * expSimpleRemainder lambda j w =
      expAffine lambda w - expAffine lambda j := by
    simpa [expSimpleRemainder, smul_eq_mul] using hds
  apply (div_eq_iff hden).2
  calc
    expAffine lambda w = expAffine lambda j +
        (expAffine lambda w - expAffine lambda j) := by ring
    _ = expAffine lambda j + (w - j) * expSimpleRemainder lambda j w := by
      rw [hds']
    _ = (expAffine lambda j / (w - j) +
        expSimpleRemainder lambda j w) * (w - j) := by
      field_simp [hden]

/-- Second-order `dslope` expansion, divided by the double pole. -/
theorem exp_double_pole_decomp (lambda j w : ℂ) (hw : w ≠ j) :
    expAffine lambda w / ((w - j) * (w - j)) =
      expAffine lambda j / ((w - j) * (w - j)) +
        (expSimpleRemainder lambda j j) / (w - j) +
          expDoubleRemainder lambda j w := by
  have hden : w - j ≠ 0 := sub_ne_zero.mpr hw
  have hden2 : (w - j) * (w - j) ≠ 0 := mul_ne_zero hden hden
  have hds₁ := sub_smul_dslope (expAffine lambda) j w
  have hds₁' : (w - j) * expSimpleRemainder lambda j w =
      expAffine lambda w - expAffine lambda j := by
    simpa [expSimpleRemainder, smul_eq_mul] using hds₁
  have hds₂ := sub_smul_dslope (expSimpleRemainder lambda j) j w
  have hds₂' : (w - j) * expDoubleRemainder lambda j w =
      expSimpleRemainder lambda j w - expSimpleRemainder lambda j j := by
    simpa [expDoubleRemainder, smul_eq_mul] using hds₂
  have hFpoly : expAffine lambda w = expAffine lambda j +
      (w - j) * expSimpleRemainder lambda j w := by
    calc
      expAffine lambda w = expAffine lambda j +
          (expAffine lambda w - expAffine lambda j) := by ring
      _ = expAffine lambda j + (w - j) * expSimpleRemainder lambda j w := by
        rw [hds₁']
  have hGpoly : expSimpleRemainder lambda j w =
      expSimpleRemainder lambda j j +
        (w - j) * expDoubleRemainder lambda j w := by
    calc
      expSimpleRemainder lambda j w = expSimpleRemainder lambda j j +
          (expSimpleRemainder lambda j w - expSimpleRemainder lambda j j) := by ring
      _ = expSimpleRemainder lambda j j +
          (w - j) * expDoubleRemainder lambda j w := by
        rw [hds₂']
  have hpoly : expAffine lambda w =
      expAffine lambda j +
        (w - j) * expSimpleRemainder lambda j j +
          (w - j) * (w - j) * expDoubleRemainder lambda j w := by
    calc
      expAffine lambda w = expAffine lambda j +
          (w - j) * expSimpleRemainder lambda j w := hFpoly
      _ = expAffine lambda j +
          (w - j) * (expSimpleRemainder lambda j j +
            (w - j) * expDoubleRemainder lambda j w) := by
            rw [hGpoly]
      _ = _ := by ring
  apply (div_eq_iff hden2).2
  calc
    expAffine lambda w = expAffine lambda j +
        (w - j) * expSimpleRemainder lambda j j +
          (w - j) * (w - j) * expDoubleRemainder lambda j w := hpoly
    _ = (expAffine lambda j / ((w - j) * (w - j)) +
        expSimpleRemainder lambda j j / (w - j) +
          expDoubleRemainder lambda j w) * ((w - j) * (w - j)) := by
      field_simp [hden]

/-- Both divided-difference remainders are entire. -/
theorem entire_remainder_holomorphicOn (lambda j : ℂ) :
    HolomorphicOn (expSimpleRemainder lambda j) Set.univ ∧
      HolomorphicOn (expDoubleRemainder lambda j) Set.univ := by
  exact ⟨(expSimpleRemainder_differentiable lambda j).differentiableOn,
    (expDoubleRemainder_differentiable lambda j).differentiableOn⟩

theorem exp_simple_remainder_holomorphicOn (lambda j : ℂ) (U : Set ℂ) :
    HolomorphicOn (expSimpleRemainder lambda j) U := by
  exact (expSimpleRemainder_differentiable lambda j).differentiableOn

theorem exp_double_remainder_holomorphicOn (lambda j : ℂ) (U : Set ℂ) :
    HolomorphicOn (expDoubleRemainder lambda j) U := by
  exact (expDoubleRemainder_differentiable lambda j).differentiableOn

theorem exp_simple_remainder_holomorphicOn_v13 (lambda j : ℂ)
    (n : ℕ) (beta : ℝ) :
    HolomorphicOn (expSimpleRemainder lambda j) (v13Rectangle n beta) := by
  exact exp_simple_remainder_holomorphicOn lambda j (v13Rectangle n beta)

theorem exp_double_remainder_holomorphicOn_v13 (lambda j : ℂ)
    (n : ℕ) (beta : ℝ) :
    HolomorphicOn (expDoubleRemainder lambda j) (v13Rectangle n beta) := by
  exact exp_double_remainder_holomorphicOn lambda j (v13Rectangle n beta)

/-- A holomorphic remainder has zero oriented integral on any rectangle. -/
theorem remainder_vanishesOnRectangle {R : ℂ → ℂ} {z w : ℂ}
    (hR : HolomorphicOn R (Complex.Rectangle z w)) :
    RectangleIntegral R z w = 0 := by
  exact hR.vanishesOnRectangle (by rfl)

theorem exp_simple_remainder_vanishesOnRectangle (lambda j z w : ℂ) :
    RectangleIntegral (expSimpleRemainder lambda j) z w = 0 := by
  apply remainder_vanishesOnRectangle
  exact exp_simple_remainder_holomorphicOn lambda j (Complex.Rectangle z w)

theorem exp_double_remainder_vanishesOnRectangle (lambda j z w : ℂ) :
    RectangleIntegral (expDoubleRemainder lambda j) z w = 0 := by
  apply remainder_vanishesOnRectangle
  exact exp_double_remainder_holomorphicOn lambda j (Complex.Rectangle z w)

theorem exp_simple_remainder_vanishesOn_v13Rectangle
    (lambda j : ℂ) (n : ℕ) (beta : ℝ) :
    RectangleIntegral (expSimpleRemainder lambda j)
        (v13RectangleLower n beta) (v13RectangleUpper n beta) = 0 := by
  exact exp_simple_remainder_vanishesOnRectangle lambda j
    (v13RectangleLower n beta) (v13RectangleUpper n beta)

theorem exp_double_remainder_vanishesOn_v13Rectangle
    (lambda j : ℂ) (n : ℕ) (beta : ℝ) :
    RectangleIntegral (expDoubleRemainder lambda j)
        (v13RectangleLower n beta) (v13RectangleUpper n beta) = 0 := by
  exact exp_double_remainder_vanishesOnRectangle lambda j
    (v13RectangleLower n beta) (v13RectangleUpper n beta)

end

end Li2Lean.B4.ContourDecomposition

#print axioms Li2Lean.B4.ContourDecomposition.exp_simple_pole_decomp
#print axioms Li2Lean.B4.ContourDecomposition.exp_double_pole_decomp
#print axioms Li2Lean.B4.ContourDecomposition.entire_remainder_holomorphicOn
#print axioms Li2Lean.B4.ContourDecomposition.exp_simple_remainder_vanishesOnRectangle
#print axioms Li2Lean.B4.ContourDecomposition.exp_double_remainder_vanishesOnRectangle
#print axioms Li2Lean.B4.ContourDecomposition.exp_simple_remainder_vanishesOn_v13Rectangle
#print axioms Li2Lean.B4.ContourDecomposition.exp_double_remainder_vanishesOn_v13Rectangle
