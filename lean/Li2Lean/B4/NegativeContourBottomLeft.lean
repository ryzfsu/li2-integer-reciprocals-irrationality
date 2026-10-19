/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourTangent
import Li2Lean.B4.ContourSum

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.Config

/-!
Bottom and lower-left interfaces for the rational-height rectangle in
v13 `hp-tail.tex:319-371`.

The definitions below specialize the contour to `hpNegPhi` and its fixed
height rectangle.  The analytic estimates are named fields of
`HpNegBottomLeftEnvelope`; no arbitrary coefficient sequence occurs here.
The finite geometry and the polynomial positivity used by the bottom
concavity argument are proved in this file.  The sum-to-integral and valley
estimates remain explicit hypotheses until their dedicated analytic lemmas
are merged.
-/

/-! ### Concrete side geometry -/

/-- The lower half of the left side, used in v13 `hp-tail.tex:345-355`. -/
def hpNegLeftLowerSide (n : ℕ) : Set ℂ :=
  hpNegLeftSide n ∩ {w | w.im ≤ 0}

/-- The real and imaginary coordinates of a bottom-side point. -/
theorem hp_neg_bottom_side_coordinates {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegBottomSide n) :
    (-1 / 2 : ℝ) ≤ w.re ∧ w.re ≤ (n : ℝ) + 1 / 2 ∧
      w.im = -((n : ℝ) / 5) := by
  have h := hw
  simp [hpNegBottomSide, hpRectLower, hpRectUpper] at h
  rcases h with ⟨hlo, hhi, him⟩
  have hhi' : w.re ≤ (n : ℝ) + 1 / 2 := by
    convert hhi using 1 <;> norm_num
  refine ⟨hlo, hhi', ?_⟩
  calc
    w.im = -((n : ℝ) * (5 : ℝ)⁻¹) := him
    _ = -((n : ℝ) / 5) := by ring

/-- The real and imaginary coordinates of a lower-left point. -/
theorem hp_neg_left_lower_side_coordinates {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegLeftLowerSide n) :
    w.re = (-1 / 2 : ℝ) ∧
      -((n : ℝ) / 5) ≤ w.im ∧ w.im ≤ 0 := by
  rcases hw with ⟨hwleft, hwlower⟩
  have hleft :
      w.re = (-1 / 2 : ℝ) ∧
        -((n : ℝ) / 5) ≤ w.im ∧ w.im ≤ (n : ℝ) / 5 := by
    have h := hwleft
    simp [hpNegLeftSide, hpRectLower, hpRectUpper] at h
    rcases h with ⟨hre, hlow, hhigh⟩
    have hlow' : -((n : ℝ) / 5) ≤ w.im := by
      simpa [div_eq_mul_inv] using hlow
    have hhigh' : w.im ≤ (n : ℝ) / 5 := by
      simpa [div_eq_mul_inv] using hhigh
    exact ⟨hre, hlow', hhigh'⟩
  have hwlower' : w.im ≤ 0 := hwlower
  exact ⟨hleft.1, hleft.2.1, hwlower'⟩

/-- Scaled real and imaginary coordinates used in the sum-to-integral
decomposition `hp-tail.tex:307-316`. -/
def hpNegScaledX (n : ℕ) (w : ℂ) : ℝ := w.re / (n : ℝ)

def hpNegScaledY (n : ℕ) (w : ℂ) : ℝ := w.im / (n : ℝ)

theorem hp_neg_bottom_scaled_window {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    (-(1 / 60 : ℝ)) ≤ hpNegScaledX n w ∧
      hpNegScaledX n w ≤ 61 / 60 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases hp_neg_bottom_side_coordinates hw with ⟨hlo, hhi, _⟩
  constructor
  · apply (le_div_iff₀ hnR).2
    nlinarith [hlo, hnR30]
  · apply (div_le_iff₀ hnR).2
    nlinarith [hhi, hnR30]

theorem hp_neg_bottom_scaled_im {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    hpNegScaledY n w = -(1 / 5 : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  rcases hp_neg_bottom_side_coordinates hw with ⟨_, _, him⟩
  unfold hpNegScaledY
  rw [him]
  field_simp

theorem hp_neg_left_lower_scaled_window {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegLeftLowerSide n) :
    (-(1 / 5 : ℝ)) ≤ hpNegScaledY n w ∧
      hpNegScaledY n w ≤ 0 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases hp_neg_left_lower_side_coordinates hw with ⟨_, himlo, himhi⟩
  constructor
  · apply (le_div_iff₀ hnR).2
    nlinarith [himlo, hnR30]
  · apply (div_le_iff₀ hnR).2
    nlinarith [himhi]

theorem hp_neg_left_lower_scaled_x_window {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegLeftLowerSide n) :
    (-(1 / 60 : ℝ)) ≤ hpNegScaledX n w ∧
      hpNegScaledX n w < 0 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases hp_neg_left_lower_side_coordinates hw with ⟨hre, _, _⟩
  constructor
  · apply (le_div_iff₀ hnR).2
    nlinarith [hre, hnR30]
  · apply (div_lt_iff₀ hnR).2
    nlinarith [hre, hnR30]

/-- The bottom-side point lies in the positivity window for the concavity
polynomial from v13 `hp-tail.tex:343-355`. -/
theorem hp_neg_bottom_polynomial_pos {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    0 < hpNegP (hpNegScaledX n w) := by
  rcases hp_neg_bottom_scaled_window hn hw with ⟨hlo, hhi⟩
  exact hp_neg_p_pos_on_window hlo hhi

/-- Every denominator factor in the bottom-side tangent computation is
strictly positive. -/
theorem hp_neg_bottom_denominator_pos (a : ℝ) {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    0 < hpNegD a (hpNegScaledX n w) := by
  exact hp_neg_D_pos _ _

/-! ### The valley error and exact sum-to-integral obligations -/

/-- The right-endpoint quadrature error for `cpLog`, isolated from the two
scaled cells in `ContourSum`.  This is the quantity bounded from below by
the valley argument in v13 `hp-tail.tex:307-316`. -/
def hpNegValleyError (ζ : ℂ) (g : ℕ) : ℝ :=
  (∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
    (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u)

theorem hp_neg_valley_error_eq_sum_sub_integral (ζ : ℂ) (g : ℕ) :
    hpNegValleyError ζ g =
      (∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) := by
  rfl

theorem hp_neg_valley_log_argument_pos {g : ℕ} (hg : 1 ≤ g) :
    0 < (8 : ℝ) * ((g : ℝ) + 1) := by
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  nlinarith

/-! ### Explicit envelope package -/

/-- The bottom/left analytic envelope.  Its `sum_to_integral` field is the
two-sided cell input required by `hp_product_log_error_bound`; `valley_lower`
is the missing lower estimate for a log-distance valley.  The final `bottom`
and `left` fields are exactly the side inequalities consumed by
`HpNegFourSideBound`.  Every quantity is tied to the concrete `hpNegPhi`
sequence through `hpNegBoundaryLog`; no arbitrary `B` is quantified. -/
structure HpNegBottomLeftEnvelope (q : ℕ) where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  n0 : ℕ
  n0_spec : 30 ≤ n0
  cell_C : ℝ
  cell_C_nonneg : 0 ≤ cell_C
  sum_to_integral : ∀ n : ℕ, n0 ≤ n → ∀ xi : ℂ,
    HpRightErrorBound cell_C n n (2 * n) xi ∧
      HpRightErrorBound cell_C n 0 n xi
  endpoint : ∀ n : ℕ, n0 ≤ n → ∀ xi : ℂ,
    HpEndpointBound cell_C n xi
  valley_lower : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g →
    (∀ u ∈ Set.Icc (0 : ℝ) (g : ℝ),
      ζ + (u : ℂ) ≠ 0) →
    -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g
  bottom : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegBottomSide n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))
  left : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegLeftSide n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-! ### Small helper consequences used by the eventual bottom proof -/

theorem hp_neg_product_log_error_bound_three
    (n : ℕ) (hn : 0 < n) (xi : ℂ)
    (hnum : HpRightErrorBound 3 n n (2 * n) xi)
    (hden : HpRightErrorBound 3 n 0 n xi)
    (hend : HpEndpointBound 3 n xi) :
    |hpProductLogError n xi| ≤
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have h := hp_product_log_error_bound (C := (3 : ℝ)) (by norm_num)
    n hn xi hnum hden hend
  norm_num at h ⊢
  exact h

def hp_neg_bottom_left_envelope_of_data {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (n0 : ℕ) (hn0 : 30 ≤ n0) (C : ℝ) (hC : 0 ≤ C)
    (hsum : ∀ n : ℕ, n0 ≤ n → ∀ xi : ℂ,
      HpRightErrorBound C n n (2 * n) xi ∧
        HpRightErrorBound C n 0 n xi)
    (hend : ∀ n : ℕ, n0 ≤ n → ∀ xi : ℂ, HpEndpointBound C n xi)
    (hvalley : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g →
      (∀ u ∈ Set.Icc (0 : ℝ) (g : ℝ), ζ + (u : ℂ) ≠ 0) →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g)
    (hbottom : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegBottomSide n,
      hpNegBoundaryLog q n w ≤
        (n : ℝ) * (hpNegT q : ℝ) +
          (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)))
    (hleft : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegLeftSide n,
      hpNegBoundaryLog q n w ≤
        (n : ℝ) * (hpNegT q : ℝ) +
          (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))) :
    HpNegBottomLeftEnvelope q := by
  exact
    { q_spec := hq
      n0 := n0
      n0_spec := hn0
      cell_C := C
      cell_C_nonneg := hC
      sum_to_integral := hsum
      endpoint := hend
      valley_lower := hvalley
      bottom := hbottom
      left := hleft }

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_side_coordinates
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_scaled_window
#print axioms Li2Lean.B4.NegContour.hp_neg_left_lower_scaled_window
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_polynomial_pos
#print axioms Li2Lean.B4.NegContour.hp_neg_product_log_error_bound_three
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_left_envelope_of_data
