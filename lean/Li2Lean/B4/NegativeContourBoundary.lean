/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ContourSum
import Li2Lean.B4.RationalRectangleBoundary
import Li2Lean.B4.ResidueTailAlgebra
import Li2Lean.B4.NegativeContourTyped
import Li2Lean.Vendor.PNT.Rectangle
import Li2Lean.P0.CA.Contour.LogAtan

open Complex Real
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.B4.Residues
open Li2Lean.B4.NegativeContour
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.ConfigLogTaylor

/-!
The declarations in this file are the finite, rational part of the fixed-height
rectangle estimate in `hp-tail.tex:319-371`.  The three numbers below are the
certified tangent upper bounds from the rational-height plan.  The analytic
side estimates consume these values through `HpNegBoundaryCertificate`; this
keeps the finite checks separate from the (substantial) contour proof.
-/

/-- The rational height used in the replacement rectangle, v13
`hp-tail.tex:268-279` with the fixed-height choice from the B4 plan. -/
def hpNegHeight : ℚ := 1 / 5

theorem hp_neg_height_spec : hpNegHeight = (1 / 5 : ℚ) := by
  rfl

/-- Certified tangent bounds for the bottom side, one for each exceptional
base.  The decimal values are only comments; all fields are exact rationals.
These implement the finite part of v13 `hp-tail.tex:343-371`. -/
def hpNegT8 : ℚ := 3350441 / 1000000
def hpNegT9 : ℚ := 3351491 / 1000000
def hpNegT10 : ℚ := 3350563 / 1000000

theorem hp_neg_t8_pos : (0 : ℚ) < hpNegT8 := by
  norm_num [hpNegT8]

theorem hp_neg_t9_pos : (0 : ℚ) < hpNegT9 := by
  norm_num [hpNegT9]

theorem hp_neg_t10_pos : (0 : ℚ) < hpNegT10 := by
  norm_num [hpNegT10]

theorem hp_neg_t8_le_t9 : hpNegT8 ≤ hpNegT9 := by
  norm_num [hpNegT8, hpNegT9]

theorem hp_neg_t10_le_t9 : hpNegT10 ≤ hpNegT9 := by
  norm_num [hpNegT10, hpNegT9]

/-- The lower atanh-series value at 29 is above the largest tangent bound.
This is a kernel-checked rational calculation followed by the proved
`logPolynomial_le_log` enclosure, so it does not use a floating-point fact.
-/
theorem hp_neg_t8_lt_log29 :
    (hpNegT8 : ℝ) < Real.log 29 := by
  have hlog := logPolynomial_le_log (q := (29 : ℚ)) (by norm_num) 40
  have hrat : hpNegT8 < logPolynomial (29 : ℚ) 40 := by
    norm_num [hpNegT8, logPolynomial, logCoordinate]
  exact lt_of_lt_of_le (by exact_mod_cast hrat) hlog

theorem hp_neg_t9_lt_log29_series :
    (hpNegT9 : ℝ) < Real.log 29 := by
  have hlog := logPolynomial_le_log (q := (29 : ℚ)) (by norm_num) 40
  have hrat : hpNegT9 < logPolynomial (29 : ℚ) 40 := by
    norm_num [hpNegT9, logPolynomial, logCoordinate]
  exact lt_of_lt_of_le (by exact_mod_cast hrat) hlog

theorem hp_neg_t9_lt_log29 :
    (hpNegT9 : ℝ) < Real.log 29 := by
  exact hp_neg_t9_lt_log29_series

theorem hp_neg_t10_lt_log29 :
    (hpNegT10 : ℝ) < Real.log 29 := by
  have hle : (hpNegT10 : ℝ) ≤ (hpNegT9 : ℝ) := by
    norm_num [hpNegT10, hpNegT9]
  exact lt_of_le_of_lt hle hp_neg_t9_lt_log29

/-- The finite q-indexed tangent table. -/
def hpNegT (q : ℕ) : ℚ :=
  if q = 8 then hpNegT8 else if q = 9 then hpNegT9 else hpNegT10

theorem hp_neg_t_eq_cases {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    hpNegT q = hpNegT8 ∨ hpNegT q = hpNegT9 ∨ hpNegT q = hpNegT10 := by
  rcases hq with rfl | rfl | rfl <;> simp [hpNegT]

theorem hp_neg_t_lt_log29 {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    (hpNegT q : ℝ) < Real.log 29 := by
  rcases hq with rfl | rfl | rfl
  · simpa [hpNegT] using hp_neg_t8_lt_log29
  · simpa [hpNegT] using hp_neg_t9_lt_log29
  · simpa [hpNegT] using hp_neg_t10_lt_log29

/-! The polynomial certificate for the concavity window.  This is the exact
polynomial in the denominator identity of v13 `hp-tail.tex:343-355`; the
chosen rational height is `1/5`. -/

def hpNegBottomPolynomial (x : ℚ) : ℚ :=
  x ^ 3 - 4 * x ^ 2 + (72 / 25) * x + 4 / 25

theorem hp_neg_bottom_polynomial_at_right :
    0 < hpNegBottomPolynomial (61 / 60 : ℚ) := by
  norm_num [hpNegBottomPolynomial]

theorem hp_neg_bottom_polynomial_at_left :
    0 < hpNegBottomPolynomial (-(1 / 60 : ℚ)) := by
  norm_num [hpNegBottomPolynomial]

theorem hp_neg_bottom_window_endpoint :
    (-(1 / 60 : ℚ)) < (61 / 60 : ℚ) := by
  norm_num

/-- The concrete B sequence used by the contour branch.  In particular, this
is not an arbitrary sequence: it is the polynomial `B_n` from
`hp-tail.tex:24-27` and `ResidueTailAlgebra.hpBpoly`. -/
def hpBseq (n : ℕ) (z : ℚ) : ℝ :=
  ((Polynomial.eval z (hpBpoly n) : ℚ) : ℝ)

/-- The concrete C sequence paired with `hpBseq` in the v13 contour formula. -/
def hpCseq (n : ℕ) (z : ℚ) : ℝ :=
  ((Polynomial.eval z (hpCpoly n) : ℚ) : ℝ)

theorem hpBseq_eq_hpBSequence : hpBseq = hpBSequence := by
  funext n z
  rfl

theorem hp_neg_rectangle_certificate_of_bound {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hbound : NegativeContour.NegContourB hpBSequence q) :
    Nonempty (NegativeContour.NegContourRectangleCertificate hpBSequence q) := by
  refine ⟨
    { rectangle := rationalBetaRectangle
      rectangle_eq := fun n => rfl
      q_mem := ?_
      contour_bound := hbound }⟩
  simp [negativeContourBases, hq]

/-- The phase used in v13 `F_n^+`, `hp-tail.tex:258-266`. -/
def hpNegLambda (q : ℕ) : ℂ :=
  -((Real.log (q : ℝ)) : ℂ) + (Real.pi : ℂ) * Complex.I

/-- The rational-height rectangle, written as a set so that side estimates can
be stated without committing to a particular boundary parametrisation. -/
def hpRectLower (n : ℕ) (h : ℝ) : ℂ :=
  ⟨-1 / 2, -((n : ℝ) * h)⟩

def hpRectUpper (n : ℕ) (h : ℝ) : ℂ :=
  ⟨(n : ℝ) + 1 / 2, (n : ℝ) * h⟩

/-- The contour estimate is taken on the four-sided boundary, which excludes
the poles in the rectangle interior. -/
def hpNegBorder (n : ℕ) : Set ℂ :=
  RectangleBorder (hpRectLower n (1 / 5 : ℝ)) (hpRectUpper n (1 / 5 : ℝ))

/-- The four component sets of `hpNegBorder`.  Keeping these components
separate mirrors the four boundary estimates in v13 `hp-tail.tex:319-371`;
the side proofs can therefore be developed independently before their union
is assembled. -/
def hpNegBottomSide (n : ℕ) : Set ℂ :=
  {w | (hpRectLower n (1 / 5 : ℝ)).re ≤ w.re ∧
    w.re ≤ (hpRectUpper n (1 / 5 : ℝ)).re ∧
    w.im = (hpRectLower n (1 / 5 : ℝ)).im}

def hpNegTopSide (n : ℕ) : Set ℂ :=
  {w | (hpRectLower n (1 / 5 : ℝ)).re ≤ w.re ∧
    w.re ≤ (hpRectUpper n (1 / 5 : ℝ)).re ∧
    w.im = (hpRectUpper n (1 / 5 : ℝ)).im}

def hpNegLeftSide (n : ℕ) : Set ℂ :=
  {w | w.re = (hpRectLower n (1 / 5 : ℝ)).re ∧
    (hpRectLower n (1 / 5 : ℝ)).im ≤ w.im ∧
    w.im ≤ (hpRectUpper n (1 / 5 : ℝ)).im}

def hpNegRightSide (n : ℕ) : Set ℂ :=
  {w | w.re = (hpRectUpper n (1 / 5 : ℝ)).re ∧
    (hpRectLower n (1 / 5 : ℝ)).im ≤ w.im ∧
    w.im ≤ (hpRectUpper n (1 / 5 : ℝ)).im}

theorem hpNegBorder_eq_union_sides (n : ℕ) :
    hpNegBorder n =
      hpNegBottomSide n ∪ hpNegLeftSide n ∪
        hpNegTopSide n ∪ hpNegRightSide n := by
  ext w
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn : (-1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  simp only [hpNegBorder, RectangleBorder, hpNegBottomSide, hpNegLeftSide,
    hpNegTopSide, hpNegRightSide, hpRectLower, hpRectUpper,
    Complex.mem_reProdIm, Set.mem_setOf_eq, Set.mem_union]
  rw [Set.uIcc_of_le hn]
  simp
  aesop

/-- The v13 product in the contour integrand, `hp-tail.tex:14-18`. -/
def hpNegPhi (n : ℕ) (w : ℂ) : ℂ :=
  (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      (w - (r : ℂ))) /
    ∏ j ∈ Finset.range (n + 1), (w - (j : ℂ)) ^ 2

/-- The logarithmic boundary quantity appearing in the fixed-height estimate,
`hp-tail.tex:319-371`. -/
def hpNegBoundaryLog (q n : ℕ) (w : ℂ) : ℝ :=
  Real.log ‖hpNegPhi n w * Complex.exp (hpNegLambda q * w)‖

def HpNegBorderBound (q : ℕ) : Prop :=
  ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegBorder n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- A typed side certificate.  `bound` is the analytic obligation proved by
the reflection, right-side product, valley sum, and tangent lemmas.  The
finite fields below are all discharged in this file; no arbitrary `B` enters
the statement. -/
structure HpNegBoundaryCertificate (q : ℕ) where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  height : hpNegHeight = (1 / 5 : ℚ)
  tangent_lt_log29 : (hpNegT q : ℝ) < Real.log 29
  n0 : ℕ
  n0_spec : 30 ≤ n0
  exponent : ℕ
  exponent_spec : exponent = 18
  bound : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegBorder n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (exponent : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- The finite fields of a boundary certificate can be filled for every
exceptional q once the four analytic side lemmas are supplied.  This helper
is intentionally an explicit constructor rather than a `sorry` theorem. -/
def hpNegBoundaryCertificateOfBound {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hbound : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegBorder n,
      hpNegBoundaryLog q n w ≤
        (n : ℝ) * (hpNegT q : ℝ) +
          (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))) :
    HpNegBoundaryCertificate q := by
  refine
    { q_spec := hq
      height := hp_neg_height_spec
      tangent_lt_log29 := hp_neg_t_lt_log29 hq
      n0 := 30
      n0_spec := by norm_num
      exponent := 18
      exponent_spec := by rfl
      bound := ?_ }
  intro n hn w hw
  simpa using hbound n hn w hw

/-- The exact coefficient target consumed by the final contour glue.  The
polynomial and `(n+1)^k` factor are fixed here, correcting the old arbitrary-B
and `n^k` interfaces.  This is the target from v13 `hp-tail.tex:403-409`. -/
def HpNegContourB (q : ℕ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
    |hpBseq n (-((1 : ℚ) / (q : ℚ)))| ≤
      C * ((n + 1 : ℕ) : ℝ) ^ k * (29 : ℝ) ^ n

theorem hp_neg_contour_target_shape (q : ℕ) :
    HpNegContourB q ↔
      ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
        |hpBseq n (-((1 : ℚ) / (q : ℚ)))| ≤
          C * ((n + 1 : ℕ) : ℝ) ^ k * (29 : ℝ) ^ n := by
  rfl

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_t8_lt_log29
#print axioms Li2Lean.B4.NegContour.hp_neg_t_lt_log29
#print axioms Li2Lean.B4.NegContour.hpNegBoundaryCertificateOfBound
