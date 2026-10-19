/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary
import Li2Lean.B4.ContourPNT
import Li2Lean.B4.ResidueCertificateAllN_M0c

/-!
Construction-bound exceptional negative contour producers for the three
exceptional bases in v13 hp-tail.tex:256-410.  The four-side analytic
estimates remain named q-specific inputs.  The coefficient estimate below is
for the concrete Hermite-Pade polynomial hpBSequence only.

The finite-index absorption and exponent k = 19 implement the final
normalization in v13 hp-tail.tex:403-409.  The residue input is the
construction-bound all-n M0 certificate from hp-tail.tex:12-27.
-/

open Complex Real
open scoped BigOperators Interval

namespace Li2Lean.B4.NegativeContour

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.NegContour
open Li2Lean.B4.ResidueTailBridge

def hpNegK0 (q : ℕ) : ℝ :=
  (1 + Real.log (q : ℝ) / Real.pi) * (1 / (2 * Real.pi)) * 3 * Real.exp 18

def hpNegFiniteSum (q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range 30,
    |hpBSequence m (-((1 : ℚ) / (q : ℚ)))|

/- The unresolved analytic work is an explicit producer contract. -/
structure HpNegContourProducerInput (q : ℕ) : Prop where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  /-- P1, v13 hp-tail.tex:256-310, for the actual branch kernel. -/
  residue : ∀ n : ℕ, 0 < n →
    HpTailResidueRectangleCertificate q n (1 / 5 : ℝ)
  /-- P2, v13 hp-tail.tex:319-404, on the rectangle border only. -/
  boundary : HpNegBorderBound q
  /-- Quantitative P1 plus P2 output for the actual branch value. -/
  branch_bound : ∀ n : ℕ, 30 ≤ n →
    ‖hpTailBranchValuePlus q n‖ ≤
      (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
        (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)

/- M0 is unconditional and construction-bound. -/
theorem residue_certificate_all (n : ℕ) : ExplicitResidueCertificate n :=
  explicitResidueCertificate_all n

/- B plus (log q/pi) C extraction from v13 hp-tail.tex:405-410. -/
theorem hpBSequence_eq_branch_re_im (q n : ℕ) :
    hpBSequence n (-((1 : ℚ) / (q : ℚ))) =
      (hpTailBranchValuePlus q n).re +
        Real.log (q : ℝ) / Real.pi * (hpTailBranchValuePlus q n).im := by
  unfold hpBSequence hpTailBranchValuePlus
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im]
  field_simp [Real.pi_ne_zero]
  ring

theorem abs_hpBSequence_le_branch_norm {q n : ℕ}
    (hq : 1 ≤ q) :
    |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤
      (1 + Real.log (q : ℝ) / Real.pi) *
        ‖hpTailBranchValuePlus q n‖ := by
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hc : 0 ≤ Real.log (q : ℝ) / Real.pi :=
    div_nonneg hlog Real.pi_pos.le
  rw [hpBSequence_eq_branch_re_im]
  calc
    |(hpTailBranchValuePlus q n).re +
        Real.log (q : ℝ) / Real.pi *
          (hpTailBranchValuePlus q n).im| ≤
        |(hpTailBranchValuePlus q n).re| +
          Real.log (q : ℝ) / Real.pi *
            |(hpTailBranchValuePlus q n).im| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (1 + Real.log (q : ℝ) / Real.pi) *
        ‖hpTailBranchValuePlus q n‖ := by
      have hre := Complex.abs_re_le_norm (hpTailBranchValuePlus q n)
      have him := Complex.abs_im_le_norm (hpTailBranchValuePlus q n)
      nlinarith

theorem hpNeg_large_B_bound {q : ℕ}
    (producer : HpNegContourProducerInput q) (n : ℕ) (hn : 30 ≤ n) :
    |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤
      hpNegK0 q * ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by
  have hq1 : 1 ≤ q := by
    rcases producer.q_spec with rfl | rfl | rfl <;> norm_num
  have hB := abs_hpBSequence_le_branch_norm (q := q) (n := n) hq1
  have hF := producer.branch_bound n hn
  have hcoef : 0 ≤ 1 + Real.log (q : ℝ) / Real.pi := by
    have hlog : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hq1)
    positivity
  have hmul := mul_le_mul_of_nonneg_left hF hcoef
  calc
    |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤
        (1 + Real.log (q : ℝ) / Real.pi) *
          ‖hpTailBranchValuePlus q n‖ := hB
    _ ≤ (1 + Real.log (q : ℝ) / Real.pi) *
        ((1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)) := hmul
    _ = hpNegK0 q * ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by
      simp only [hpNegK0]
      ring

theorem hpNegK0_nonneg {q : ℕ} (hq : 1 ≤ q) : 0 ≤ hpNegK0 q := by
  unfold hpNegK0
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  positivity

theorem hpNeg_factor_ge_one (n : ℕ) :
    1 ≤ ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by
  have hx : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hxpow : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 19 :=
    one_le_pow₀ hx
  have hy : (1 : ℝ) ≤ (29 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le hxpow hy

theorem negContourB_of_producers {q : ℕ}
    (producer : HpNegContourProducerInput q) :
    NegContourB hpBSequence q := by
  let K0 : ℝ := hpNegK0 q
  let S : ℝ := hpNegFiniteSum q
  refine ⟨K0 + S, 19, ?_⟩
  have hq1 : 1 ≤ q := by
    rcases producer.q_spec with rfl | rfl | rfl <;> norm_num
  have hK0 : 0 ≤ K0 := by
    exact hpNegK0_nonneg hq1
  have hS : 0 ≤ S := by
    dsimp [S, hpNegFiniteSum]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  intro n
  have hpow : (1 : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n :=
    hpNeg_factor_ge_one n
  by_cases hn : 30 ≤ n
  · have hlarge := hpNeg_large_B_bound producer n hn
    calc
      |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤
          K0 * ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by
            simpa [K0] using hlarge
      _ ≤ (K0 + S) * ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by
        have hfactor : 0 ≤
            ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by positivity
        nlinarith
  · have hnlt : n < 30 := by omega
    have hle : |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤ S := by
      dsimp [S, hpNegFiniteSum]
      apply Finset.single_le_sum (s := Finset.range 30)
        (f := fun m => |hpBSequence m (-((1 : ℚ) / (q : ℚ)))|)
      · intro m hm
        exact abs_nonneg _
      · exact Finset.mem_range.mpr hnlt
    have hSbound : S ≤ S *
        (((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n) := by
      nlinarith
    calc
      |hpBSequence n (-((1 : ℚ) / (q : ℚ)))| ≤ S := hle
      _ ≤ S * (((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n) := hSbound
      _ ≤ (K0 + S) * (((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n) := by
        have hfactor : 0 ≤
            ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by positivity
        nlinarith
      _ = (K0 + S) * ((n + 1 : ℕ) : ℝ) ^ 19 * (29 : ℝ) ^ n := by ring

theorem negativeContour_rectangle_q8_of_producers
    (producer : HpNegContourProducerInput 8) :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) := by
  refine ⟨
    { rectangle := rationalBetaRectangle
      rectangle_eq := fun _ => rfl
      q_mem := by simp [negativeContourBases]
      contour_bound := negContourB_of_producers producer }⟩

theorem negativeContour_rectangle_q9_of_producers
    (producer : HpNegContourProducerInput 9) :
    Nonempty (NegContourRectangleCertificate hpBSequence 9) := by
  refine ⟨
    { rectangle := rationalBetaRectangle
      rectangle_eq := fun _ => rfl
      q_mem := by simp [negativeContourBases]
      contour_bound := negContourB_of_producers producer }⟩

theorem negativeContour_rectangle_q10_of_producers
    (producer : HpNegContourProducerInput 10) :
    Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  refine ⟨
    { rectangle := rationalBetaRectangle
      rectangle_eq := fun _ => rfl
      q_mem := by simp [negativeContourBases]
      contour_bound := negContourB_of_producers producer }⟩

theorem negativeContourB_q8_of_producers
    (producer : HpNegContourProducerInput 8) : concreteNegContourB 8 :=
  negContourB_of_producers producer

theorem negativeContourB_q9_of_producers
    (producer : HpNegContourProducerInput 9) : concreteNegContourB 9 :=
  negContourB_of_producers producer

theorem negativeContourB_q10_of_producers
    (producer : HpNegContourProducerInput 10) : concreteNegContourB 10 :=
  negContourB_of_producers producer

end

end Li2Lean.B4.NegativeContour

#print axioms Li2Lean.B4.NegativeContour.negContourB_of_producers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q8_of_producers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q9_of_producers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q10_of_producers
