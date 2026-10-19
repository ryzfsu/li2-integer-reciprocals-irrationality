/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseCellShift
import Li2Lean.P0.PositiveBaseContour
import Li2Lean.P0.Contour

open MeasureTheory

namespace Li2Lean.P0.PositiveBase

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Config

theorem qContourQValue_eq_mul_contourQValue {m : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) :
    qContourQValue q S h4 hSI R hR Z =
      contourQValue S h4 hSI R hR Z *
        (Real.log (q : ℝ) / ell) ^ S.card *
        Real.exp (logShift (q : ℤ) *
          ((∑ a ∈ S, (a : ℝ)) +
            (∑ i : Fin (m - S.card), (Z i).re) -
              ∑ i : Fin m, (R i : ℝ))) := by
  classical
  have hqpos : 0 < q := by omega
  have hell : ell ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hP :
      (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) =
        (∏ a ∈ S, ell * UReal (m / 2) a) *
          (Real.log (q : ℝ) / ell) ^ S.card *
          Real.exp (logShift (q : ℤ) * (∑ a ∈ S, (a : ℝ))) := by
    calc
      (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) =
          ∏ a ∈ S, ((ell * UReal (m / 2) a) *
            ((Real.log (q : ℝ) / ell) *
              Real.exp (logShift (q : ℤ) * (a : ℝ)))) := by
        apply Finset.prod_congr rfl
        intro a ha
        rw [qUReal_eq q (m / 2) a hqpos]
        field_simp [hell]
      _ = (∏ a ∈ S, ell * UReal (m / 2) a) *
          (∏ a ∈ S, (Real.log (q : ℝ) / ell) *
            Real.exp (logShift (q : ℤ) * (a : ℝ))) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ a ∈ S, ell * UReal (m / 2) a) *
          (Real.log (q : ℝ) / ell) ^ S.card *
          Real.exp (logShift (q : ℤ) * (∑ a ∈ S, (a : ℝ))) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        rw [← Real.exp_sum]
        have hsum :
            Real.exp (∑ a ∈ S, logShift (q : ℤ) * (a : ℝ)) =
              Real.exp (logShift (q : ℤ) * (∑ a ∈ S, (a : ℝ))) := by
          congr 1
          rw [← Finset.mul_sum]
        rw [hsum]
        ring
  have hF :
      (∏ i : Fin m, qFrequencyWeightReal q (m / 2) (R i)) =
        (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
          Real.exp (-(logShift (q : ℤ) *
            (∑ i : Fin m, (R i : ℝ)))) := by
    calc
      (∏ i : Fin m, qFrequencyWeightReal q (m / 2) (R i)) =
          ∏ i : Fin m, (frequencyWeightReal (m / 2) (R i) *
            Real.exp (-(logShift (q : ℤ) * (R i : ℝ)))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact qFrequencyWeightReal_eq q (m / 2) (R i) hqpos
      _ = (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
          Real.exp (-(logShift (q : ℤ) *
            (∑ i : Fin m, (R i : ℝ)))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hN :
      (∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖) =
        (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
          Real.exp (logShift (q : ℤ) *
            (∑ i : Fin (m - S.card), (Z i).re)) := by
    calc
      (∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖) =
          ∏ i : Fin (m - S.card),
            (‖p0Entire (m / 2) (Z i)‖ *
              Real.exp (logShift (q : ℤ) * (Z i).re)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact norm_p0EntireQ_eq (q : ℤ) (by omega) (m / 2) (Z i)
      _ = (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
          Real.exp (logShift (q : ℤ) *
            (∑ i : Fin (m - S.card), (Z i).re)) := by
        simp only [Finset.prod_mul_distrib]
        rw [← Real.exp_sum, ← Finset.mul_sum]
  have hexp :
      Real.exp (logShift (q : ℤ) * (∑ a ∈ S, (a : ℝ))) *
          Real.exp (-(logShift (q : ℤ) * (∑ i : Fin m, (R i : ℝ)))) *
          Real.exp (logShift (q : ℤ) *
            (∑ i : Fin (m - S.card), (Z i).re)) =
        Real.exp (logShift (q : ℤ) *
          ((∑ a ∈ S, (a : ℝ)) +
            (∑ i : Fin (m - S.card), (Z i).re) -
              ∑ i : Fin m, (R i : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [qContourQValue, contourQValue]
  rw [hP, hF, hN]
  calc
    _ =
        ((∏ a ∈ S, ell * UReal (m / 2) a) *
          (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
          (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
          ‖(contourQMinors S h4 hSI R hR Z).1 *
            (contourQMinors S h4 hSI R hR Z).2.1 *
            (contourQMinors S h4 hSI R hR Z).2.2‖) *
          (Real.log (q : ℝ) / ell) ^ S.card *
          (Real.exp (logShift (q : ℤ) * (∑ a ∈ S, (a : ℝ))) *
            Real.exp (-(logShift (q : ℤ) *
              (∑ i : Fin m, (R i : ℝ)))) *
            Real.exp (logShift (q : ℤ) *
              (∑ i : Fin (m - S.card), (Z i).re))) := by ring
    _ = _ := by rw [hexp]

end

end Li2Lean.P0.PositiveBase
