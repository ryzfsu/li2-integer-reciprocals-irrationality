/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseEnvelopeCore

/-!
# q-dependent cell weights

The positive-base cell route uses the q-pinned row factor `log q`.  This file
keeps the corrected weight definition and its elementary one-body
factorizations separate from the later contour and cell comparison proofs.
-/

open MeasureTheory

namespace Li2Lean.P0.PositiveBase

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Config

/-! ## Corrected q-weight -/

def qContourQValueFixed {m : ℕ} (q : ℕ) (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) : ℝ :=
  let minors := contourQMinors S h4 hSI R hR Z
  (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) *
    (∏ i : Fin m, qFrequencyWeightReal q (m / 2) (R i)) *
    (∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖) *
    ‖minors.1 * minors.2.1 * minors.2.2‖

private theorem qPinned_subset_Iset (C : FiniteConfiguration) :
    C.pinned ⊆ Iset C.m := by
  rw [Iset_eq_paper_interval C.m C.four_dvd_m]
  simpa [pinnedUniverse] using C.pinned_subset

private theorem qContour_count_eq (C : FiniteConfiguration) :
    C.contourCount = C.m - C.pinned.card := by
  have h := C.mass_balance
  omega

private noncomputable def qScaledContourPoint (C : FiniteConfiguration)
    (i : Fin C.contourCount) : ℂ :=
  Complex.ofReal (C.m : ℝ) * C.contour i

def qLiteralConfigQWeightFixed (q : ℕ) (C : FiniteConfiguration) : ℝ :=
  qContourQValueFixed q C.pinned C.four_dvd_m (qPinned_subset_Iset C)
    (fun i : Fin C.m =>
      orderedElem C.frequency (Fin.cast C.frequency_card.symm i))
    (by
      intro i j hij
      exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij)
    (fun i : Fin (C.m - C.pinned.card) =>
      qScaledContourPoint C (Fin.cast (qContour_count_eq C).symm i))

/-! ## One-body factorizations -/

theorem qUReal_eq (q g a : ℕ) (hq : 0 < q) :
    qUReal q g a = UReal g a * Real.exp (logShift (q : ℤ) * a) := by
  have hq2 : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  unfold qUReal UReal logShift
  rw [show Real.exp (Real.log (((q : ℤ) : ℝ) / 2) * a) =
      ((q : ℝ) / 2) ^ a by
    rw [mul_comm, ← Real.log_rpow (by push_cast; exact hq2),
      Real.exp_log (by push_cast; positivity)]
    push_cast
    rw [Real.rpow_natCast]]
  rw [div_pow]
  field_simp

theorem qFrequencyWeightReal_eq (q g r : ℕ) (hq : 0 < q) :
    qFrequencyWeightReal q g r =
      frequencyWeightReal g r * Real.exp (-(logShift (q : ℤ) * r)) := by
  have hq2 : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  unfold qFrequencyWeightReal frequencyWeightReal logShift
  rw [show Real.exp (-(Real.log (((q : ℤ) : ℝ) / 2) * r)) =
      ((2 : ℝ) / q) ^ r by
    have hbase : Real.exp (-Real.log (((q : ℤ) : ℝ) / 2)) =
        (2 : ℝ) / q := by
      have hcast : (((q : ℤ) : ℝ) / 2) = (q : ℝ) / 2 := by norm_num
      rw [hcast, Real.exp_neg, Real.exp_log hq2]
      push_cast
      field_simp
    rw [show -(Real.log (((q : ℤ) : ℝ) / 2) * r) =
        (r : ℝ) * (-Real.log (((q : ℤ) : ℝ) / 2)) by ring]
    rw [Real.exp_nat_mul, hbase]]
  rw [div_pow]
  field_simp

end

end Li2Lean.P0.PositiveBase

#print axioms Li2Lean.P0.PositiveBase.qUReal_eq
#print axioms Li2Lean.P0.PositiveBase.qFrequencyWeightReal_eq
