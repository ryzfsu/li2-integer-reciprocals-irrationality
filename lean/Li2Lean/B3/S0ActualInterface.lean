/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Actual signed-V S0 consumer for the v13 construction.

The definitions in `V.Literal` are the four-piece contour and the exact
integrand from `v-analytic.tex:85-123`.  This file only packages the two
remaining analytic inputs for that fixed construction; it does not
re-quantify an arbitrary determinant or an arbitrary integrand.
-/

import Li2Lean.B3.ProducerInterfaces
import Li2Lean.B3.ReferencePackage
import Li2Lean.V.VLiteralNestedBridge
import Li2Lean.V.S0Interface
import Li2Lean.P0.P0CoefficientEvaluationBridge

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory

/-! ## The actual value and its real-polynomial presentation

The source is v13 `v-arithmetic.tex:13-35`, and the contour presentation is
v13 `v-analytic.tex:106-123`. -/

def vContourActualGValue (q n : ℕ) : ℂ :=
  V.Literal.vContourGValue q n

theorem vContourActualGValue_eq_literal (q n : ℕ) :
    vContourActualGValue q n = V.Literal.vContourGValue q n := rfl

/- The real form is the same value used by the top-down B3 interface. -/
theorem vContourActualGValue_eq_vRealPoly (q n : ℕ) :
    vContourActualGValue q n =
      (((vRealPoly q (4 * n)).eval
          (li2InvValue (-(q : ℤ))) : ℝ) : ℂ) := by
  unfold vContourActualGValue V.Literal.vContourGValue
  rw [vRealPoly_four_mul, Polynomial.eval_map]
  conv_rhs => rw [Polynomial.eval₂_eq_eval_map]
  exact (Li2Lean.P0.ofReal_eval_map_rat
    (V.vPolynomial n (-(q : ℤ)))
    (li2InvValue (-(q : ℤ)))).symm

/-! ## The fixed v13 analytic obligation

The two fields below are concrete statements about the objects just defined.
The first is the determinant/triple-integral identity in
`v-analytic.tex:106-145`; the second is its absolute-value estimate in
`:106-123,530-610`. -/

structure VContourS0Data (q n : ℕ) (Tq phiMax : ℝ) : Prop where
  q_ge_two : 2 ≤ q
  determinant_identity :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        V.Literal.vContourTripleIntegral q n
  triple_norm_bound :
    ‖V.Literal.vContourTripleIntegral q n‖ ≤
      Tq ^ (4 * n) * |phiMax|

def vContourS0MagnitudeGoal (q n : ℕ) (Tq phiMax : ℝ) : Prop :=
  s0MultiplicativeBound q (4 * n) (5 * n)
    (vContourActualGValue q n) Tq phiMax

lemma s0Exponent_four_mul (n : ℕ) :
    s0Exponent (4 * n) = 24 * n ^ 2 - 4 * n := by
  unfold s0Exponent
  have h : 3 * (4 * n) ^ 2 = 2 * (24 * n ^ 2) := by ring
  rw [h]
  simp

theorem vContourS0Magnitude_of_data {q n : ℕ} {Tq phiMax : ℝ}
    (D : VContourS0Data q n Tq phiMax) :
    vContourS0MagnitudeGoal q n Tq phiMax := by
  unfold vContourS0MagnitudeGoal s0MultiplicativeBound
    s0MagnitudeRhs
  rw [D.determinant_identity, norm_mul]
  have hqR : 0 ≤ (q : ℝ) := by positivity
  have hpref :
      ‖V.Literal.vContourPrefactor q n‖ =
        (q : ℝ) ^ s0Exponent (4 * n) /
          (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
            ((Nat.factorial (5 * n) : ℕ) : ℝ)) := by
    rw [s0Exponent_four_mul]
    simp [V.Literal.vContourPrefactor, norm_div, norm_mul, norm_pow,
      Complex.norm_natCast, abs_of_nonneg hqR]
  have hfac : 0 ≤
      (q : ℝ) ^ s0Exponent (4 * n) /
        (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
          ((Nat.factorial (5 * n) : ℕ) : ℝ)) := by positivity
  have hbound := mul_le_mul_of_nonneg_left D.triple_norm_bound hfac
  rw [hpref]
  calc
    _ ≤ (q : ℝ) ^ s0Exponent (4 * n) /
        (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
          ((Nat.factorial (5 * n) : ℕ) : ℝ)) *
        (Tq ^ (4 * n) * |phiMax|) := hbound
    _ = (q : ℝ) ^ s0Exponent (4 * n) /
        (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
          ((Nat.factorial (5 * n) : ℕ) : ℝ)) *
        Tq ^ (4 * n) * |phiMax| := by ring

/-! The frozen base regression is the same construction at `q=2`. -/
theorem vContourS0Magnitude_of_data_q2 {n : ℕ} {Tq phiMax : ℝ}
    (D : VContourS0Data 2 n Tq phiMax) :
    vContourS0MagnitudeGoal 2 n Tq phiMax :=
  vContourS0Magnitude_of_data D

/-! ## Guarded logarithmic transfer to the B3 producer

The v13 maximum point is one fixed value for a base.  It is not allowed to
depend on `n`: otherwise the triple norm field can be satisfied by choosing a
new value after seeing the integral.  The transfer field below is the explicit
bound for that fixed point from `v-analytic.tex:530-558`, before the S0
prefactor and the `Tq^(4*n)` path factor are reassembled. -/

def s0TransferPrefactor (q n : ℕ) : ℝ :=
  (q : ℝ) ^ s0Exponent (4 * n) /
    (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
      ((Nat.factorial (5 * n) : ℕ) : ℝ))

def s0TransferPhiBudget (q : ℕ) (alpha sigma Tq phiMax : ℝ) (n : ℕ) : ℝ :=
  -alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
    (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
      Real.log ((4 * n : ℕ) : ℝ) +
    3 * sigma *
      (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
    (2 * denominatorTransferCost q + 7 + 130) +
      ((4 * n : ℕ) : ℝ) -
    Real.log (s0TransferPrefactor q n * Tq ^ (4 * n))

structure VContourS0TransferData (q : ℕ) (alpha sigma : ℝ) : Type where
  q_ge_two : 2 ≤ q
  q_le_seven : q ≤ 7
  Tq : ℝ
  Tq_pos : 0 < Tq
  phiMax : ℝ
  phiMax_pos : 0 < phiMax
  s0_data : ∀ n : ℕ, VContourS0Data q n Tq phiMax
  /-- The v13 estimate for the fixed maximum point, before the prefactor. -/
  phi_log_bound : ∀ n : ℕ, 64 ≤ 4 * n →
    Real.log |phiMax| ≤ s0TransferPhiBudget q alpha sigma Tq phiMax n

theorem s0TransferPrefactor_pos {q n : ℕ} (hq : 2 ≤ q) :
    0 < s0TransferPrefactor q n := by
  unfold s0TransferPrefactor
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  positivity

theorem s0MagnitudeRhs_eq_transfer
    {q n : ℕ} {Tq phiMax : ℝ} :
    s0MagnitudeRhs q (4 * n) (5 * n) Tq phiMax =
      s0TransferPrefactor q n * Tq ^ (4 * n) * |phiMax| := by
  rfl

theorem s0_log_rhs_le_of_transfer
    {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0TransferData q alpha sigma)
    {n : ℕ} (hn : 64 ≤ 4 * n) :
    Real.log (s0MagnitudeRhs q (4 * n) (5 * n) H.Tq H.phiMax) ≤
      -alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigma *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) := by
  have hpref : 0 < s0TransferPrefactor q n :=
    s0TransferPrefactor_pos H.q_ge_two
  have hpow : 0 < H.Tq ^ (4 * n) := pow_pos H.Tq_pos _
  have hphi : 0 < |H.phiMax| := abs_pos.mpr H.phiMax_pos.ne'
  have hfirst : s0TransferPrefactor q n * H.Tq ^ (4 * n) ≠ 0 :=
    (mul_pos hpref hpow).ne'
  rw [s0MagnitudeRhs_eq_transfer]
  rw [Real.log_mul hfirst hphi.ne']
  have hbound := H.phi_log_bound n hn
  unfold s0TransferPhiBudget at hbound
  linarith

theorem vRawPrebound_of_s0_transfer {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0TransferData q alpha sigma) :
    VRawPrebound q alpha sigma := by
  intro n hn hreal
  have D := H.s0_data n
  have hcomplex : vContourActualGValue q n ≠ 0 := by
    rw [vContourActualGValue_eq_vRealPoly]
    exact Complex.ofReal_ne_zero.mpr hreal
  have hRhs : 0 < s0MagnitudeRhs q (4 * n) (5 * n)
      H.Tq H.phiMax := by
    rw [s0MagnitudeRhs_eq_transfer]
    exact mul_pos (mul_pos (s0TransferPrefactor_pos H.q_ge_two)
      (pow_pos H.Tq_pos _)) (abs_pos.mpr H.phiMax_pos.ne')
  have hmag := vContourS0Magnitude_of_data D
  have hlog := Real.log_le_log (norm_pos_iff.mpr hcomplex) hmag
  rw [vContourActualGValue_eq_vRealPoly] at hlog
  rw [Complex.norm_real, Real.norm_eq_abs] at hlog
  exact hlog.trans (s0_log_rhs_le_of_transfer H hn)

/- The q=2 specialization keeps the frozen signed base in the same chain. -/
theorem vRawPrebound_of_s0_transfer_q2 {alpha sigma : ℝ}
    (H : VContourS0TransferData 2 alpha sigma) :
    VRawPrebound 2 alpha sigma :=
  vRawPrebound_of_s0_transfer H

theorem vAllMPreboundProducer_of_s0_transfer {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0TransferData q alpha sigma)
    (hσ : ∃ Ax Av Az : ℝ,
      0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧ sigma = sigmaBudget Ax Av Az) :
    VAllMPreboundProducer q alpha sigma :=
  producer_of_rawPrebound H.q_ge_two H.q_le_seven hσ
    (vRawPrebound_of_s0_transfer H)

/-! ## Construction-bound actual transfer carrier

These declarations belong to the actual S0 interface itself, rather than to
the leaf compatibility module. This keeps the dependency direction
`S0TBudgetAssembly -> S0Actual` and avoids the former cycle through
`PreboundLeafInterfaces`. The envelope is the normalized v13 triple
integral (`v-analytic.tex:106-145, 493-631`), with no free replacement value.
-/

noncomputable def v13PhiMaxValue (q : ℕ) (Tq : ℝ) (n : ℕ) : ℝ :=
  ‖V.Literal.vContourTripleIntegral q n‖ / Tq ^ (4 * n)

theorem v13PhiMaxValue_pos {q : ℕ} {Tq : ℝ} (hTq : 0 < Tq)
    (n : ℕ) (htriple : V.Literal.vContourTripleIntegral q n ≠ 0) :
    0 < v13PhiMaxValue q Tq n := by
  unfold v13PhiMaxValue
  exact div_pos (norm_pos_iff.mpr htriple) (pow_pos hTq _)

theorem vContourTripleIntegral_ne_zero_of_s0_data
    {q n : ℕ} {Tq phiMax : ℝ}
    (D : VContourS0Data q n Tq phiMax)
    (hG : vContourActualGValue q n ≠ 0) :
    V.Literal.vContourTripleIntegral q n ≠ 0 := by
  intro htriple
  rw [D.determinant_identity, htriple, mul_zero] at hG
  exact hG rfl

theorem v13PhiMaxValue_pos_of_s0_data
    {q n : ℕ} {Tq phiMax : ℝ}
    (hTq : 0 < Tq)
    (D : VContourS0Data q n Tq phiMax)
    (hG : vContourActualGValue q n ≠ 0) :
    0 < v13PhiMaxValue q Tq n :=
  v13PhiMaxValue_pos hTq n
    (vContourTripleIntegral_ne_zero_of_s0_data D hG)

theorem v13PhiMaxValue_triple_norm {q : ℕ} {Tq : ℝ}
    (hTq : 0 < Tq) (n : ℕ) :
    ‖V.Literal.vContourTripleIntegral q n‖ ≤
      Tq ^ (4 * n) * v13PhiMaxValue q Tq n := by
  unfold v13PhiMaxValue
  have hpow : 0 < Tq ^ (4 * n) := pow_pos hTq _
  calc
    ‖V.Literal.vContourTripleIntegral q n‖ =
        Tq ^ (4 * n) *
          (‖V.Literal.vContourTripleIntegral q n‖ / Tq ^ (4 * n)) := by
      field_simp
    _ ≤ Tq ^ (4 * n) *
          (‖V.Literal.vContourTripleIntegral q n‖ / Tq ^ (4 * n)) := le_rfl

/-! Corrected v13 transfer carrier; its maximum source may vary with n but is
construction-bound and cannot be selected after the target inequality. -/
structure VContourS0TransferDataActual (q : ℕ) (alpha sigma : ℝ) : Type where
  q_ge_two : 2 ≤ q
  q_le_seven : q ≤ 7
  Tq : ℝ
  Tq_pos : 0 < Tq
  s0_data : ∀ n : ℕ,
    VContourS0Data q n Tq (v13PhiMaxValue q Tq n)
  phi_log_bound : ∀ n : ℕ,
    V.Literal.vContourTripleIntegral q n ≠ 0 → 64 ≤ 4 * n →
    Real.log |v13PhiMaxValue q Tq n| ≤
      s0TransferPhiBudget q alpha sigma Tq (v13PhiMaxValue q Tq n) n

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.vContourS0Magnitude_of_data
#print axioms Li2Lean.B3.vContourS0Magnitude_of_data_q2
