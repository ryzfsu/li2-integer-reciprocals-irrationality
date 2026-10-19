/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.OuterMomentPolynomialAdapter
import Li2Lean.V.VLiteralAndreiefActual
import Li2Lean.V.VLiteralPolynomialRows
import Li2Lean.V.VLiteralXStage

namespace Li2Lean.V

noncomputable section

open MeasureTheory Set

theorem vLiteralOuterM0_inl_inr_eq (q n : ℕ) (k : Fin n)
    (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    vLiteralOuterM0 q n (Sum.inl (literalXColumnEquiv n (Sum.inr k))) c =
      Complex.ofReal (vVEntry (vLiteralOuterColumnIndex n c) (1 + k.val)) := by
  let j := vLiteralOuterColumnIndex n c
  have hj : 1 ≤ j := by
    rcases c with c | c <;> simp [j, vLiteralOuterColumnIndex] <;> omega
  simp only [vLiteralOuterM0, literalXStageA0, Equiv.symm_apply_apply,
    vLiteralOuterB0, Literal.vContourUnitIntervalMeasure]
  have hcast : (fun t : ℝ => (t : ℂ) ^ k.val * (t : ℂ) ^ j) =
      (fun t : ℝ => Complex.ofReal (t ^ (k.val + j))) := by
    ext t
    push_cast [pow_add]
    rfl
  rw [hcast]
  have hreal : (∫ t in Set.Icc (0 : ℝ) 1, Complex.ofReal (t ^ (k.val + j))) =
      Complex.ofReal (∫ t in Set.Icc (0 : ℝ) 1, t ^ (k.val + j)) := by
    simpa using (integral_ofReal (𝕜 := ℂ)
      (f := fun t : ℝ => t ^ (k.val + j))
      (μ := Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
  rw [hreal]
  congr 1
  have h_int : ∫ t in Set.Icc (0 : ℝ) 1, t ^ (k.val + j) =
      ((k.val + j + 1 : ℕ) : ℝ)⁻¹ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    simp
  rw [h_int, vVEntry]
  have h_nat : k.val + j + 1 = j + (1 + k.val) := by omega
  rw [h_nat]
  simp [j]

theorem vLiteralOuterM0_inl_inl_eq (q n : ℕ) (hq : 2 ≤ q) (i : Fin (4 * n))
    (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    vLiteralOuterM0 q n (Sum.inl (literalXColumnEquiv n (Sum.inl i))) c =
      Complex.ofReal (vOuterMoment q (2 * n + i.val)
        (vLiteralOuterColumnIndex n c)) := by
  let μ : Measure ℝ := Literal.vContourUnitIntervalMeasure
  letI : SFinite μ := by
    dsimp [μ, Literal.vContourUnitIntervalMeasure]
    infer_instance
  let s : Set ℝ := Icc (0 : ℝ) 1
  let a : ℕ := 2 * n + i.val
  let b : ℕ := vLiteralOuterColumnIndex n c
  let F : ℝ → ℝ → ℝ :=
    fun x t => x ^ a * t ^ b / ((q : ℝ) + x * t)
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hden : ∀ p : ℝ × ℝ, p ∈ s ×ˢ s →
      (q : ℝ) + p.1 * p.2 ≠ 0 := by
    intro p hp
    obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
    have hmul : 0 ≤ p.1 * p.2 := mul_nonneg hx.1 ht.1
    exact ne_of_gt (show (0 : ℝ) < (q : ℝ) + p.1 * p.2 by linarith)
  have hnum : Continuous
      (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b) := by
    fun_prop
  have hdencont : Continuous
      (fun p : ℝ × ℝ => (q : ℝ) + p.1 * p.2) := by
    fun_prop
  have hcont : ContinuousOn
      (Function.uncurry F) (s ×ˢ s) := by
    change ContinuousOn
      (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b /
        ((q : ℝ) + p.1 * p.2)) (s ×ˢ s)
    exact hnum.continuousOn.div hdencont.continuousOn hden
  have hF : Integrable
      (Function.uncurry F) (μ.prod μ) := by
    have hOn : IntegrableOn
        (Function.uncurry F) (s ×ˢ s)
        (volume.prod volume) :=
      hcont.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    have hμ :
        (volume.prod volume).restrict (s ×ˢ s) =
          μ.prod μ := by
      dsimp [μ, Literal.vContourUnitIntervalMeasure, s]
      rw [← Measure.prod_restrict]
    rw [← hμ]
    exact hOn.integrable
  have hpoint (t : ℝ) (ht : t ∈ s) :
      literalXMoment q n i t * (t : ℂ) ^ b =
        Complex.ofReal (∫ x : ℝ, F x t ∂μ) := by
    rw [literalXMoment, ← integral_mul_const]
    have hreal :
        (∫ x : ℝ, Complex.ofReal (F x t) ∂μ) =
          Complex.ofReal (∫ x : ℝ, F x t ∂μ) := by
      simpa using (integral_ofReal (𝕜 := ℂ)
        (f := fun x : ℝ => F x t) (μ := μ))
    rw [← hreal]
    apply integral_congr_ae
    filter_upwards [] with x
    change
      ((x : ℂ) ^ a * literalXKernel q t x) *
          (t : ℂ) ^ b =
        ((F x t : ℝ) : ℂ)
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    simp [literalXKernel, ht']
    dsimp [F]
    push_cast
    ring
  have hswap :
      (∫ t : ℝ, ∫ x : ℝ, F x t ∂μ ∂μ) =
        ∫ x : ℝ, ∫ t : ℝ, F x t ∂μ ∂μ := by
    exact (integral_integral_swap hF).symm
  change
    (∫ t : ℝ,
      literalXStageA0 q n
          (literalXColumnEquiv n (Sum.inl i)) t *
        vLiteralOuterB0 n t c ∂μ) = _
  simp only [literalXStageA0, Equiv.symm_apply_apply, vLiteralOuterB0]
  change
    (∫ t : ℝ,
      literalXMoment q n i t * (t : ℂ) ^ b ∂μ) =
        Complex.ofReal (vOuterMoment q a b)
  calc
    (∫ t : ℝ,
        literalXMoment q n i t * (t : ℂ) ^ b ∂μ) =
          ∫ t : ℝ,
            Complex.ofReal
              (∫ x : ℝ, F x t ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc]
        with t ht
      exact hpoint t ht
    _ = Complex.ofReal
          (∫ t : ℝ, ∫ x : ℝ,
            F x t ∂μ ∂μ) :=
      integral_ofReal
    _ = Complex.ofReal (vOuterMoment q a b) := by
      rw [hswap]
      rfl

end

end Li2Lean.V

#print axioms Li2Lean.V.vLiteralOuterM0_inl_inr_eq
#print axioms Li2Lean.V.vLiteralOuterM0_inl_inl_eq
