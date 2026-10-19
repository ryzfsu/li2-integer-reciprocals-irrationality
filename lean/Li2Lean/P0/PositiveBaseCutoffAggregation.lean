/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseFrequencyTail
import Li2Lean.P0.CoefficientStepAssembly

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.PositiveBase

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.FrequencyCutoff

/-! These are the order/counting lemmas for the q-envelope cutoff.  The
pointwise q-contour estimate is deliberately an explicit input: the estimate
itself is the preceding P2-1a/b analytic bridge, while these declarations
perform only the finite sum, contour volume, and powerset assembly. -/

theorem qFiniteEnvelopeSum_le_of_head
    {beta : ℝ} {q m : ℕ} (_hq : 2 ≤ q) (_hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (hpoint : ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m)
      (r : IncreasingTuple (m / 2) m)
      (_hr : r ∈ cutoffTuples (m / 2) m (20 * m))
      (u : Fin (m - S.card) → ℝ),
      qContourQValue q S h4 hSI r.val r.property.1
          (fun i => p0EllipsePoint m (u i)) ≤ Real.exp beta)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) :
    ∑ r ∈ cutoffTuples (m / 2) m (20 * m),
        qEnvelopeTerm q m h4 S hSI r u ≤
      (Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ) *
        Real.exp beta *
          ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^
            (m - S.card) := by
  have hdens :
      ∏ i : Fin (m - S.card), contourArcDensity m (u i) ≤
        ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^
          (m - S.card) := by
    calc
      ∏ i : Fin (m - S.card), contourArcDensity m (u i) ≤
          ∏ _i : Fin (m - S.card),
            (m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi) :=
        Finset.prod_le_prod₀
          (fun i _ => Li2Lean.P0.CoefficientAssembly.arcDensity_nonneg m (u i))
          (fun i _ => Li2Lean.P0.CoefficientAssembly.contourArcDensity_le m (u i))
      _ = _ := by simp [div_pow]
  have hterm : ∀ r ∈ cutoffTuples (m / 2) m (20 * m),
      qEnvelopeTerm q m h4 S hSI r u ≤
        Real.exp beta *
          ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^
            (m - S.card) := by
    intro r _hr
    unfold qEnvelopeTerm
    exact mul_le_mul (hpoint S hSI r _hr u) hdens
      (by
        unfold contourArcDensity
        positivity)
      (Real.exp_pos beta).le
  calc
    ∑ r ∈ cutoffTuples (m / 2) m (20 * m),
        qEnvelopeTerm q m h4 S hSI r u ≤
        ∑ _r ∈ cutoffTuples (m / 2) m (20 * m),
          Real.exp beta *
            ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^
              (m - S.card) := Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Li2Lean.P0.CoefficientAssembly.headTupleCount]
      ring

theorem qE_twentyM_le_of_head
    {beta : ℝ} {q m : ℕ} (hq : 2 ≤ q) (hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (hpoint : ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m)
      (r : IncreasingTuple (m / 2) m)
      (_hr : r ∈ cutoffTuples (m / 2) m (20 * m))
      (u : Fin (m - S.card) → ℝ),
      qContourQValue q S h4 hSI r.val r.property.1
          (fun i => p0EllipsePoint m (u i)) ≤ Real.exp beta) :
    qE q m (20 * m) h4 ≤
      (2 : ℝ) ^ m *
        ((Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ) *
          Real.exp beta * Real.exp ((m : ℝ) * (12783 / 10000))) := by
  classical
  unfold qE
  have hcard : ((Iset m).powerset.card : ℝ) = (2 : ℝ) ^ m := by
    rw [Finset.card_powerset, Iset_card]
    push_cast
    ring
  calc
    (∑ S ∈ (Iset m).powerset,
        if hSI : S ⊆ Iset m then
          (Nat.factorial (m - S.card) : ℝ)⁻¹ *
            ∫ u : Fin (m - S.card) → ℝ,
              ∑ r ∈ cutoffTuples (m / 2) m (20 * m),
                qEnvelopeTerm q m h4 S hSI r u
              ∂(ContourKit.productMeasure contourParameterMeasure)
        else 0) ≤
      ∑ _S ∈ (Iset m).powerset,
        (Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ) *
          Real.exp beta * Real.exp ((m : ℝ) * (12783 / 10000)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
      rw [dite_eq_left hSI]
      let d := m - S.card
      let K : ℝ := (m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)
      let c : ℝ :=
        (Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ) *
          Real.exp beta
      have hc0 : 0 ≤ c := by
        dsimp [c]
        positivity
      have hint :
          (∫ u : Fin d → ℝ,
            ∑ r ∈ cutoffTuples (m / 2) m (20 * m),
              qEnvelopeTerm q m h4 S hSI r u
            ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
            (2 * Real.pi) ^ d * (c * K ^ d) := by
        calc
          _ ≤ ∫ _u : Fin d → ℝ, c * K ^ d
              ∂(ContourKit.productMeasure contourParameterMeasure) :=
            integral_mono
              (qIntegrableFiniteEnvelope q m (20 * m) (by omega) h4 S hSI)
              (integrable_const _)
              (fun u => by
                dsimp [d, c, K]
                simpa [c, K, d] using qFiniteEnvelopeSum_le_of_head
                  hq hm8 h4 hpoint S hSI u)
          _ = (2 * Real.pi) ^ d * (c * K ^ d) := by
            rw [integral_const, smul_eq_mul,
              Li2Lean.P0.CoefficientAssembly.productMeasure_real_univ]
      have hvol :
          (2 * Real.pi) ^ d * K ^ d =
            ((m : ℝ) * (12783 / 10000 : ℝ)) ^ d := by
        rw [← mul_pow, show (2 * Real.pi) * K =
          (m : ℝ) * (12783 / 10000 : ℝ) by
            dsimp [K]
            field_simp]
      have hexp := FrequencyHeadCount.factorial_normalized_volume_le_exp
        (m := m) (d := d) (A := (12783 / 10000 : ℝ)) (by norm_num)
      have hfac : 0 < (Nat.factorial d : ℝ) := by
        exact_mod_cast Nat.factorial_pos d
      calc
        (Nat.factorial d : ℝ)⁻¹ *
            (∫ u : Fin d → ℝ,
              ∑ r ∈ cutoffTuples (m / 2) m (20 * m),
                qEnvelopeTerm q m h4 S hSI r u
              ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
            (Nat.factorial d : ℝ)⁻¹ * ((2 * Real.pi) ^ d * (c * K ^ d)) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
        _ = c * (((m : ℝ) * (12783 / 10000 : ℝ)) ^ d /
            (Nat.factorial d : ℝ)) := by
          rw [← hvol]
          field_simp
        _ ≤ c * Real.exp ((m : ℝ) * (12783 / 10000 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp hc0
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]

end

end Li2Lean.P0.PositiveBase
