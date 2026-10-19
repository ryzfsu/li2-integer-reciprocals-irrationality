/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TAssembly
import Li2Lean.B3.S0TAllMConstructionPieces
import Li2Lean.B3.S0TC7OneBody
import Li2Lean.B3.S0TPotentialTransfer
import Li2Lean.B3.F1SupportBookkeeping
import Li2Lean.P0.ProductIntegralBound

/-!
# S0-T Core Bound (`H5-hcore`) — Measure Layer and Pointwise C5/C6/C7 Producer Reduction

This module provides:
1. The measure-theoretic triple-integral norm and logarithm bounds for
   `V.Literal.vContourTripleIntegral q n` (both global and restricted to the
   product unit-cube support), using three applications of
   `MeasureTheory.norm_integral_le_of_norm_le_const` and `P0.pi_real_mass_eq_pow`.
2. The zero/collision branch vs. nonvanishing branch split for
   `V.Literal.vContourPhi q n x v z`: when `vContourPhi q n x v z ≠ 0` and
   `0 < n`, all eight pairwise-distinctness, nonvanishing, and denominator
   hypotheses of `V.c5_vContourPhi_log_norm` hold automatically, as does
   translated-center injectivity for `p4_c6_three_self_energies`.
3. The exact identity `2 * V.c5PairLog u = p4C6DiscreteSelf u m` and the
   combined C5 + C6 self-energy step `c5_c6_vContourPhi_self_energy_step`.
4. Construction of the circle-smoothed empirical measure triple
   `v13SmoothedEmpiricalMeasures` (`V.SignedVMeasures`) and concrete C6/C7
   transfer lemmas connecting `translatedAtom` to `VReferencePackage`
   (`P.facts`), `c7_negative_z_one_body_bound`,
   `p4_c7_positive_one_body_scalar`, `weighted_denominator_pair_cost`, and
   `s0T_potential_transfer_modulus`.
5. The conditional assembly `h5_v13_s0T_core_bound_of_pointwise` and the
   compiled downstream leaf helpers `h5_v13_triple_integral_ne_zero_of_actual_g`
   and `h5_v13_phi_log_bound_nonzero_of_core`.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

/-! ## 1. Finite-measure instances and masses for the literal triple integral -/

instance vContourUnitIntervalMeasure_finite :
    IsFiniteMeasure V.Literal.vContourUnitIntervalMeasure := by
  unfold V.Literal.vContourUnitIntervalMeasure
  infer_instance

instance vContourParameterMeasure_finite :
    IsFiniteMeasure V.Literal.vContourParameterMeasure := by
  unfold V.Literal.vContourParameterMeasure
  infer_instance

theorem vContourUnitIntervalMeasure_real_univ :
    V.Literal.vContourUnitIntervalMeasure.real Set.univ = 1 := by
  simp [V.Literal.vContourUnitIntervalMeasure, Measure.real, Real.volume_Icc]

theorem vContourParameterMeasure_real_univ :
    V.Literal.vContourParameterMeasure.real Set.univ = 4 := by
  unfold V.Literal.vContourParameterMeasure
  rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod]
  simp [Measure.count_univ, Measure.restrict_apply_univ, Real.volume_Icc]

theorem vContourUnitIntervalMeasure_pi_real_univ (d : ℕ) :
    (Measure.pi fun _ : Fin d => V.Literal.vContourUnitIntervalMeasure).real Set.univ = 1 := by
  rw [P0.pi_real_mass_eq_pow, vContourUnitIntervalMeasure_real_univ, one_pow]

theorem vContourParameterMeasure_pi_real_univ (d : ℕ) :
    (Measure.pi fun _ : Fin d => V.Literal.vContourParameterMeasure).real Set.univ =
      (4 : ℝ) ^ d := by
  rw [P0.pi_real_mass_eq_pow, vContourParameterMeasure_real_univ, Fintype.card_fin]

/-! ## 2. Almost-everywhere unit-interval support on the three product spaces -/

theorem ae_mem_Icc_vContourUnitIntervalMeasure_pi (d : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin d => V.Literal.vContourUnitIntervalMeasure),
      ∀ i : Fin d, x i ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (Set.univ.pi (fun _ : Fin d => (Set.univ : Set ℝ))) ≤ᵐ[
      Measure.pi fun _ : Fin d => V.Literal.vContourUnitIntervalMeasure]
      Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    apply Measure.ae_le_set_pi
    intro i _
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    intro _
    exact ht
  filter_upwards [hpi] with x hx i
  exact (Set.mem_pi.mp (hx (by simp))) i (by simp)

theorem ae_snd_mem_Icc_vContourParameterMeasure :
    ∀ᵐ p : Fin 4 × ℝ ∂V.Literal.vContourParameterMeasure,
      p.2 ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [literalContourParameterMeasure_ae_mem] with p hp
  exact (Set.mem_prod.mp hp).2

theorem ae_snd_mem_Icc_vContourParameterMeasure_pi (d : ℕ) :
    ∀ᵐ p ∂(Measure.pi fun _ : Fin d => V.Literal.vContourParameterMeasure),
      ∀ i : Fin d, (p i).2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (Set.univ.pi (fun _ : Fin d => (Set.univ : Set (Fin 4 × ℝ)))) ≤ᵐ[
      Measure.pi fun _ : Fin d => V.Literal.vContourParameterMeasure]
      Set.univ.pi (fun _ : Fin d => (Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply Measure.ae_le_set_pi
    intro i _
    filter_upwards [literalContourParameterMeasure_ae_mem] with p hp
    intro _
    exact hp
  filter_upwards [hpi] with p hp i
  exact (Set.mem_prod.mp ((Set.mem_pi.mp (hp (by simp))) i (by simp))).2

theorem vContourPoint_mem_vContourTrace (q : ℕ) (piece : Fin 4) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    V.Literal.vContourPoint q piece t ∈ V.vContourTrace q := by
  fin_cases piece
  · left
    refine ⟨t, ht, ?_⟩
    simp [V.Literal.vContourPoint, V.vNegativeSegment]
  · right; left
    refine ⟨t, ht, ?_⟩
    simp [V.Literal.vContourPoint, V.vPositiveSegment]
  · right; right; left
    refine ⟨t, ht, ?_⟩
    simp [V.Literal.vContourPoint, V.vUpperArc, ContourKit.p0CirclePoint_eq_circleMap,
      circleMap, mul_comm]
  · right; right; right
    refine ⟨t, ht, ?_⟩
    simp [V.Literal.vContourPoint, V.vLowerArc, ContourKit.p0CirclePoint_eq_circleMap,
      circleMap, mul_comm]

/-! ## 3. Nested triple-integral norm and logarithm bounds -/

/-- Threefold application of `MeasureTheory.norm_integral_le_of_norm_le_const`
    on the literal contour triple integral, using an everywhere pointwise bound. -/
theorem h5_nested_norm_integral_bound (q n : ℕ) (C : ℝ)
    (hpt : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤ C) :
    ‖V.Literal.vContourTripleIntegral q n‖ ≤ C * (4 : ℝ) ^ (4 * n) := by
  let μx := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μv := Measure.pi (fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μz := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure)
  unfold V.Literal.vContourTripleIntegral
  have hz : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ),
      ‖∫ p : Fin (4 * n) → Fin 4 × ℝ,
        (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz‖ ≤
        C * (4 : ℝ) ^ (4 * n) := by
    intro x v
    calc
      ‖∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz‖ ≤
          C * μz.real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hpt x v))
      _ = C * (4 : ℝ) ^ (4 * n) := by
        rw [vContourParameterMeasure_pi_real_univ]
  have hv : ∀ (x : Fin (4 * n) → ℝ),
      ‖∫ v : Fin (5 * n) → ℝ,
        (∫ p : Fin (4 * n) → Fin 4 × ℝ,
          (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
            V.Literal.vContourPhi q n x v
              (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz) ∂μv‖ ≤
        C * (4 : ℝ) ^ (4 * n) := by
    intro x
    calc
      ‖∫ v, (∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz) ∂μv‖ ≤
          (C * (4 : ℝ) ^ (4 * n)) * μv.real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hz x))
      _ = C * (4 : ℝ) ^ (4 * n) := by
        rw [vContourUnitIntervalMeasure_pi_real_univ, mul_one]
  calc
    ‖∫ x, ∫ v, ∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz ∂μv ∂μx‖ ≤
        (C * (4 : ℝ) ^ (4 * n)) * μx.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hv)
    _ = C * (4 : ℝ) ^ (4 * n) := by
      rw [vContourUnitIntervalMeasure_pi_real_univ, mul_one]

/-- Support-restricted version of `h5_nested_norm_integral_bound`: the pointwise
    bound is required only on the unit cubes `x_i, v_b, (p_i).2 ∈ [0, 1]`. -/
theorem h5_nested_norm_integral_bound_on_support (q n : ℕ) (C : ℝ)
    (hpt : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ b, v b ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1) →
      ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤ C) :
    ‖V.Literal.vContourTripleIntegral q n‖ ≤ C * (4 : ℝ) ^ (4 * n) := by
  let μx := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μv := Measure.pi (fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μz := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure)
  unfold V.Literal.vContourTripleIntegral
  have hz : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ b, v b ∈ Set.Icc (0 : ℝ) 1) →
      ‖∫ p : Fin (4 * n) → Fin 4 × ℝ,
        (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz‖ ≤
        C * (4 : ℝ) ^ (4 * n) := by
    intro x v hx hv
    have hp_ae : ∀ᵐ p ∂μz,
        ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤ C := by
      filter_upwards [ae_snd_mem_Icc_vContourParameterMeasure_pi (4 * n)] with p hp
      exact hpt x v p hx hv hp
    calc
      ‖∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz‖ ≤
          C * μz.real Set.univ :=
        norm_integral_le_of_norm_le_const hp_ae
      _ = C * (4 : ℝ) ^ (4 * n) := by
        rw [vContourParameterMeasure_pi_real_univ]
  have hv : ∀ (x : Fin (4 * n) → ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      ‖∫ v : Fin (5 * n) → ℝ,
        (∫ p : Fin (4 * n) → Fin 4 × ℝ,
          (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
            V.Literal.vContourPhi q n x v
              (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz) ∂μv‖ ≤
        C * (4 : ℝ) ^ (4 * n) := by
    intro x hx
    have hv_ae : ∀ᵐ v ∂μv,
        ‖∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz‖ ≤
          C * (4 : ℝ) ^ (4 * n) := by
      filter_upwards [ae_mem_Icc_vContourUnitIntervalMeasure_pi (5 * n)] with v hv'
      exact hz x v hx hv'
    calc
      ‖∫ v, (∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz) ∂μv‖ ≤
          (C * (4 : ℝ) ^ (4 * n)) * μv.real Set.univ :=
        norm_integral_le_of_norm_le_const hv_ae
      _ = C * (4 : ℝ) ^ (4 * n) := by
        rw [vContourUnitIntervalMeasure_pi_real_univ, mul_one]
  have hx_ae : ∀ᵐ x ∂μx,
      ‖∫ v, (∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz) ∂μv‖ ≤
        C * (4 : ℝ) ^ (4 * n) := by
    filter_upwards [ae_mem_Icc_vContourUnitIntervalMeasure_pi (4 * n)] with x hx'
    exact hv x hx'
  calc
    ‖∫ x, ∫ v, ∫ p, (∏ i, V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ∂μz ∂μv ∂μx‖ ≤
        (C * (4 : ℝ) ^ (4 * n)) * μx.real Set.univ :=
      norm_integral_le_of_norm_le_const hx_ae
    _ = C * (4 : ℝ) ^ (4 * n) := by
      rw [vContourUnitIntervalMeasure_pi_real_univ, mul_one]

/-- Taking `Real.log` of the triple integral norm bound when
    `V.Literal.vContourTripleIntegral q n ≠ 0`. -/
theorem h5_log_tripleIntegral_le_of_pointwise_exp (q n : ℕ) (B : ℝ)
    (hI : V.Literal.vContourTripleIntegral q n ≠ 0)
    (hpt : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ b, v b ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1) →
      ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤
        Real.exp B / (4 : ℝ) ^ (4 * n)) :
    Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤ B := by
  have hnorm := h5_nested_norm_integral_bound_on_support q n
    (Real.exp B / (4 : ℝ) ^ (4 * n)) hpt
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ (4 * n) := by positivity
  have hcancel : Real.exp B / (4 : ℝ) ^ (4 * n) * (4 : ℝ) ^ (4 * n) = Real.exp B :=
    div_mul_cancel₀ (Real.exp B) h4pos.ne'
  rw [hcancel] at hnorm
  have hIpos : 0 < ‖V.Literal.vContourTripleIntegral q n‖ := norm_pos_iff.mpr hI
  calc
    Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤ Real.log (Real.exp B) :=
      Real.log_le_log hIpos hnorm
    _ = B := Real.log_exp B

/-! ## 4. Nonvanishing extraction from `vContourPhi q n x v z ≠ 0` and C5 log decomposition -/

theorem vContourVandermonde_ne_zero_imp_strict {d : ℕ} {u : Fin d → ℂ}
    (h : V.Literal.vContourVandermonde u ≠ 0) :
    ∀ i j, i < j → u i ≠ u j := by
  intro i j hij heq
  apply h
  unfold V.Literal.vContourVandermonde
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hij, heq]

theorem vContourPhi_ne_zero_hx {q n : ℕ} {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i j, i < j → (x i : ℂ) ≠ (x j : ℂ) := by
  apply vContourVandermonde_ne_zero_imp_strict
  intro h0
  apply hphi
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hv {q n : ℕ} {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i j, i < j → (v i : ℂ) ≠ (v j : ℂ) := by
  apply vContourVandermonde_ne_zero_imp_strict
  intro h0
  apply hphi
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hz {q n : ℕ} {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i j, i < j → z i ≠ z j := by
  apply vContourVandermonde_ne_zero_imp_strict
  intro h0
  apply hphi
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hxv {q n : ℕ} {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i b, z i ≠ (v b : ℂ) := by
  intro i b heq
  apply hphi
  have h0 : (Finset.univ.prod fun i' : Fin (4 * n) =>
      Finset.univ.prod fun b' : Fin (5 * n) => z i' - (v b' : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    exact sub_eq_zero.mpr heq
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hx0 {q n : ℕ} (hn : 0 < n) {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i, (x i : ℂ) ≠ 0 := by
  intro i heq
  apply hphi
  have h3n : 3 * n ≠ 0 := by omega
  have h0 : (∏ i' : Fin (4 * n), (x i' : ℂ) ^ (3 * n)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [heq, zero_pow h3n]
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hv0 {q n : ℕ} (hn : 0 < n) {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ b, (v b : ℂ) ≠ 0 := by
  intro b heq
  apply hphi
  have hn0 : n ≠ 0 := by omega
  have h0 : (∏ b' : Fin (5 * n), (v b' : ℂ) ^ n) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    rw [heq, zero_pow hn0]
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hz0 {q n : ℕ} (hn : 0 < n) {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i, z i ≠ 0 := by
  intro i heq
  apply hphi
  have h5n : (-(5 * n : ℤ)) ≠ 0 := by omega
  have h0 : (∏ i' : Fin (4 * n), z i' ^ (-(5 * n : ℤ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [heq, zero_zpow _ h5n]
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

theorem vContourPhi_ne_zero_hden {q n : ℕ} {x : Fin (4 * n) → ℝ}
    {v : Fin (5 * n) → ℝ} {z : Fin (4 * n) → ℂ}
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    ∀ i b, (q : ℂ) + (x i : ℂ) * (v b : ℂ) ≠ 0 := by
  intro i b heq
  apply hphi
  have h0 : (Finset.univ.prod fun i' : Fin (4 * n) =>
      Finset.univ.prod fun b' : Fin (5 * n) =>
        (q : ℂ) + (x i' : ℂ) * (v b' : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    exact heq
  unfold V.Literal.vContourPhi
  dsimp only
  rw [h0]
  simp

/-- C5 logarithmic expansion derived directly from `vContourPhi q n x v z ≠ 0`
    and `0 < n`, discharging all 8 hypotheses of `V.c5_vContourPhi_log_norm`. -/
theorem c5_vContourPhi_log_norm_of_ne_zero
    {q n : ℕ} (hn : 0 < n) (x : Fin (4 * n) → ℝ)
    (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    Real.log ‖V.Literal.vContourPhi q n x v z‖ =
      2 * V.c5PairLog (fun i => (x i : ℂ)) +
      2 * V.c5PairLog (fun i => (v i : ℂ)) +
      2 * V.c5PairLog z +
      V.c5CrossLog z (fun b => (v b : ℂ)) -
      V.c5DenominatorLog (fun i => (x i : ℂ))
        (fun b => (v b : ℂ)) q +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) :=
  V.c5_vContourPhi_log_norm q n x v z
    (vContourPhi_ne_zero_hx hphi)
    (vContourPhi_ne_zero_hv hphi)
    (vContourPhi_ne_zero_hz hphi)
    (vContourPhi_ne_zero_hxv hphi)
    (vContourPhi_ne_zero_hx0 hn hphi)
    (vContourPhi_ne_zero_hv0 hn hphi)
    (vContourPhi_ne_zero_hz0 hn hphi)
    (vContourPhi_ne_zero_hden hphi)

/-! ## 5. Translated-center injectivity and C5-to-C6 self-energy step -/

theorem translatedAtomCenter_ne_of_strict {d : ℕ} {u : Fin d → ℂ} (m : ℕ)
    (hu : ∀ i j, i < j → u i ≠ u j) :
    ∀ i j, i ≠ j → translatedAtomCenter (u i) m ≠ translatedAtomCenter (u j) m := by
  intro i j hij heq
  have huij : u i = u j := by
    unfold translatedAtomCenter at heq
    exact add_right_cancel heq
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hu i j hlt huij
  · exact hu j i hgt huij.symm

theorem two_mul_c5PairLog_eq_p4C6DiscreteSelf {d : ℕ} (u : Fin d → ℂ) (m : ℕ) :
    2 * V.c5PairLog u = p4C6DiscreteSelf u m := by
  rw [V.c5_strict_pair_eq_half_odFin, ← mul_assoc,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  unfold P0.CellBound.LogQ.odFin p4C6DiscreteSelf v13LogKernel translatedAtomCenter
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rfl
  · congr 2
    ring

theorem p4C6SmoothedSelf_eq_vLogInteraction {d : ℕ} (u : Fin d → ℂ) (m : ℕ) :
    p4C6SmoothedSelf u m =
      V.vLogInteraction (translatedEmpiricalMeasure u m) (translatedEmpiricalMeasure u m) := by
  unfold p4C6SmoothedSelf V.vLogInteraction li2LogInteraction
  have hfn : (fun p : ℂ × ℂ => v13LogKernel p.1 p.2) =
      (fun p : ℂ × ℂ => -li2LogKernel p.1 p.2) := by
    funext p
    simp [v13LogKernel, li2LogKernel]
  rw [hfn, integral_neg]

/-- Combined C5 + C6 self-energy step for a nonvanishing `vContourPhi` point:
    replaces the three Vandermonde pair sums by the three smoothed self-energies
    plus `(13 / 2) * (4 * n) * log (4 * n)`. -/
theorem c5_c6_vContourPhi_self_energy_step
    {q n : ℕ} (hn : 0 < n) (x : Fin (4 * n) → ℝ)
    (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hphi : V.Literal.vContourPhi q n x v z ≠ 0) :
    Real.log ‖V.Literal.vContourPhi q n x v z‖ ≤
      ((4 * n : ℕ) : ℝ) ^ 2 *
        (p4C6SmoothedSelf (fun i => (x i : ℂ)) (4 * n) +
          p4C6SmoothedSelf (fun b => (v b : ℂ)) (4 * n) +
          p4C6SmoothedSelf z (4 * n)) +
      (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
        Real.log ((4 * n : ℕ) : ℝ) +
      V.c5CrossLog z (fun b => (v b : ℂ)) -
      V.c5DenominatorLog (fun i => (x i : ℂ))
        (fun b => (v b : ℂ)) q +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) := by
  have hc5 := c5_vContourPhi_log_norm_of_ne_zero hn x v z hphi
  have hpair_x := two_mul_c5PairLog_eq_p4C6DiscreteSelf (fun i => (x i : ℂ)) (4 * n)
  have hpair_v := two_mul_c5PairLog_eq_p4C6DiscreteSelf (fun b => (v b : ℂ)) (4 * n)
  have hpair_z := two_mul_c5PairLog_eq_p4C6DiscreteSelf z (4 * n)
  have hc6 := p4_c6_three_self_energies hn
    (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    (translatedAtomCenter_ne_of_strict (4 * n) (vContourPhi_ne_zero_hx hphi))
    (translatedAtomCenter_ne_of_strict (4 * n) (vContourPhi_ne_zero_hv hphi))
    (translatedAtomCenter_ne_of_strict (4 * n) (vContourPhi_ne_zero_hz hphi))
  linarith

/-! ## 6. Circle-smoothed empirical `SignedVMeasures` and C6/C7 transfers -/

theorem translatedEmpiricalMeasure_univ_eq_one {m : ℕ} (hm : 0 < m)
    (u : Fin m → ℂ) :
    (translatedEmpiricalMeasure u m) Set.univ = (1 : ℝ≥0∞) := by
  have hreal := translatedEmpiricalMeasure_mass_eq_one hm u
  have hfin : (translatedEmpiricalMeasure u m) Set.univ ≠ ⊤ :=
    measure_ne_top _ _
  have hof := congrArg ENNReal.ofReal hreal
  simpa [Measure.real, ENNReal.ofReal_toReal hfin] using hof

theorem translatedEmpiricalMeasure_univ_five_four {n : ℕ} (hn : 0 < n)
    (u : Fin (5 * n) → ℂ) :
    (translatedEmpiricalMeasure u (4 * n)) Set.univ = (5 / 4 : ℝ≥0∞) := by
  have hreal := translatedEmpiricalMeasure_mass_five_four hn u
  have hfin : (translatedEmpiricalMeasure u (4 * n)) Set.univ ≠ ⊤ :=
    measure_ne_top _ _
  have hof := congrArg ENNReal.ofReal hreal
  have h54 : ENNReal.ofReal (5 / 4 : ℝ) = (5 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [Measure.real, ENNReal.ofReal_toReal hfin, h54] at hof
  exact hof

/-- The v13 circle-smoothed empirical measure triple associated with a finite
    configuration `(x, v, z)` at scale `m = 4 * n`. -/
noncomputable def v13SmoothedEmpiricalMeasures
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (x : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) (z : Fin (4 * n) → ℂ) :
    V.SignedVMeasures where
  q := q
  q_lower := hq.1
  q_upper := hq.2
  μx := translatedEmpiricalMeasure x (4 * n)
  μv := translatedEmpiricalMeasure v (4 * n)
  μz := translatedEmpiricalMeasure z (4 * n)
  mass_x := translatedEmpiricalMeasure_univ_eq_one (by omega) x
  mass_v := translatedEmpiricalMeasure_univ_five_four hn v
  mass_z := translatedEmpiricalMeasure_univ_eq_one (by omega) z
  finite_x := measure_ne_top _ _
  finite_v := measure_ne_top _ _
  finite_z := measure_ne_top _ _

theorem v13SmoothedEmpiricalMeasures_atomless_x
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (x : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) (z : Fin (4 * n) → ℂ)
    (w : ℂ) :
    (v13SmoothedEmpiricalMeasures hq hn x v z).μx {w} = 0 := by
  change translatedEmpiricalMeasure x (4 * n) {w} = 0
  letI : NullSingletonClass (translatedEmpiricalMeasure x (4 * n)) :=
    translatedEmpiricalMeasure_nullSingleton x (show 0 < 4 * n by omega)
  exact (inferInstance : NullSingletonClass (translatedEmpiricalMeasure x (4 * n))).measure_singleton w

theorem v13SmoothedEmpiricalMeasures_atomless_v
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (x : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) (z : Fin (4 * n) → ℂ)
    (w : ℂ) :
    (v13SmoothedEmpiricalMeasures hq hn x v z).μv {w} = 0 := by
  change translatedEmpiricalMeasure v (4 * n) {w} = 0
  letI : NullSingletonClass (translatedEmpiricalMeasure v (4 * n)) :=
    translatedEmpiricalMeasure_nullSingleton v (show 0 < 4 * n by omega)
  exact (inferInstance : NullSingletonClass (translatedEmpiricalMeasure v (4 * n))).measure_singleton w

theorem v13SmoothedEmpiricalMeasures_atomless_z
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (x : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) (z : Fin (4 * n) → ℂ)
    (w : ℂ) :
    (v13SmoothedEmpiricalMeasures hq hn x v z).μz {w} = 0 := by
  change translatedEmpiricalMeasure z (4 * n) {w} = 0
  letI : NullSingletonClass (translatedEmpiricalMeasure z (4 * n)) :=
    translatedEmpiricalMeasure_nullSingleton z (show 0 < 4 * n by omega)
  exact (inferInstance : NullSingletonClass (translatedEmpiricalMeasure z (4 * n))).measure_singleton w

theorem norm_ofReal_le_one_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(t : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact ht.2

theorem one_div_three_smoothingEpsilon_eq {m : ℕ} (hm : 0 < m) :
    1 / (3 * smoothingEpsilon m) = (m : ℝ) ^ 2 / 3 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [smoothingEpsilon_eq_inv_sq]
  field_simp [hmR]

/-- C7 negative `z` one-body sum transfer across `Fin (4 * n)`, producing the
    exact `+ 7` constant in the `hcore` budget. -/
theorem c7_negative_z_one_body_sum_bound
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (z : Fin (4 * n) → ℂ) (hz : ∀ i, z i ∈ V.vContourTrace q)
    (theta : Fin (4 * n) → ℝ) :
    -(5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
      ((4 * n : ℕ) : ℝ) *
        (∑ i : Fin (4 * n),
          -(5 / 4 : ℝ) * Real.log ‖translatedAtom (z i) (4 * n) (theta i)‖) + 7 := by
  have hm : 0 < 4 * n := by omega
  have hmR : (0 : ℝ) < ((4 * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hsum :
      (∑ i : Fin (4 * n), -(5 / 4 : ℝ) * Real.log ‖z i‖) ≤
        (∑ i : Fin (4 * n),
          (-(5 / 4 : ℝ) * Real.log ‖translatedAtom (z i) (4 * n) (theta i)‖ +
            7 * smoothingEpsilon (4 * n))) := by
    apply Finset.sum_le_sum
    intro i _
    exact c7_negative_z_one_body_bound hq hn (hz i) (theta i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum hmR.le
  have hlhs :
      ((4 * n : ℕ) : ℝ) * (∑ i : Fin (4 * n), -(5 / 4 : ℝ) * Real.log ‖z i‖) =
        -(5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) := by
    rw [← Finset.mul_sum]
    push_cast
    ring
  have heps :
      ((4 * n : ℕ) : ℝ) * (((4 * n : ℕ) : ℝ) * (7 * smoothingEpsilon (4 * n))) = 7 := by
    rw [smoothingEpsilon_eq_inv_sq]
    field_simp [hmR.ne']
  linarith

/-- C6/C7 discrete denominator transfer across `Fin (4 * n) × Fin (5 * n)`,
    producing the exact `denominatorTransferCost q` constant. -/
theorem c6_denominator_sum_transfer_at_angles
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (theta : Fin (4 * n) → ℝ) (phi : Fin (5 * n) → ℝ) :
    -V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q ≤
      -(∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
          Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
            translatedAtom (v b : ℂ) (4 * n) (phi b)‖) +
        denominatorTransferCost q := by
  have hm : 0 < 4 * n := by omega
  have hmR : (0 : ℝ) < ((4 * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hpair : ∀ (i : Fin (4 * n)) (b : Fin (5 * n)),
      (5 / 4 : ℝ) *
        (Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
            translatedAtom (v b : ℂ) (4 * n) (phi b)‖ -
          Real.log ‖(q : ℂ) + (x i : ℂ) * (v b : ℂ)‖) ≤
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    intro i b
    have hcost := weighted_denominator_pair_cost hq hn (x i : ℂ) (v b : ℂ)
      (theta i) (phi b) (norm_ofReal_le_one_of_mem_Icc (hx i))
      (norm_ofReal_le_one_of_mem_Icc (hv b))
    have habs :
        Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
            translatedAtom (v b : ℂ) (4 * n) (phi b)‖ -
          Real.log ‖(q : ℂ) + (x i : ℂ) * (v b : ℂ)‖ ≤
        |Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
            translatedAtom (v b : ℂ) (4 * n) (phi b)‖ -
          Real.log ‖(q : ℂ) + (x i : ℂ) * (v b : ℂ)‖| := le_abs_self _
    exact (mul_le_mul_of_nonneg_left habs (by norm_num)).trans hcost
  have hsum :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
              translatedAtom (v b : ℂ) (4 * n) (phi b)‖ -
            Real.log ‖(q : ℂ) + (x i : ℂ) * (v b : ℂ)‖)) ≤
      ∑ _i : Fin (4 * n), ∑ _b : Fin (5 * n),
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro b _
    exact hpair i b
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrhs :
      ((4 * n : ℕ) : ℝ) * (((5 * n : ℕ) : ℝ) *
        (denominatorTransferCost q * smoothingEpsilon (4 * n))) =
      (5 / 4 : ℝ) * denominatorTransferCost q := by
    rw [smoothingEpsilon_eq_inv_sq]
    have hnR : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    push_cast
    field_simp [hnR]
  have hlhs :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
              translatedAtom (v b : ℂ) (4 * n) (phi b)‖ -
            Real.log ‖(q : ℂ) + (x i : ℂ) * (v b : ℂ)‖)) =
      (5 / 4 : ℝ) *
        ((∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
          Real.log ‖(q : ℂ) + translatedAtom (x i : ℂ) (4 * n) (theta i) *
            translatedAtom (v b : ℂ) (4 * n) (phi b)‖) -
          V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q) := by
    unfold V.c5DenominatorLog
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hlhs, hrhs] at hsum
  linarith

/-- Reference potential modulus transfer for `P.measure.μx` at a smoothed atom. -/
theorem s0T_reference_x_potential_transfer
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ)
    (hu : Integrable (fun t : ℂ => Real.log ‖u - t‖) P.measure.μx)
    (hatom : Integrable (fun t : ℂ => Real.log ‖translatedAtom u m theta - t‖)
      P.measure.μx) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx| ≤
      densityTransferBudget P.Ax xMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) := by
  letI : IsFiniteMeasure P.measure.μx := ⟨lt_top_iff_ne_top.mpr P.measure.finite_x⟩
  have hmpos : 0 < m := by omega
  have hmass : P.measure.μx.real Set.univ ≤ xMass := by
    simp [Measure.real, P.measure.mass_x, xMass]
  have hmod := s0T_potential_transfer_modulus
    P.facts.Ax_nonneg (by norm_num [xMass] : (0 : ℝ) ≤ xMass) hmass P.facts.x_ball
    (mul_pos (by norm_num) (smoothingEpsilon_pos hmpos))
    (smoothingEpsilon_le_one_third hm)
    (translatedAtom_dist_le_threeEpsilon u m theta hmpos) hatom hu
  simpa [densityTransferBudget, one_div_three_smoothingEpsilon_eq hmpos] using hmod

/-- Reference potential modulus transfer for `P.measure.μv` at a smoothed atom. -/
theorem s0T_reference_v_potential_transfer
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ)
    (hu : Integrable (fun t : ℂ => Real.log ‖u - t‖) P.measure.μv)
    (hatom : Integrable (fun t : ℂ => Real.log ‖translatedAtom u m theta - t‖)
      P.measure.μv) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv| ≤
      densityTransferBudget P.Av vMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) := by
  letI : IsFiniteMeasure P.measure.μv := ⟨lt_top_iff_ne_top.mpr P.measure.finite_v⟩
  have hmpos : 0 < m := by omega
  have hmass : P.measure.μv.real Set.univ ≤ vMass := by
    simp [Measure.real, P.measure.mass_v, vMass]
  have hmod := s0T_potential_transfer_modulus
    P.facts.Av_nonneg (by norm_num [vMass] : (0 : ℝ) ≤ vMass) hmass P.facts.v_ball
    (mul_pos (by norm_num) (smoothingEpsilon_pos hmpos))
    (smoothingEpsilon_le_one_third hm)
    (translatedAtom_dist_le_threeEpsilon u m theta hmpos) hatom hu
  simpa [densityTransferBudget, one_div_three_smoothingEpsilon_eq hmpos] using hmod

/-- Reference potential modulus transfer for `P.measure.μz` at a smoothed atom. -/
theorem s0T_reference_z_potential_transfer
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ)
    (hu : Integrable (fun t : ℂ => Real.log ‖u - t‖) P.measure.μz)
    (hatom : Integrable (fun t : ℂ => Real.log ‖translatedAtom u m theta - t‖)
      P.measure.μz) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz| ≤
      densityTransferBudget P.Az zMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) := by
  letI : IsFiniteMeasure P.measure.μz := ⟨lt_top_iff_ne_top.mpr P.measure.finite_z⟩
  have hmpos : 0 < m := by omega
  have hmass : P.measure.μz.real Set.univ ≤ zMass := by
    simp [Measure.real, P.measure.mass_z, zMass]
  have hmod := s0T_potential_transfer_modulus
    P.facts.Az_nonneg (by norm_num [zMass] : (0 : ℝ) ≤ zMass) hmass P.facts.z_ball
    (mul_pos (by norm_num) (smoothingEpsilon_pos hmpos))
    (smoothingEpsilon_le_one_third hm)
    (translatedAtom_dist_le_threeEpsilon u m theta hmpos) hatom hu
  simpa [densityTransferBudget, one_div_three_smoothingEpsilon_eq hmpos] using hmod

/-! ## 7. Zero-branch vs. nonzero-branch pointwise integrand reduction and `hcore` assembly -/

/-- The `hcore` right-hand side from `Li2Lean/B3/S0TAssembly.lean:234-242`. -/
def h5CoreBudgetRhs {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) (n : ℕ) : ℝ :=
  -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
      (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
      ((4 * n : ℕ) : ℝ) ^ 2 +
    (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
      Real.log ((4 * n : ℕ) : ℝ) +
    3 * sigmaBudget P.Ax P.Av P.Az *
      (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
    (2 * denominatorTransferCost q + 7 + 130) +
      ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)

/-- Zero-branch vs. nonzero-branch case split for the literal contour integrand:
    if `vContourPhi = 0`, the product vanishes and the exponential bound holds
    trivially; if `vContourPhi ≠ 0`, it reduces to the C5/C6/C7 logarithmic bound
    on `vContourPhi` plus the contour weight product bound. -/
theorem v13_pointwise_integrand_bound_of_nonzero_log_bound
    {q n : ℕ} (Bphi Bw : ℝ)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (p : Fin (4 * n) → Fin 4 × ℝ)
    (hw : ‖∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)‖ ≤
      Real.exp Bw / (4 : ℝ) ^ (4 * n))
    (hphi_log : V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ≠ 0 →
      Real.log ‖V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤ Bphi) :
    ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
      V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤
      Real.exp (Bw + Bphi) / (4 : ℝ) ^ (4 * n) := by
  let z : Fin (4 * n) → ℂ := fun i => V.Literal.vContourPoint q (p i).1 (p i).2
  by_cases hphi : V.Literal.vContourPhi q n x v z = 0
  · change ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v z‖ ≤ _
    rw [hphi, mul_zero, norm_zero]
    positivity
  · have hpos : 0 < ‖V.Literal.vContourPhi q n x v z‖ := norm_pos_iff.mpr hphi
    have hlog := hphi_log hphi
    have hphi_le : ‖V.Literal.vContourPhi q n x v z‖ ≤ Real.exp Bphi := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hlog
    change ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v z‖ ≤ _
    rw [norm_mul, Real.exp_add, mul_div_right_comm]
    exact mul_le_mul hw hphi_le (norm_nonneg _) (by positivity)

/-- Complete reduction of `h5_v13_s0T_core_bound` to the nonvanishing C5/C6/C7
    logarithmic bound on the unit-cube support. -/
theorem h5_v13_s0T_core_bound_of_pointwise
    {q : ℕ} (hq : SignedVBaseRange q)
    (P : VReferencePackage q hq)
    (hpt_nonzero : ∀ (n : ℕ), 64 ≤ 4 * n →
      ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
        (p : Fin (4 * n) → Fin 4 × ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ b, v b ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1) →
      V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ≠ 0 →
      ‖∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)‖ *
        ‖V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤
        Real.exp (h5CoreBudgetRhs P n) / (4 : ℝ) ^ (4 * n)) :
    ∀ n : ℕ, 64 ≤ 4 * n →
      V.Literal.vContourTripleIntegral q n ≠ 0 →
      Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
        -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
          (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
          ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigmaBudget P.Ax P.Av P.Az *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n) := by
  intro n hn hI
  change Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤ h5CoreBudgetRhs P n
  apply h5_log_tripleIntegral_le_of_pointwise_exp q n (h5CoreBudgetRhs P n) hI
  intro x v p hx hv hp
  let z : Fin (4 * n) → ℂ := fun i => V.Literal.vContourPoint q (p i).1 (p i).2
  by_cases hphi : V.Literal.vContourPhi q n x v z = 0
  · change ‖(∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v z‖ ≤ _
    rw [hphi, mul_zero, norm_zero]
    positivity
  · rw [norm_mul]
    exact hpt_nonzero n hn x v p hx hv hp hphi

/-! ## 8. Compiled downstream leaf helpers (`the corresponding branch` and `the corresponding branch`) -/

/-- Valid conditional nonvanishing bridge (`the corresponding branch`): derives
    `vContourTripleIntegral q n ≠ 0` from `vContourActualGValue q n ≠ 0`
    and the determinant identity. -/
theorem h5_v13_triple_integral_ne_zero_of_actual_g
    {q n : ℕ}
    (hdet : vContourActualGValue q n =
      V.Literal.vContourPrefactor q n * V.Literal.vContourTripleIntegral q n)
    (hG : vContourActualGValue q n ≠ 0) :
    V.Literal.vContourTripleIntegral q n ≠ 0 := by
  intro hI
  apply hG
  rw [hdet, hI, mul_zero]

/-- Compiled nonzero `phi_log_bound` leaf (`the corresponding branch`). -/
theorem h5_v13_phi_log_bound_nonzero_of_core_candidate
    {q : ℕ} (hq : SignedVBaseRange q)
    (P : VReferencePackage q hq)
    (Tq : ℝ) (hTq : 0 < Tq)
    (hcore : ∀ n : ℕ, 64 ≤ 4 * n →
      V.Literal.vContourTripleIntegral q n ≠ 0 →
      Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
        -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
          (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
          ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigmaBudget P.Ax P.Av P.Az *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)) :
    ∀ n : ℕ, V.Literal.vContourTripleIntegral q n ≠ 0 →
      64 ≤ 4 * n →
      Real.log |v13PhiMaxValue q Tq n| ≤
        s0TransferPhiBudget q (vAlpha q) (vSigma q)
          Tq (v13PhiMaxValue q Tq n) n := by
  intro n hI hn
  let m : ℝ := ((4 * n : ℕ) : ℝ)
  let energyCoeff : ℝ :=
    ((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log q -
      (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)
  have hI_norm_pos :
      0 < ‖V.Literal.vContourTripleIntegral q n‖ :=
    norm_pos_iff.mpr hI
  have hTpow_pos : 0 < Tq ^ (4 * n) := pow_pos hTq _
  have hphi_pos : 0 < v13PhiMaxValue q Tq n := by
    unfold v13PhiMaxValue
    exact div_pos hI_norm_pos hTpow_pos
  have hpref_pos : 0 < s0TransferPrefactor q n :=
    s0TransferPrefactor_pos hq.1
  have hlog_phi :
      Real.log |v13PhiMaxValue q Tq n| =
        Real.log ‖V.Literal.vContourTripleIntegral q n‖ -
          Real.log (Tq ^ (4 * n)) := by
    rw [abs_of_pos hphi_pos]
    unfold v13PhiMaxValue
    rw [Real.log_div hI_norm_pos.ne' hTpow_pos.ne']
  have hcore' := hcore n hn hI
  rw [← P.facts.sigma_eq] at hcore'
  change Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
      -energyCoeff * m ^ 2 +
        (13 / 2 : ℝ) * m * Real.log m +
        3 * vSigma q * (1 + Real.log (m ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) + m -
        Real.log (s0TransferPrefactor q n) at hcore'
  have hAlpha : vAlpha q ≤ energyCoeff := by
    simpa [energyCoeff] using P.facts.alpha_le
  have henergy : -energyCoeff * m ^ 2 ≤ -vAlpha q * m ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hAlpha (sq_nonneg m)
    linarith
  rw [hlog_phi]
  unfold s0TransferPhiBudget
  rw [Real.log_mul hpref_pos.ne' hTpow_pos.ne']
  change Real.log ‖V.Literal.vContourTripleIntegral q n‖ -
      Real.log (Tq ^ (4 * n)) ≤
    -vAlpha q * m ^ 2 +
      (13 / 2 : ℝ) * m * Real.log m +
      3 * vSigma q * (1 + Real.log (m ^ 2 / 3)) +
      (2 * denominatorTransferCost q + 7 + 130) + m -
      (Real.log (s0TransferPrefactor q n) +
        Real.log (Tq ^ (4 * n)))
  linarith

end

end Li2Lean.B3
