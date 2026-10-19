/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0ModulusClosed
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace Li2Lean.B3

noncomputable section

/-!
The reciprocal-tail estimate from v13 `v-analytic.tex:496-520`.
The layer-cake variable is split at `1`; total mass controls the first
piece and the closed-ball `A / t` bound controls the second piece.
-/
theorem v13_reciprocal_tail_bound
    {nu : Measure Complex} [IsFiniteMeasure nu]
    {A M d : Real}
    (hA : 0 <= A) (hM : 0 <= M)
    (hmass : nu.real Set.univ <= M)
    (hball : VBallBound nu A)
    (hd : 0 < d) (hdsmall : d <= (1 / 3 : Real))
    {w : Complex}
    (hrecInt : Integrable
      (fun z : Complex => if 2 * d < dist w z then 1 / dist w z else 0) nu) :
    (∫ z, (if 2 * d < dist w z then 1 / dist w z else 0) ∂nu)
      <= M + A * Real.log (1 / (2 * d)) := by
  let f : Complex -> Real := fun z =>
    if 2 * d < dist w z then 1 / dist w z else 0
  let L : Real := 1 / (2 * d)
  have h2d : 0 < 2 * d := by positivity
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hLone : 1 <= L := by
    dsimp [L]
    apply (le_div_iff₀ h2d).2
    have h2dle : 2 * d <= 2 / 3 := by linarith
    linarith
  have hfint : Integrable f nu := by
    simpa [f] using hrecInt
  have hf_nonneg : ∀ z, 0 <= f z := by
    intro z
    by_cases hz : 2 * d < dist w z
    · simp [f, hz]
    · simp [f, hz]
  have hf_bdd : ∀ z, f z <= L := by
    intro z
    by_cases hz : 2 * d < dist w z
    · have hdist : 0 < dist w z := lt_trans h2d hz
      dsimp [f, L]
      simp only [hz, if_pos]
      exact (one_div_le_one_div_of_le h2d (le_of_lt hz))
    · rw [show f z = 0 by simp [f, hz]]
      exact le_of_lt hL
  have hlayer : ∫ z, f z ∂nu =
      ∫ t in Ioc (0 : Real) L, nu.real {z | t <= f z} := by
    exact hfint.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf_nonneg)
      (Filter.Eventually.of_forall hf_bdd)
  let g : Real -> Real := fun t => nu.real {z | t <= f z}
  have hg_nonneg : ∀ t, 0 <= g t := by
    intro t
    exact measureReal_nonneg
  have hg_mass : ∀ t, g t <= M := by
    intro t
    dsimp [g]
    exact (measureReal_mono (subset_univ _)
      (measure_ne_top nu _)).trans hmass
  have hg_meas : Measurable g := by
    apply Antitone.measurable
    intro a b hab
    dsimp [g]
    exact measureReal_mono (by
      intro z hz
      exact le_trans hab hz) (measure_ne_top nu _)
  have hg_intOn : ∀ a b : Real, IntegrableOn g (Ioc a b) volume := by
    intro a b
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      hg_meas.aestronglyMeasurable M
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg t)]
    exact hg_mass t
  have hsplit :
      (∫ t in Ioc (0 : Real) L, g t) =
        (∫ t in Ioc (0 : Real) 1, g t) +
          ∫ t in Ioc 1 L, g t := by
    have hset : Ioc (0 : Real) L = Ioc 0 1 ∪ Ioc 1 L := by
      ext t
      constructor
      · intro ht
        by_cases htle : t <= 1
        · exact Or.inl ⟨ht.1, htle⟩
        · have htl : 1 < t := lt_of_not_ge htle
          exact Or.inr ⟨htl, ht.2⟩
      · intro ht
        rcases ht with ht | ht
        · exact ⟨ht.1, ht.2.trans hLone⟩
        · exact ⟨lt_trans zero_lt_one ht.1, ht.2⟩
    rw [hset]
    apply setIntegral_union
    · exact Set.disjoint_left.2 (by
        intro t ht0 ht1
        linarith [ht0.2, ht1.1])
    · exact measurableSet_Ioc
    · exact hg_intOn 0 1
    · exact hg_intOn 1 L
  have hfirst : (∫ t in Ioc (0 : Real) 1, g t) <= M := by
    calc
      (∫ t in Ioc (0 : Real) 1, g t) <=
          ∫ t in Ioc (0 : Real) 1, (fun _ : Real => M) t := by
        change (∫ t, g t ∂(volume.restrict (Ioc (0 : Real) 1))) <=
          ∫ t, (fun _ : Real => M) t ∂(volume.restrict (Ioc (0 : Real) 1))
        apply integral_mono_ae (μ := volume.restrict (Ioc (0 : Real) 1))
          (hg_intOn 0 1) (integrableOn_const measure_Ioc_lt_top.ne)
        filter_upwards [ae_restrict_mem (μ := volume)
          measurableSet_Ioc] with t ht
        exact hg_mass t
      _ = M := by
        rw [setIntegral_const]
        simp [smul_eq_mul]
  have htail_set : ∀ {t : Real}, 1 < t ->
      {z : Complex | t <= f z} ⊆ closedBall w (1 / t) := by
    intro t ht
    intro z hz
    by_cases hcond : 2 * d < dist w z
    · have hdist : 0 < dist w z := lt_trans h2d hcond
      have hrec : t <= 1 / dist w z := by
        simpa [f, hcond] using hz
      have hmul : t * dist w z <= 1 := (le_div_iff₀ hdist).mp hrec
      have hdist' : dist w z <= 1 / t := by
        apply (le_div_iff₀ (lt_trans zero_lt_one ht)).2
        simpa [mul_comm] using hmul
      show z ∈ closedBall w (1 / t)
      simpa [mem_closedBall, dist_comm] using hdist'
    · simp [f, hcond] at hz
      linarith
  have htail_bound : ∀ {t : Real}, 1 < t ->
      g t <= A / t := by
    intro t ht
    dsimp [g]
    calc
      nu.real {z : Complex | t <= f z} <=
          (nu (closedBall w (1 / t))).toReal :=
        measureReal_mono (htail_set ht)
      _ <= A * (1 / t) :=
        closedBall_bound_of_ballBound hball (by positivity)
      _ = A / t := by ring
  have hInvInt : IntegrableOn (fun t : Real => A / t) (Ioc 1 L) volume := by
    have hcont : ContinuousOn (fun t : Real => A / t) (Icc 1 L) := by
      have hnum : ContinuousOn (fun _ : Real => A) (Icc 1 L) :=
        continuousOn_const
      have hden : ContinuousOn (fun t : Real => t) (Icc 1 L) :=
        continuousOn_id
      apply hnum.div₀ hden
      intro t ht
      linarith [ht.1]
    exact (hcont.integrableOn_Icc).mono_set (by
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2⟩)
  have hsecond : (∫ t in Ioc 1 L, g t) <=
      ∫ t in Ioc 1 L, (fun t : Real => A / t) t := by
    change (∫ t, g t ∂(volume.restrict (Ioc (1 : Real) L))) <=
      ∫ t, (fun t : Real => A / t) t ∂(volume.restrict (Ioc (1 : Real) L))
    apply integral_mono_ae (μ := volume.restrict (Ioc (1 : Real) L))
      (hg_intOn 1 L) hInvInt
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc]
      with t ht
    exact htail_bound ht.1
  have hsecond_eval :
      (∫ t in Ioc 1 L, (fun t : Real => A / t) t) =
        A * Real.log L := by
    rw [← intervalIntegral.integral_of_le hLone]
    calc
      (∫ t in (1 : Real)..L, A / t) =
          A * (∫ t in (1 : Real)..L, 1 / t) := by
        rw [show (fun t : Real => A / t) = fun t => A * (1 / t) by
          funext t; ring]
        exact intervalIntegral.integral_const_mul A (fun t : Real => 1 / t)
      _ = A * Real.log L := by
        congr 1
        simpa [one_div] using (integral_inv_of_pos (a := (1 : Real))
          (b := L) one_pos hL)
  rw [show (∫ z, f z ∂nu) =
      ∫ z, (if 2 * d < dist w z then 1 / dist w z else 0) ∂nu by
        rfl]
  rw [hlayer, hsplit]
  calc
    (∫ t in Ioc (0 : Real) 1, g t) + ∫ t in Ioc 1 L, g t <=
        M + ∫ t in Ioc 1 L, g t := by
      simpa [add_comm] using add_le_add_left hfirst
        (∫ t in Ioc 1 L, g t)
    _ <= M + ∫ t in Ioc 1 L, (fun t : Real => A / t) t := by
      simpa [add_comm] using add_le_add_left hsecond M
    _ = M + A * Real.log (1 / (2 * d)) := by
      rw [hsecond_eval]

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reciprocal_tail_bound
