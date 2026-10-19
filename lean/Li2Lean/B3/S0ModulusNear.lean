/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0ModulusClosed
import Li2Lean.B3.S0ModulusLayerCake
import Li2Lean.V.AllMSmoothing

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Metric

theorem s0T_near_ball_log_integral_bound
    {μ : Measure ℂ} [IsFiniteMeasure μ]
    {A δ : ℝ}
    (hA : 0 ≤ A) (hball : VBallBound μ A)
    (hδ : 0 < δ) (hδsmall : δ ≤ (1 / 3 : ℝ))
    {x c : ℂ} (hxc : ‖x - c‖ ≤ δ)
    (hc : Integrable (fun t : ℂ => Real.log ‖c - t‖) μ) :
    (∫ t in closedBall x (2 * δ), |Real.log ‖c - t‖| ∂μ) ≤
      A * δ * (1 + 2 * Real.log (1 / δ)) := by
  let N : Set ℂ := closedBall x (2 * δ)
  let f : ℂ → ℝ := fun t => |Real.log ‖c - t‖|
  have hN : MeasurableSet N := by
    dsimp [N]
    exact isClosed_closedBall.measurableSet
  have hfc : Integrable f (μ.restrict N) := by
    dsimp [f]
    simpa [IntegrableOn, N] using hc.norm.integrableOn
  have hfc_nn : 0 ≤ᵐ[μ.restrict N] f := Filter.Eventually.of_forall (fun t => abs_nonneg _)
  have hmeas_r : Measurable (fun t : ℂ => ‖c - t‖) :=
    measurable_norm.comp (measurable_const.sub measurable_id)
  have hmeas_f : Measurable f := by
    dsimp [f]
    exact (hmeas_r.log).abs
  have hlayer :
      (∫ t, f t ∂(μ.restrict N)) =
        ∫ s in Ioi (0 : ℝ), (μ.restrict N).real {t | s ≤ f t} :=
    hfc.integral_eq_integral_meas_le hfc_nn
  have h2δ : 0 < 2 * δ := by positivity
  have h2δle : 2 * δ ≤ 1 := by linarith
  have hNbound : (μ.restrict N).real Set.univ ≤ A * (2 * δ) := by
    change ((μ.restrict N) Set.univ).toReal ≤ A * (2 * δ)
    rw [Measure.restrict_apply_univ]
    dsimp [N]
    exact closedBall_bound_of_ballBound hball h2δ
  let q : ℝ → ℝ := fun s => (μ.restrict N).real {t | s ≤ f t}
  have hq_nonneg : ∀ s, 0 ≤ q s := by
    intro s
    exact measureReal_nonneg
  have hq_anti : Antitone q := by
    intro a b hab
    dsimp [q]
    apply measureReal_mono
    · intro t ht
      exact le_trans hab ht
    · exact measure_ne_top _ _
  have hq_meas : Measurable q := hq_anti.measurable
  have hq_mass : ∀ s, q s ≤ A * (2 * δ) := by
    intro s
    dsimp [q]
    calc
      (μ.restrict N).real {t | s ≤ f t} ≤ (μ.restrict N).real Set.univ := by
        exact measureReal_mono (subset_univ _) (measure_ne_top _ _)
      _ ≤ A * (2 * δ) := hNbound
  have hq_ball : ∀ {s : ℝ}, 0 < s →
      q s ≤ A * Real.exp (-s) := by
    intro s hs
    have hset_meas : MeasurableSet {t : ℂ | s ≤ f t} :=
      measurableSet_le measurable_const hmeas_f
    have hball_subset : {t : ℂ | s ≤ f t} ∩ N ⊆ closedBall c (Real.exp (-s)) := by
      intro t ht
      have htN : t ∈ N := ht.2
      have hdistx : ‖x - t‖ ≤ 2 * δ := by
        simpa [N, mem_closedBall, dist_comm, Complex.dist_eq] using htN
      have hd : ‖c - t‖ ≤ 3 * δ := by
        have htri := norm_add_le (c - x) (x - t)
        have htri' : ‖c - t‖ ≤ ‖c - x‖ + ‖x - t‖ := by
          simpa [sub_add_sub_cancel] using htri
        have hxc' : ‖c - x‖ ≤ δ := by simpa [norm_sub_rev] using hxc
        linarith [hxc', hdistx, htri']
      have hd1 : ‖c - t‖ ≤ 1 := by linarith
      have hlog_nonpos : Real.log ‖c - t‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) hd1
      have hlog_abs : |Real.log ‖c - t‖| = -Real.log ‖c - t‖ :=
        abs_of_nonpos hlog_nonpos
      have hslog : s ≤ -Real.log ‖c - t‖ := by
        have := ht.1
        change s ≤ |Real.log ‖c - t‖| at this
        rw [hlog_abs] at this
        exact this
      have hpos : 0 < ‖c - t‖ := by
        by_contra hzero
        have : ‖c - t‖ = 0 := le_antisymm (le_of_not_gt hzero) (norm_nonneg _)
        rw [this, Real.log_zero, neg_zero] at hslog
        linarith
      have hlog_le : Real.log ‖c - t‖ ≤ -s := by linarith
      have hexp : ‖c - t‖ ≤ Real.exp (-s) := by
        rw [← Real.exp_log hpos]
        exact Real.exp_le_exp.mpr hlog_le
      simpa [mem_closedBall, dist_comm, Complex.dist_eq] using hexp
    have hrestr : (μ.restrict N) {t : ℂ | s ≤ f t} =
        μ ({t : ℂ | s ≤ f t} ∩ N) := Measure.restrict_apply hset_meas
    dsimp [q]
    change ((μ.restrict N) {t : ℂ | s ≤ f t}).toReal ≤ A * Real.exp (-s)
    rw [hrestr]
    change μ.real ({t : ℂ | s ≤ f t} ∩ N) ≤ A * Real.exp (-s)
    exact (measureReal_mono hball_subset (measure_ne_top μ _)).trans
      (closedBall_bound_of_ballBound hball (by positivity))
  have hq_int : IntegrableOn q (Ioi (0 : ℝ)) volume := by
    have hscalar_int : IntegrableOn
        (fun s : ℝ => min (2 * A * δ) (A * Real.exp (-s)))
        (Ioi (0 : ℝ)) volume := by
      let T : ℝ := Real.log (1 / (2 * δ))
      let C : ℝ := 2 * A * δ
      let q0 : ℝ → ℝ := fun s => min C (A * Real.exp (-s))
      have hT : 0 ≤ T := by
        dsimp [T]
        apply Real.log_nonneg
        apply (one_le_div h2δ).2
        exact h2δle
      have hexp : Real.exp (-T) = 2 * δ := by
        dsimp [T]
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 / (2 * δ) : ℝ))]
        field_simp
      have hleft : IntegrableOn q0 (Ioc (0 : ℝ) T) volume := by
        have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) T) :=
          integrableOn_const (measure_Ioc_lt_top.ne)
        apply hconst.congr_fun _ measurableSet_Ioc
        intro s hs
        dsimp [q0]
        dsimp [C]
        rw [min_eq_left]
        have hbase : 2 * δ ≤ Real.exp (-s) := by
          rw [← hexp]
          exact Real.exp_le_exp.mpr (by linarith [hs.2])
        nlinarith [mul_le_mul_of_nonneg_left hbase hA]
      have htail : IntegrableOn q0 (Ioi T) volume := by
        have he : IntegrableOn (fun s : ℝ => A * Real.exp (-s)) (Ioi T) := by
          simpa only [IntegrableOn] using
            (Integrable.const_mul (integrableOn_exp_neg_Ioi T) A)
        apply he.congr_fun _ measurableSet_Ioi
        intro s hs
        dsimp [q0]
        dsimp [C]
        rw [min_eq_right]
        have hbase : Real.exp (-s) ≤ 2 * δ := by
          rw [← hexp]
          have hs' : T < s := hs
          exact Real.exp_le_exp.mpr (by linarith [hs'])
        nlinarith [mul_le_mul_of_nonneg_left hbase hA]
      have hq0 : IntegrableOn q0 (Ioi (0 : ℝ)) volume := by
        rw [← Ioc_union_Ioi_eq_Ioi hT]
        exact hleft.union htail
      simpa [q0, C] using hq0
    have hq_mono : IntegrableOn q (Ioi (0 : ℝ)) volume := by
      apply hscalar_int.mono' hq_meas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg s)]
      exact le_min (by simpa [q, mul_comm, mul_left_comm, mul_assoc] using hq_mass s)
        (by exact hq_ball hs)
    exact hq_mono
  have hscalar_int : IntegrableOn
      (fun s : ℝ => min (2 * A * δ) (A * Real.exp (-s))) (Ioi (0 : ℝ)) volume := by
    let T : ℝ := Real.log (1 / (2 * δ))
    let C : ℝ := 2 * A * δ
    let q0 : ℝ → ℝ := fun s => min C (A * Real.exp (-s))
    have hT : 0 ≤ T := by
      dsimp [T]
      apply Real.log_nonneg
      apply (one_le_div h2δ).2
      exact h2δle
    have hexp : Real.exp (-T) = 2 * δ := by
      dsimp [T]
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 / (2 * δ) : ℝ))]
      field_simp
    have hleft : IntegrableOn q0 (Ioc (0 : ℝ) T) volume := by
      have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) T) :=
        integrableOn_const (measure_Ioc_lt_top.ne)
      apply hconst.congr_fun _ measurableSet_Ioc
      intro s hs
      dsimp [q0]
      dsimp [C]
      rw [min_eq_left]
      have hbase : 2 * δ ≤ Real.exp (-s) := by
        rw [← hexp]
        exact Real.exp_le_exp.mpr (by linarith [hs.2])
      nlinarith [mul_le_mul_of_nonneg_left hbase hA]
    have htail : IntegrableOn q0 (Ioi T) volume := by
      have he : IntegrableOn (fun s : ℝ => A * Real.exp (-s)) (Ioi T) := by
        simpa only [IntegrableOn] using
          (Integrable.const_mul (integrableOn_exp_neg_Ioi T) A)
      apply he.congr_fun _ measurableSet_Ioi
      intro s hs
      dsimp [q0]
      dsimp [C]
      rw [min_eq_right]
      have hbase : Real.exp (-s) ≤ 2 * δ := by
        rw [← hexp]
        have hs' : T < s := hs
        exact Real.exp_le_exp.mpr (by linarith [hs'])
      nlinarith [mul_le_mul_of_nonneg_left hbase hA]
    have hq0 : IntegrableOn q0 (Ioi (0 : ℝ)) volume := by
      rw [← Ioc_union_Ioi_eq_Ioi hT]
      exact hleft.union htail
    simpa [q0, C] using hq0
  have hq_le : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      q s ≤ min (2 * A * δ) (A * Real.exp (-s)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    exact le_min (by simpa [q, mul_comm, mul_left_comm, mul_assoc] using hq_mass s)
      (hq_ball hs)
  have hbound_integral :
      (∫ s in Ioi (0 : ℝ), q s) ≤
        ∫ s in Ioi (0 : ℝ), min (2 * A * δ) (A * Real.exp (-s)) := by
    change (∫ s, q s ∂(volume.restrict (Ioi (0 : ℝ)))) ≤
      ∫ s, (fun s : ℝ => min (2 * A * δ) (A * Real.exp (-s))) s
        ∂(volume.restrict (Ioi (0 : ℝ)))
    exact integral_mono_ae hq_int hscalar_int hq_le
  have hscalar_eval := s0_near_field_layer_cake hA hδ h2δle
  rw [show (∫ t in closedBall x (2 * δ), f t ∂μ) =
      ∫ t, f t ∂(μ.restrict N) by rfl] at *
  calc
    (∫ t in closedBall x (2 * δ), |Real.log ‖c - t‖| ∂μ) =
        ∫ s in Ioi (0 : ℝ), q s := by simpa [f, q, N] using hlayer
    _ ≤ ∫ s in Ioi (0 : ℝ), min (2 * A * δ) (A * Real.exp (-s)) := hbound_integral
    _ = 2 * A * δ * (1 + Real.log (1 / (2 * δ))) := hscalar_eval
    _ ≤ A * δ * (1 + 2 * Real.log (1 / δ)) := by
      have hlog : 0 ≤ Real.log (1 / δ) := by
        apply Real.log_nonneg
        exact (one_le_div hδ).2 (by linarith)
      have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have hsplit : Real.log (1 / (2 * δ)) =
          Real.log (1 / δ) - Real.log (2 : ℝ) := by
        rw [show (1 / (2 * δ) : ℝ) = (1 / 2 : ℝ) * (1 / δ) by field_simp]
        rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
          (one_div_ne_zero hδ.ne')]
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv,
          one_div, Real.log_inv]
        ring
      rw [hsplit]
      have hδ0 : 0 ≤ δ := hδ.le
      have hlog2big := Real.log_two_gt_d9
      nlinarith [mul_nonneg hA hδ0]

end
end Li2Lean.B3
