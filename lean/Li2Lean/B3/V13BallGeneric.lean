/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Sharp ball bounds (`VBallBound`) and exact `sigmaBudget = vSigma q` solve for
the v13 reference measures (`H6-S5`, `v-analytic.tex:300-317, 412-437`).
-/

import Li2Lean.B3.F3Ball
import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.B3.Q4ReferenceMeasureFacts
import Li2Lean.B3.Q5ReferencePackageFacts
import Li2Lean.B3.Q6ReferenceMeasureFacts
import Li2Lean.B3.Q7ReferenceMeasureFacts

namespace Li2Lean

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace B3

open MeasureTheory Set Complex
open scoped ENNReal
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## 1. Basic algebra of `VBallBound` -/

private theorem toReal_add_le (a b : ℝ≥0∞) : (a + b).toReal ≤ a.toReal + b.toReal := by
  by_cases ha : a = ⊤
  · subst ha; simp
  · by_cases hb : b = ⊤
    · subst hb; simp
    · rw [ENNReal.toReal_add ha hb]

theorem vBallBound_zero : VBallBound (0 : Measure ℂ) 0 := by
  intro w t _ht
  simp

theorem vBallBound_add_toReal {μ ν : Measure ℂ} {A B : ℝ}
    (hμ : VBallBound μ A) (hν : VBallBound ν B) : VBallBound (μ + ν) (A + B) := by
  intro w t ht
  rw [Measure.add_apply]
  have hsub := toReal_add_le (μ (Metric.ball w t)) (ν (Metric.ball w t))
  have h1 := hμ w t ht
  have h2 := hν w t ht
  linarith

theorem vBallBound_of_le {μ : Measure ℂ} {A B : ℝ}
    (h : VBallBound μ A) (hAB : A ≤ B) : VBallBound μ B := by
  intro w t ht
  exact (h w t ht).trans (mul_le_mul_of_nonneg_right hAB ht.le)

theorem vBallBound_smul {μ : Measure ℂ} {A c : ℝ}
    (hc : 0 ≤ c) (hμ : VBallBound μ A) :
    VBallBound (ENNReal.ofReal c • μ) (c * A) := by
  intro w t ht
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hμ w t ht) hc

/-! ## 2. Sharp chain ball bound (`2 * H`, independent of cell count) -/

/-- Consecutive ordered chain cells: non-empty, `c.left ≤ c.right`, and
adjacent cells share their boundary point `c.right = d.left`. -/
def V13ChainAdjacent : List V13ChainCell → Prop
  | [] => False
  | [c] => c.left ≤ c.right
  | c :: d :: rest =>
      c.left ≤ c.right ∧ c.right = d.left ∧ V13ChainAdjacent (d :: rest)

private theorem v13ChainMeasure_cons_le_Ioi :
    ∀ (c : V13ChainCell) (rest : List V13ChainCell),
      V13ChainAdjacent (c :: rest) →
      ∀ {H : ℝ}, (∀ x ∈ c :: rest, 0 ≤ x.density ∧ x.density ≤ H) →
      ∀ {S : Set ℝ}, MeasurableSet S →
        v13ChainMeasure (c :: rest) S ≤ ENNReal.ofReal H * volume (S ∩ Ioi c.left)
  | c, [], _hcons, H, hd, S, hs => by
      have hc : c.density ≤ H := (hd c (by simp)).2
      have hcoef : ENNReal.ofReal c.density ≤ ENNReal.ofReal H :=
        ENNReal.ofReal_le_ofReal hc
      have hsub : S ∩ Ioc c.left c.right ⊆ S ∩ Ioi c.left := by
        intro x hx
        exact ⟨hx.1, hx.2.1⟩
      have hvol : volume (S ∩ Ioc c.left c.right) ≤ volume (S ∩ Ioi c.left) :=
        measure_mono hsub
      unfold v13ChainMeasure
      simp only [List.foldr_cons, List.foldr_nil, add_zero,
        Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
      exact mul_le_mul hcoef hvol (by positivity) (by positivity)
  | c, d :: rest, hcons, H, hd, S, hs => by
      rcases hcons with ⟨hcl, hcd, hcons'⟩
      have hc : c.density ≤ H := (hd c (by simp)).2
      have hcoef : ENNReal.ofReal c.density ≤ ENNReal.ofReal H :=
        ENNReal.ofReal_le_ofReal hc
      have hih := v13ChainMeasure_cons_le_Ioi d rest hcons'
        (fun x hx => hd x (by simp [hx])) hs
      have hdisj : Disjoint (S ∩ Ioc c.left c.right) (S ∩ Ioi d.left) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h1 : x ≤ d.left := hcd ▸ hx1.2.2
        exact not_lt_of_ge h1 hx2.2
      have hsub : (S ∩ Ioc c.left c.right) ∪ (S ∩ Ioi d.left) ⊆ S ∩ Ioi c.left := by
        intro x hx
        rcases hx with ⟨hxS, h1, _⟩ | ⟨hxS, h2⟩
        · exact ⟨hxS, h1⟩
        · exact ⟨hxS, lt_of_le_of_lt (hcd ▸ hcl) h2⟩
      have hunion :
          volume (S ∩ Ioc c.left c.right) + volume (S ∩ Ioi d.left) ≤
            volume (S ∩ Ioi c.left) := by
        rw [← measure_union hdisj (hs.inter measurableSet_Ioi)]
        exact measure_mono hsub
      unfold v13ChainMeasure
      change (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
        v13ChainMeasure (d :: rest)) S ≤ _
      rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
      calc
        ENNReal.ofReal c.density * volume (S ∩ Ioc c.left c.right) +
            v13ChainMeasure (d :: rest) S ≤
          ENNReal.ofReal H * volume (S ∩ Ioc c.left c.right) +
            ENNReal.ofReal H * volume (S ∩ Ioi d.left) :=
          add_le_add (mul_le_mul_of_nonneg_right hcoef (by positivity)) hih
        _ = ENNReal.ofReal H *
            (volume (S ∩ Ioc c.left c.right) + volume (S ∩ Ioi d.left)) := by
          rw [← mul_add]
        _ ≤ ENNReal.ofReal H * volume (S ∩ Ioi c.left) :=
          mul_le_mul_of_nonneg_left hunion (by positivity)

private theorem preimage_ball_volume_le (w : ℂ) {t : ℝ} (ht : 0 < t) :
    volume (Complex.ofReal ⁻¹' Metric.ball w t) ≤ ENNReal.ofReal (2 * t) := by
  have hsub : Complex.ofReal ⁻¹' Metric.ball w t ⊆ Ioo (w.re - t) (w.re + t) := by
    intro x hx
    simp only [mem_preimage, Metric.mem_ball, Complex.dist_eq] at hx
    have hre : |x - w.re| ≤ ‖(x : ℂ) - w‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm ((x : ℂ) - w)
    have habs : |x - w.re| < t := lt_of_le_of_lt hre hx
    rcases abs_lt.mp habs with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  calc
    volume (Complex.ofReal ⁻¹' Metric.ball w t) ≤
        volume (Ioo (w.re - t) (w.re + t)) := measure_mono hsub
    _ = ENNReal.ofReal (2 * t) := by
      rw [Real.volume_Ioo]
      congr 1
      ring

/-- Sharp linear ball bound `2 * H` for consecutive chain cells with density `≤ H`
(v13 `v-analytic.tex:425-431`). -/
theorem v13ChainMeasureComplex_ballBound_of_adjacent
    (cells : List V13ChainCell) (hcons : V13ChainAdjacent cells) {H : ℝ}
    (hd : ∀ c ∈ cells, 0 ≤ c.density ∧ c.density ≤ H) :
    VBallBound (v13ChainMeasureComplex cells) (2 * H) := by
  cases cells with
  | nil => cases hcons
  | cons c rest =>
      have hH : 0 ≤ H := (hd c (by simp)).1.trans (hd c (by simp)).2
      intro w t ht
      unfold v13ChainMeasureComplex
      have hs : MeasurableSet (Complex.ofReal ⁻¹' Metric.ball w t) :=
        Complex.continuous_ofReal.measurable Metric.isOpen_ball.measurableSet
      rw [Measure.map_apply Complex.continuous_ofReal.measurable
        Metric.isOpen_ball.measurableSet]
      have h1 := v13ChainMeasure_cons_le_Ioi c rest hcons hd hs
      have h2 : volume ((Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioi c.left) ≤
          ENNReal.ofReal (2 * t) :=
        (measure_mono Set.inter_subset_left).trans (preimage_ball_volume_le w ht)
      have h3 : v13ChainMeasure (c :: rest) (Complex.ofReal ⁻¹' Metric.ball w t) ≤
          ENNReal.ofReal (2 * H * t) := by
        calc
          v13ChainMeasure (c :: rest) (Complex.ofReal ⁻¹' Metric.ball w t) ≤
              ENNReal.ofReal H *
                volume ((Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioi c.left) := h1
          _ ≤ ENNReal.ofReal H * ENNReal.ofReal (2 * t) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = ENNReal.ofReal (2 * H * t) := by
            rw [← ENNReal.ofReal_mul hH]
            congr 1
            ring
      have htop : ENNReal.ofReal (2 * H * t) ≠ ⊤ := by simp
      have hreal := ENNReal.toReal_mono htop h3
      simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * H * t)] using hreal

/-! ## 3. Circle-arc and Poisson measure ball bounds (`P_q`) -/

private theorem norm_circleMap_zero_sub_circleMap_zero
    {r : ℝ} (hr : 0 < r) (θ θ₀ : ℝ) :
    ‖circleMap 0 r θ - circleMap 0 r θ₀‖ = 2 * r * |Real.sin ((θ - θ₀) / 2)| := by
  have hfac : circleMap 0 r θ - circleMap 0 r θ₀ =
      (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((θ - θ₀ : ℝ) : ℂ)) - 1) := by
    simp only [circleMap, zero_add]
    have hexp : Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp ((θ₀ : ℂ) * Complex.I) *
          Complex.exp (Complex.I * ((θ - θ₀ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

private theorem angle_diff_cases_of_abs_sin_le
    {θ θ₀ s : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) (2 * Real.pi))
    (hθ₀ : θ₀ ∈ Ioc (0 : ℝ) (2 * Real.pi))
    (hsin : |Real.sin ((θ - θ₀) / 2)| ≤ s) :
    |θ - θ₀| ≤ Real.pi * s ∨
      2 * Real.pi - (θ - θ₀) ≤ Real.pi * s ∨
      2 * Real.pi - (θ₀ - θ) ≤ Real.pi * s := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let u := (θ - θ₀) / 2
  have hu_lt : u < Real.pi := by
    dsimp [u]; linarith [hθ.2, hθ₀.1]
  have hu_gt : -Real.pi < u := by
    dsimp [u]; linarith [hθ.1, hθ₀.2]
  rcases le_or_gt |u| (Real.pi / 2) with hmid | houter
  · left
    have hj := (Real.mul_abs_le_abs_sin hmid).trans hsin
    have hu_abs : |u| = |θ - θ₀| / 2 := by
      dsimp [u]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [hu_abs] at hj
    have hmul := mul_le_mul_of_nonneg_left hj hpi.le
    have hcancel : Real.pi * (2 / Real.pi * (|θ - θ₀| / 2)) = |θ - θ₀| := by
      field_simp [hpi.ne']
    linarith
  · rcases lt_or_ge u 0 with hneg | hpos
    · right; right
      have hu_lt' : u < -(Real.pi / 2) := by
        rw [abs_of_neg hneg] at houter
        linarith
      have h1 : 0 ≤ Real.pi + u := by linarith
      have h2 : |Real.pi + u| ≤ Real.pi / 2 := by
        rw [abs_of_nonneg h1]
        linarith
      have hsin_eq : |Real.sin (Real.pi + u)| = |Real.sin u| := by
        rw [add_comm, Real.sin_add_pi, abs_neg]
      have hj := (Real.mul_abs_le_abs_sin h2).trans (hsin_eq.symm ▸ hsin)
      rw [abs_of_nonneg h1] at hj
      have hmul := mul_le_mul_of_nonneg_left hj hpi.le
      have hcancel : Real.pi * (2 / Real.pi * (Real.pi + u)) =
          2 * Real.pi - (θ₀ - θ) := by
        dsimp [u]
        field_simp [hpi.ne']
        ring
      linarith
    · right; left
      have hu_gt' : Real.pi / 2 < u := by
        rw [abs_of_nonneg hpos] at houter
        exact houter
      have h1 : 0 ≤ Real.pi - u := by linarith
      have h2 : |Real.pi - u| ≤ Real.pi / 2 := by
        rw [abs_of_nonneg h1]
        linarith
      have hsin_eq : |Real.sin (Real.pi - u)| = |Real.sin u| := by
        rw [Real.sin_pi_sub]
      have hj := (Real.mul_abs_le_abs_sin h2).trans (hsin_eq.symm ▸ hsin)
      rw [abs_of_nonneg h1] at hj
      have hmul := mul_le_mul_of_nonneg_left hj hpi.le
      have hcancel : Real.pi * (2 / Real.pi * (Real.pi - u)) =
          2 * Real.pi - (θ - θ₀) := by
        dsimp [u]
        field_simp [hpi.ne']
      linarith

private theorem wrap_intervals_length_sum
    {θ₀ δ : ℝ} (hθ₀ : θ₀ ∈ Ioc (0 : ℝ) (2 * Real.pi)) (hδ : 0 ≤ δ) :
    let L₁ := min (2 * Real.pi) (θ₀ + δ) - max 0 (θ₀ - δ)
    let L₂ := max 0 (δ - θ₀)
    let L₃ := max 0 (θ₀ + δ - 2 * Real.pi)
    0 ≤ L₁ ∧ L₁ + L₂ + L₃ = 2 * δ := by
  rcases hθ₀ with ⟨h1, h2⟩
  dsimp only
  by_cases hA : θ₀ + δ ≤ 2 * Real.pi
  · have hmin : min (2 * Real.pi) (θ₀ + δ) = θ₀ + δ := min_eq_right hA
    by_cases hB : θ₀ - δ ≤ 0
    · have hmax : max 0 (θ₀ - δ) = 0 := max_eq_left hB
      have hL2 : max 0 (δ - θ₀) = δ - θ₀ :=
        max_eq_right (by linarith)
      have hL3 : max 0 (θ₀ + δ - 2 * Real.pi) = 0 :=
        max_eq_left (by linarith)
      rw [hmin, hmax, hL2, hL3]
      constructor <;> linarith
    · have hB' : 0 ≤ θ₀ - δ := le_of_not_ge hB
      have hmax : max 0 (θ₀ - δ) = θ₀ - δ := max_eq_right hB'
      have hL2 : max 0 (δ - θ₀) = 0 :=
        max_eq_left (by linarith)
      have hL3 : max 0 (θ₀ + δ - 2 * Real.pi) = 0 :=
        max_eq_left (by linarith)
      rw [hmin, hmax, hL2, hL3]
      constructor <;> linarith
  · have hA' : 2 * Real.pi ≤ θ₀ + δ := le_of_not_ge hA
    have hmin : min (2 * Real.pi) (θ₀ + δ) = 2 * Real.pi := min_eq_left hA'
    by_cases hB : θ₀ - δ ≤ 0
    · have hmax : max 0 (θ₀ - δ) = 0 := max_eq_left hB
      have hL2 : max 0 (δ - θ₀) = δ - θ₀ := max_eq_right (by linarith)
      have hL3 : max 0 (θ₀ + δ - 2 * Real.pi) =
          θ₀ + δ - 2 * Real.pi := max_eq_right (by linarith)
      rw [hmin, hmax, hL2, hL3]
      constructor <;> linarith
    · have hB' : 0 ≤ θ₀ - δ := le_of_not_ge hB
      have hmax : max 0 (θ₀ - δ) = θ₀ - δ := max_eq_right hB'
      have hL2 : max 0 (δ - θ₀) = 0 := max_eq_left (by linarith)
      have hL3 : max 0 (θ₀ + δ - 2 * Real.pi) =
          θ₀ + δ - 2 * Real.pi := max_eq_right (by linarith)
      rw [hmin, hmax, hL2, hL3]
      constructor <;> linarith

private theorem ofReal_max_zero (x : ℝ) :
    ENNReal.ofReal (max 0 x) = ENNReal.ofReal x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right hx]
  · rw [max_eq_left hx, ENNReal.ofReal_eq_zero.mpr hx, ENNReal.ofReal_zero]

private theorem circleMap_preimage_ball_volume_le
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (w : ℂ) :
    volume (circleMap 0 r ⁻¹' Metric.ball w t ∩ Ioc (0 : ℝ) (2 * Real.pi)) ≤
      ENNReal.ofReal (2 * Real.pi * t / r) := by
  let S := circleMap 0 r ⁻¹' Metric.ball w t ∩ Ioc (0 : ℝ) (2 * Real.pi)
  let δ := Real.pi * t / r
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have h2δ : 2 * Real.pi * t / r = 2 * δ := by dsimp [δ]; ring
  rw [h2δ]
  by_cases hne : S.Nonempty
  · rcases hne with ⟨θ₀, hθ₀B, hθ₀I⟩
    let J₁ := Icc (max 0 (θ₀ - δ)) (min (2 * Real.pi) (θ₀ + δ))
    let J₂ := Icc (θ₀ + 2 * Real.pi - δ) (2 * Real.pi)
    let J₃ := Icc 0 (θ₀ + δ - 2 * Real.pi)
    have hsub : S ⊆ (J₁ ∪ J₂) ∪ J₃ := by
      intro θ ⟨hθB, hθI⟩
      have hdist : ‖circleMap 0 r θ - circleMap 0 r θ₀‖ ≤ 2 * t := by
        have d1 : ‖circleMap 0 r θ - w‖ < t := by
          simpa [Metric.mem_ball, dist_eq_norm] using hθB
        have d2 : ‖circleMap 0 r θ₀ - w‖ < t := by
          simpa [Metric.mem_ball, dist_eq_norm] using hθ₀B
        have htri : ‖circleMap 0 r θ - circleMap 0 r θ₀‖ ≤
            ‖circleMap 0 r θ - w‖ + ‖circleMap 0 r θ₀ - w‖ := by
          rw [← sub_sub_sub_cancel_right (circleMap 0 r θ) (circleMap 0 r θ₀) w]
          exact norm_sub_le _ _
        linarith
      rw [norm_circleMap_zero_sub_circleMap_zero hr] at hdist
      have hsin : |Real.sin ((θ - θ₀) / 2)| ≤ t / r := by
        rw [le_div_iff₀ hr]
        linarith
      have hcases := angle_diff_cases_of_abs_sin_le hθI hθ₀I hsin
      have hδ_eq : Real.pi * (t / r) = δ := by dsimp [δ]; ring
      rw [hδ_eq] at hcases
      rcases hcases with hc1 | hc2 | hc3
      · left; left
        rcases abs_sub_le_iff.mp hc1 with ⟨hlo, hhi⟩
        exact ⟨max_le hθI.1.le (by linarith), le_min hθI.2 (by linarith)⟩
      · left; right
        exact ⟨by linarith, hθI.2⟩
      · right
        exact ⟨hθI.1.le, by linarith⟩
    have hL := wrap_intervals_length_sum hθ₀I hδ
    have hJ₁ : volume J₁ = ENNReal.ofReal (min (2 * Real.pi) (θ₀ + δ) - max 0 (θ₀ - δ)) :=
      Real.volume_Icc
    have hJ₂ : volume J₂ = ENNReal.ofReal (max 0 (δ - θ₀)) := by
      rw [Real.volume_Icc, ofReal_max_zero]
      congr 1
      ring
    have hJ₃ : volume J₃ = ENNReal.ofReal (max 0 (θ₀ + δ - 2 * Real.pi)) := by
      rw [Real.volume_Icc, sub_zero, ofReal_max_zero]
    calc
      volume S ≤ volume ((J₁ ∪ J₂) ∪ J₃) := measure_mono hsub
      _ ≤ volume (J₁ ∪ J₂) + volume J₃ := measure_union_le (μ := volume) _ _
      _ ≤ volume J₁ + volume J₂ + volume J₃ := by
        exact add_le_add_left (measure_union_le (μ := volume) J₁ J₂) (volume J₃)
      _ = ENNReal.ofReal (2 * δ) := by
        rw [hJ₁, hJ₂, hJ₃, ← ENNReal.ofReal_add hL.1 (le_max_left 0 _),
          ← ENNReal.ofReal_add (add_nonneg hL.1 (le_max_left 0 _)) (le_max_left 0 _),
          hL.2]
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change volume S ≤ ENNReal.ofReal (2 * δ)
    rw [hS, measure_empty]
    exact bot_le

private theorem poissonKernel_unit_le
    {q ζ : ℂ} (hq : ‖q‖ < 1) (hζ : ‖ζ‖ = 1) :
    poissonKernel 0 q ζ ≤ (1 + ‖q‖) / (1 - ‖q‖) := by
  simp only [poissonKernel, sub_zero, hζ, one_pow]
  have h1 : 0 < 1 - ‖q‖ := by linarith
  have hsub : 1 - ‖q‖ ≤ ‖ζ - q‖ := by
    have h := norm_sub_norm_le ζ q
    linarith [hζ]
  have hsq : (1 - ‖q‖) ^ 2 ≤ ‖ζ - q‖ ^ 2 :=
    pow_le_pow_left₀ h1.le hsub 2
  have hden : 0 < ‖ζ - q‖ ^ 2 := lt_of_lt_of_le (sq_pos_of_pos h1) hsq
  rw [div_le_div_iff₀ hden h1]
  have hpos : 0 ≤ 1 + ‖q‖ := by linarith [norm_nonneg q]
  nlinarith

private theorem v13GlobalPoissonAngleDensity_le
    {p : ℂ} {ρ : ℝ} (hp : ‖p‖ ≤ ρ) (hρ : ρ < 3 / 5) (θ : ℝ) :
    v13GlobalPoissonAngleDensity p θ ≤
      (2 * Real.pi)⁻¹ * ((3 / 5 + ρ) / (3 / 5 - ρ)) := by
  unfold v13GlobalPoissonAngleDensity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hr : (v13GlobalPoissonRadius : ℂ) = ((3 / 5 : ℝ) : ℂ) := by
    norm_num [v13GlobalPoissonRadius]
  have hq_le : ‖p / (v13GlobalPoissonRadius : ℂ)‖ ≤ ρ / (3 / 5) := by
    rw [hr, norm_div, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    exact div_le_div_of_nonneg_right hp (by norm_num)
  have hq_lt : ‖p / (v13GlobalPoissonRadius : ℂ)‖ < 1 := by
    refine lt_of_le_of_lt hq_le ?_
    rw [div_lt_one (by norm_num)]
    exact hρ
  have hζ : ‖circleMap 0 1 θ‖ = 1 := by
    simpa using (norm_circleMap_zero 1 θ)
  refine (poissonKernel_unit_le hq_lt hζ).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem v13GlobalCirclePoissonMeasure_ballBound
    {p : ℂ} {ρ : ℝ} (hp : ‖p‖ ≤ ρ) (hρ : ρ < 3 / 5) :
    VBallBound (v13GlobalCirclePoissonMeasure p)
      ((3 / 5 + ρ) / ((3 / 5) * (3 / 5 - ρ))) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg p).trans hp
  have hr_pos : 0 < v13GlobalPoissonRadius := by norm_num [v13GlobalPoissonRadius]
  let K := (2 * Real.pi)⁻¹ * ((3 / 5 + ρ) / (3 / 5 - ρ))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))
  intro w t ht
  let B := circleMap 0 v13GlobalPoissonRadius ⁻¹' Metric.ball w t
  have hB : MeasurableSet B :=
    Metric.isOpen_ball.measurableSet.preimage
      (continuous_circleMap 0 v13GlobalPoissonRadius).measurable
  have hval : v13GlobalCirclePoissonMeasure p (Metric.ball w t) ≤
      ENNReal.ofReal (((3 / 5 + ρ) / ((3 / 5) * (3 / 5 - ρ))) * t) := by
    rw [v13GlobalCirclePoissonMeasure,
      Measure.map_apply (continuous_circleMap 0 v13GlobalPoissonRadius).measurable
        Metric.isOpen_ball.measurableSet,
      withDensity_apply _ hB, Measure.restrict_restrict hB]
    calc
      ∫⁻ θ in B ∩ Ioc 0 (2 * Real.pi),
          ENNReal.ofReal (v13GlobalPoissonAngleDensity p θ) ∂volume ≤
        ∫⁻ _ in B ∩ Ioc 0 (2 * Real.pi), ENNReal.ofReal K ∂volume := by
          apply lintegral_mono
          intro θ
          exact ENNReal.ofReal_le_ofReal (v13GlobalPoissonAngleDensity_le hp hρ θ)
      _ = ENNReal.ofReal K * volume (B ∩ Ioc 0 (2 * Real.pi)) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi * t / (3 / 5)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [B, v13GlobalPoissonRadius] using
              circleMap_preimage_ball_volume_le hr_pos ht w) (by positivity)
      _ = ENNReal.ofReal (((3 / 5 + ρ) / ((3 / 5) * (3 / 5 - ρ))) * t) := by
          rw [← ENNReal.ofReal_mul hK]
          congr 1
          dsimp [K]
          have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp [hpi]
  have htop : ENNReal.ofReal (((3 / 5 + ρ) / ((3 / 5) * (3 / 5 - ρ))) * t) ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono htop hval
  have hpos : 0 ≤ ((3 / 5 + ρ) / ((3 / 5) * (3 / 5 - ρ))) * t :=
    mul_nonneg (div_nonneg (by linarith) (mul_nonneg (by norm_num) (by linarith))) ht.le
  simpa [ENNReal.toReal_ofReal hpos] using hreal

/-- Sharp Poisson ball bound `P_q` for a list of decoded Poisson rows
(v13 `v-analytic.tex:416-432`). -/
theorem v13PoissonMeasure_ballBound (rows : List PR) (ρ : PR → ℝ)
    (hρ : ∀ c ∈ rows, ‖v13PoissonPoint c‖ ≤ ρ c ∧ ρ c < 3 / 5)
    (hw : ∀ c ∈ rows, 0 ≤ IK.val c.w) :
    VBallBound (v13PoissonMeasure rows)
      ((rows.map fun c =>
        (c.mult : ℝ) * IK.val c.w * (3 / 5 + ρ c) / ((3 / 5) * (3 / 5 - ρ c))).sum) := by
  induction rows with
  | nil =>
      simpa [v13PoissonMeasure] using vBallBound_zero
  | cons c rs ih =>
      simp only [v13PoissonMeasure, List.foldr_cons, List.map_cons, List.sum_cons]
      have hcρ := hρ c (by simp)
      have hcw : 0 ≤ (c.mult : ℝ) * IK.val c.w :=
        mul_nonneg (Nat.cast_nonneg _) (hw c (by simp))
      have hatom : VBallBound (v13PoissonAtom c)
          ((c.mult : ℝ) * IK.val c.w * (3 / 5 + ρ c) / ((3 / 5) * (3 / 5 - ρ c))) := by
        rw [mul_div_assoc]
        exact vBallBound_smul hcw
          (v13GlobalCirclePoissonMeasure_ballBound hcρ.1 hcρ.2)
      exact vBallBound_add_toReal hatom
        (ih (fun x hx => hρ x (by simp [hx])) (fun x hx => hw x (by simp [hx])))

/-! ## 4. Fast `decide +kernel` bridge for chain cells and Poisson rows -/

/-- Direct `QF` triples `(left, right, density)` for a chain before `jumpsI` encoding. -/
def chainCellsQF : List Int → List QF → List (QF × QF × QF)
  | a :: b :: tl, d :: ds => ((a, U), (b, U), d) :: chainCellsQF (b :: tl) ds
  | _, _ => []

private theorem jumpsI_ne_nil (prev : QF) (ds : List QF) : jumpsI prev ds ≠ [] := by
  cases ds <;> simp [jumpsI]

private theorem v13ChainCellsAux_zip_jumpsI :
    ∀ (ds : List QF) (coords : List Int) (prev : QF),
      coords.length = ds.length + 1 →
      0 < prev.2 →
      (∀ d ∈ ds, 0 < d.2) →
      v13ChainCellsAux (IK.val prev)
        (((coords.zip (jumpsI prev ds)).map fun p => ⟨(p.1, U), p.2⟩)) =
        (chainCellsQF coords ds).map
          (fun t => { left := IK.val t.1, right := IK.val t.2.1, density := IK.val t.2.2 })
  | [], [], _prev, hlen, _, _ => by simp at hlen
  | [], [a], _prev, _, _, _ => by
      simp [jumpsI, v13ChainCellsAux, chainCellsQF]
  | [], _ :: _ :: _, _prev, hlen, _, _ => by simp at hlen
  | _ :: _, [], _prev, hlen, _, _ => by simp at hlen
  | _ :: _, [_], _prev, hlen, _, _ => by simp at hlen
  | d :: ds, a :: b :: tl, prev, hlen, hprev, hds => by
      have hd : 0 < d.2 := hds d (by simp)
      have hlen' : (b :: tl).length = ds.length + 1 := by
        simpa [List.length_cons] using hlen
      cases hjs : jumpsI d ds with
      | nil => exact False.elim (jumpsI_ne_nil d ds hjs)
      | cons j₁ js =>
          have hstep : IK.val prev + IK.val (qsub d prev) = IK.val d := by
            rw [IK.val_qsub hd hprev]
            ring
          simp only [jumpsI, hjs, List.zip_cons_cons, List.map_cons,
            v13ChainCellsAux, chainCellsQF, hstep]
          congr 1
          simpa [hjs] using
            (v13ChainCellsAux_zip_jumpsI ds (b :: tl) d hlen' hd
              (fun x hx => hds x (by simp [hx])))

private theorem densI_length :
    ∀ (coords ms : List Int),
      coords.length = ms.length + 1 → (densI coords ms).length = ms.length
  | [], _, h => by simp at h
  | [_], [], _ => rfl
  | [_], _ :: _, h => by simp at h
  | _ :: _ :: _, [], h => by simp at h
  | _ :: b :: tl, _ :: ms, h => by
      simp only [densI, List.length_cons] at h ⊢
      exact congrArg (· + 1) (densI_length (b :: tl) ms (Nat.succ.inj h))

theorem v13ChainCells_chainCP_eq_map
    (hdr : V.Q2Certificate.ChainHeader) (es : List V.Q2Certificate.ChainEntry)
    (hw : V.EnergyCertI.widthsPos hdr es = true) :
    v13ChainCells (V.EnergyCertI.chainCP hdr es) =
      (chainCellsQF (V.EnergyCertI.chainCoords hdr es)
        (densI (V.EnergyCertI.chainCoords hdr es)
          (V.EnergyCertI.chainMassU hdr es))).map
          (fun t => { left := IK.val t.1, right := IK.val t.2.1, density := IK.val t.2.2 }) := by
  have hlen_cm : (V.EnergyCertI.chainCoords hdr es).length =
      (V.EnergyCertI.chainMassU hdr es).length + 1 := by
    simp [V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU]
  have hlen_d :
      (densI (V.EnergyCertI.chainCoords hdr es)
        (V.EnergyCertI.chainMassU hdr es)).length =
      (V.EnergyCertI.chainMassU hdr es).length :=
    densI_length _ _ hlen_cm
  have hlen : (V.EnergyCertI.chainCoords hdr es).length =
      (densI (V.EnergyCertI.chainCoords hdr es)
        (V.EnergyCertI.chainMassU hdr es)).length + 1 := by
    omega
  have hds : ∀ d ∈ densI (V.EnergyCertI.chainCoords hdr es)
      (V.EnergyCertI.chainMassU hdr es), 0 < d.2 := by
    intro d hd
    have hall := List.all_eq_true.mp hw d hd
    exact of_decide_eq_true hall
  have h0 : (0 : ℝ) = IK.val (0, 1) := by simp [IK.val]
  unfold v13ChainCells V.EnergyCertI.chainCP
  rw [h0]
  exact v13ChainCellsAux_zip_jumpsI _ _ (0, 1) hlen (by decide) hds

private theorem v13ChainConsecutive_map_chainCellsQF :
    ∀ (coords : List Int) (ds : List QF),
      (chainCellsQF coords ds) ≠ [] →
      (∀ t ∈ chainCellsQF coords ds, IK.val t.1 ≤ IK.val t.2.1) →
      V13ChainAdjacent
        ((chainCellsQF coords ds).map
          (fun t => { left := IK.val t.1, right := IK.val t.2.1, density := IK.val t.2.2 }))
  | a :: b :: tl, d :: ds, _hne, hle => by
      cases hnext : chainCellsQF (b :: tl) ds with
      | nil =>
          simp only [chainCellsQF, hnext, List.map_cons, List.map_nil, V13ChainAdjacent]
          exact hle ((a, U), (b, U), d) (by simp [chainCellsQF])
      | cons t₂ ts =>
          have hhead : t₂.1 = (b, U) := by
            cases tl with
            | nil => simp [chainCellsQF] at hnext
            | cons c tl' =>
                cases ds with
                | nil => simp [chainCellsQF] at hnext
                | cons d₂ ds' =>
                    simp only [chainCellsQF, List.cons.injEq] at hnext
                    rw [← hnext.1]
          simp only [chainCellsQF, List.map_cons]
          rw [hnext]
          simp only [List.map_cons, V13ChainAdjacent]
          refine ⟨hle ((a, U), (b, U), d) (by simp [chainCellsQF]),
            congrArg IK.val hhead.symm, ?_⟩
          simpa [hnext] using
            (v13ChainConsecutive_map_chainCellsQF (b :: tl) ds (by simp [hnext])
              (fun t ht => hle t (by simp [chainCellsQF, ht])))
  | [], _, hne, _ => False.elim (hne rfl)
  | [_], _, hne, _ => False.elim (hne rfl)
  | _ :: _ :: _, [], hne, _ => False.elim (hne rfl)

/-- Pure Boolean check for consecutive ordering and sharp max-density `H` on a chain. -/
def chainCellsOK (hdr : V.Q2Certificate.ChainHeader)
    (es : List V.Q2Certificate.ChainEntry) (H : QF) : Bool :=
  let cs := chainCellsQF (V.EnergyCertI.chainCoords hdr es)
    (densI (V.EnergyCertI.chainCoords hdr es) (V.EnergyCertI.chainMassU hdr es))
  V.EnergyCertI.widthsPos hdr es && decide (0 < H.2) && !cs.isEmpty &&
    cs.all (fun t => qle t.1 t.2.1 && qle (0, 1) t.2.2 && qle t.2.2 H)

private theorem den_pos_of_mem_chainCellsQF :
    ∀ (coords : List Int) (ds : List QF),
      (∀ d ∈ ds, 0 < d.2) →
      ∀ t ∈ chainCellsQF coords ds, 0 < t.1.2 ∧ 0 < t.2.1.2 ∧ 0 < t.2.2.2
  | a :: b :: tl, d :: ds, hds, t, ht => by
      simp only [chainCellsQF, List.mem_cons] at ht
      rcases ht with rfl | ht'
      · exact ⟨by norm_num [U], by norm_num [U], hds d (by simp)⟩
      · exact den_pos_of_mem_chainCellsQF (b :: tl) ds
          (fun x hx => hds x (by simp [hx])) t ht'
  | [], _, _, _, ht => by simp [chainCellsQF] at ht
  | [_], _, _, _, ht => by simp [chainCellsQF] at ht
  | _ :: _ :: _, [], _, _, ht => by simp [chainCellsQF] at ht

theorem v13DecodedChainMeasure_ballBound_of_chainCellsOK
    {hdr : V.Q2Certificate.ChainHeader} {es : List V.Q2Certificate.ChainEntry} {H : QF}
    (hok : chainCellsOK hdr es H = true) :
    VBallBound (v13DecodedChainMeasure (V.EnergyCertI.chainCP hdr es))
      (2 * IK.val H) := by
  unfold chainCellsOK at hok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨hw, hH⟩, hne⟩, hall⟩
  have hds : ∀ d ∈ densI (V.EnergyCertI.chainCoords hdr es)
      (V.EnergyCertI.chainMassU hdr es), 0 < d.2 := by
    intro d hd
    exact of_decide_eq_true (List.all_eq_true.mp hw d hd)
  have hmap := v13ChainCells_chainCP_eq_map hdr es hw
  unfold v13DecodedChainMeasure
  apply v13ChainMeasureComplex_ballBound_of_adjacent
  · rw [hmap]
    apply v13ChainConsecutive_map_chainCellsQF _ _ hne
    intro t ht
    have ht_all := List.all_eq_true.mp hall t ht
    simp only [Bool.and_eq_true] at ht_all
    have hden := den_pos_of_mem_chainCellsQF _ _ hds t ht
    exact (IK.qle_spec hden.1 hden.2.1).mp ht_all.1.1
  · rw [hmap]
    intro c hc
    rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
    have ht_all := List.all_eq_true.mp hall t ht
    simp only [Bool.and_eq_true] at ht_all
    have hden := den_pos_of_mem_chainCellsQF _ _ hds t ht
    have h0 : 0 ≤ IK.val t.2.2 := by
      have h := (IK.qle_spec (by decide) hden.2.2).mp ht_all.1.2
      simpa [IK.val] using h
    have hleH : IK.val t.2.2 ≤ IK.val H :=
      (IK.qle_spec hden.2.2 hH).mp ht_all.2
    exact ⟨h0, hleH⟩

/-- Integer radius numerator `⌊√(cx^2 + cy^2)⌋ + 1` in units of `1 / U`. -/
def v13PoissonRadNum (c : PR) : ℕ :=
  Nat.sqrt (c.cx.1.natAbs ^ 2 + c.cy.1.natAbs ^ 2) + 1

/-- Certified rational upper bound on `‖v13PoissonPoint c‖`. -/
noncomputable def v13PoissonRad (c : PR) : ℝ :=
  (v13PoissonRadNum c : ℝ) / (U : ℝ)

def v13PoissonRowOK (c : PR) : Bool :=
  decide (c.cx.2 = U ∧ c.cy.2 = U ∧ c.w.2 = U ∧ 0 ≤ c.w.1 ∧
    v13PoissonRadNum c < 30000000000000)

/-- Integer ceiling of a single Poisson row's ball-bound contribution in units of `1 / (3·10^13)`. -/
def v13PoissonTermCeil (c : PR) : ℕ :=
  let k := v13PoissonRadNum c
  let num := c.mult * c.w.1.natAbs * (30000000000000 + k)
  let den := 30000000000000 - k
  IK.cdivN num den

private theorem v13PoissonPoint_norm_le_rad
    {c : PR} (hcx : c.cx.2 = U) (hcy : c.cy.2 = U) :
    ‖v13PoissonPoint c‖ ≤ v13PoissonRad c := by
  have hU : (0 : ℝ) < (U : ℝ) := by norm_num [U]
  have hrad_nonneg : 0 ≤ v13PoissonRad c := by
    unfold v13PoissonRad
    positivity
  rw [← sq_le_sq₀ (norm_nonneg _) hrad_nonneg, Complex.sq_norm]
  unfold v13PoissonPoint v13PoissonRad IK.val
  simp only [Complex.normSq_mk, hcx, hcy, ← pow_two]
  rw [div_pow, div_pow, div_pow, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnat : c.cx.1.natAbs ^ 2 + c.cy.1.natAbs ^ 2 ≤ (v13PoissonRadNum c) ^ 2 := by
    unfold v13PoissonRadNum
    have h := Nat.lt_succ_sqrt (c.cx.1.natAbs ^ 2 + c.cy.1.natAbs ^ 2)
    nlinarith
  have hreal : ((c.cx.1.natAbs ^ 2 + c.cy.1.natAbs ^ 2 : ℕ) : ℝ) ≤
      ((v13PoissonRadNum c : ℝ)) ^ 2 := by
    exact_mod_cast hnat
  have hsq_eq : (c.cx.1 : ℝ) ^ 2 + (c.cy.1 : ℝ) ^ 2 =
      ((c.cx.1.natAbs ^ 2 + c.cy.1.natAbs ^ 2 : ℕ) : ℝ) := by
    norm_num [Int.natAbs_sq]
  linarith

private theorem cdivN_mul_ge (a b : ℕ) (hb : 0 < b) :
    a ≤ IK.cdivN a b * b := by
  simpa [Nat.mul_comm] using (cdivN_ge a hb)

private theorem v13PoissonTerm_le_ceil {c : PR} (hok : v13PoissonRowOK c = true) :
    (c.mult : ℝ) * IK.val c.w * (3 / 5 + v13PoissonRad c) /
        ((3 / 5) * (3 / 5 - v13PoissonRad c)) ≤
      (v13PoissonTermCeil c : ℝ) / (30000000000000 : ℝ) := by
  unfold v13PoissonRowOK at hok
  rcases of_decide_eq_true hok with ⟨_hcx, _hcy, hw2, hw1, hk⟩
  let k := v13PoissonRadNum c
  let R : ℕ := 30000000000000
  have hden_pos : 0 < R - k := Nat.sub_pos_of_lt hk
  have hk_le : k ≤ R := Nat.le_of_lt hk
  have hw_eq : IK.val c.w = (c.w.1.natAbs : ℝ) / (U : ℝ) := by
    unfold IK.val
    rw [hw2]
    congr 1
    have hi : (c.w.1.natAbs : ℤ) = c.w.1 := Int.natAbs_of_nonneg hw1
    have hiR := congrArg (fun n : ℤ => (n : ℝ)) hi.symm
    simpa only [Int.cast_natCast] using hiR
  have hrad_eq : v13PoissonRad c = (k : ℝ) / (U : ℝ) := rfl
  have hU_eq : (U : ℝ) = (5 / 3 : ℝ) * (R : ℝ) := by norm_num [U, R]
  have hdenR : ((R - k : ℕ) : ℝ) = (R : ℝ) - (k : ℝ) := Nat.cast_sub hk_le
  have hdenR_pos : (0 : ℝ) < (R : ℝ) - (k : ℝ) := by
    rw [← hdenR]
    exact_mod_cast hden_pos
  have hR_pos : (0 : ℝ) < (R : ℝ) := by norm_num [R]
  have hU_pos : (0 : ℝ) < (U : ℝ) := by norm_num [U]
  have hlhs_eq :
      (c.mult : ℝ) * IK.val c.w * (3 / 5 + v13PoissonRad c) /
          ((3 / 5) * (3 / 5 - v13PoissonRad c)) =
        (((c.mult * c.w.1.natAbs * (R + k) : ℕ) : ℝ) / ((R - k : ℕ) : ℝ)) / (R : ℝ) := by
    rw [hw_eq, hrad_eq, hdenR]
    push_cast
    rw [hU_eq]
    field_simp [hR_pos.ne', hdenR_pos.ne']
  rw [hlhs_eq]
  apply div_le_div_of_nonneg_right _ hR_pos.le
  rw [div_le_iff₀ (by exact_mod_cast hden_pos)]
  exact_mod_cast cdivN_mul_ge (c.mult * c.w.1.natAbs * (R + k)) (R - k) hden_pos

theorem v13PoissonMeasure_ballBound_of_rowOK
    {rows : List PR} (hok : rows.all v13PoissonRowOK = true) :
    VBallBound (v13PoissonMeasure rows)
      (((rows.map v13PoissonTermCeil).sum : ℝ) / (30000000000000 : ℝ)) := by
  have hρ : ∀ c ∈ rows, ‖v13PoissonPoint c‖ ≤ v13PoissonRad c ∧ v13PoissonRad c < 3 / 5 := by
    intro c hc
    have h := of_decide_eq_true (List.all_eq_true.mp hok c hc)
    refine ⟨v13PoissonPoint_norm_le_rad h.1 h.2.1, ?_⟩
    unfold v13PoissonRad
    have hk : (v13PoissonRadNum c : ℝ) < (30000000000000 : ℝ) := by
      exact_mod_cast h.2.2.2.2
    rw [div_lt_iff₀ (by norm_num [U])]
    norm_num [U]
    linarith
  have hw : ∀ c ∈ rows, 0 ≤ IK.val c.w := by
    intro c hc
    have h := of_decide_eq_true (List.all_eq_true.mp hok c hc)
    unfold IK.val
    rw [h.2.2.1]
    exact div_nonneg (by exact_mod_cast h.2.2.2.1) (by norm_num [U])
  refine vBallBound_of_le (v13PoissonMeasure_ballBound rows v13PoissonRad hρ hw) ?_
  have hsum :
      (rows.map fun c =>
        (c.mult : ℝ) * IK.val c.w * (3 / 5 + v13PoissonRad c) /
          ((3 / 5) * (3 / 5 - v13PoissonRad c))).sum ≤
      (rows.map fun c => (v13PoissonTermCeil c : ℝ) / (30000000000000 : ℝ)).sum := by
    induction rows with
    | nil => simp
    | cons c rs ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hok
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (v13PoissonTerm_le_ceil hok.1)
          (ih hok.2 (fun x hx => hρ x (by simp [hx]))
            (fun x hx => hw x (by simp [hx])))
  refine hsum.trans_eq ?_
  clear hok hρ hw hsum
  induction rows with
  | nil => simp
  | cons c rs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div, ih]

/-! ## 5. Exact `sigmaBudget` solve for `Az` -/

/-- Exact value of `Az` solving `vSigma q = sigmaBudget Ax Av Az`
(`v-analytic.tex:433-437`). -/
noncomputable def v13AzSolved (q : ℕ) (Ax Av : ℝ) : ℝ :=
  (vSigma q - (12 * Ax + 21 * Av + 77 / 4)) / (39 / 2)

theorem sigmaBudget_v13AzSolved (q : ℕ) (Ax Av : ℝ) :
    vSigma q = sigmaBudget Ax Av (v13AzSolved q Ax Av) := by
  unfold v13AzSolved sigmaBudget densityTransferBudget
    potentialModulusCoefficient xMass vMass zMass
  ring

theorem le_v13AzSolved_of_sigmaBudget_le
    {q : ℕ} {Ax Av Az0 : ℝ}
    (h : sigmaBudget Ax Av Az0 ≤ vSigma q) :
    Az0 ≤ v13AzSolved q Ax Av := by
  simp [v13AzSolved, sigmaBudget, densityTransferBudget,
    potentialModulusCoefficient, xMass, vMass, zMass] at h ⊢
  linarith

/-! ## 6. Concrete v13 sharp density constants and per-`q` certificates -/

/-- Exact maximum chain density `H_x` per base `q ∈ {2..7}` (`v-analytic.tex:412-415`). -/
def hxQ : ℕ → QF
  | 2 => (531665, 4074)
  | 3 => (77087, 582)
  | 4 => (272032, 2037)
  | 5 => (273458, 2037)
  | 6 => (274450, 2037)
  | 7 => (550357, 4074)
  | _ => (0, 1)

/-- Exact maximum chain density `H_v` per base `q ∈ {2..7}` (`v-analytic.tex:412-415`). -/
def hvQ : ℕ → QF
  | 2 => (44507, 291)
  | 3 => (622939, 4074)
  | 4 => (621547, 4074)
  | 5 => (619975, 4074)
  | 6 => (3188, 21)
  | 7 => (205699, 1358)
  | _ => (0, 1)

/-- Exact maximum chain density `H_z` per base `q ∈ {2..7}` (`v-analytic.tex:412-415`). -/
def hzQ : ℕ → QF
  | 2 => (3945, 92)
  | 3 => (26571, 889)
  | 4 => (318383, 13853)
  | 5 => (334975, 17928)
  | 6 => (173257, 11001)
  | 7 => (355036, 26077)
  | _ => (0, 1)

/-- Certified integer numerator of `P_q` in units of `1 / (3·10^13)`. -/
def pqCeilNum : ℕ → ℕ
  | 2 => 4376926416805127
  | 3 => 3744146213224490
  | 4 => 3344223381157974
  | 5 => 3062541981825943
  | 6 => 2850511256102003
  | 7 => 2683638010206851
  | _ => 0

noncomputable def v13Ax (q : ℕ) : ℝ := 2 * IK.val (hxQ q)
noncomputable def v13Av (q : ℕ) : ℝ := 2 * IK.val (hvQ q)
noncomputable def v13Az0 (q : ℕ) : ℝ :=
  2 * IK.val (hzQ q) + (pqCeilNum q : ℝ) / (30000000000000 : ℝ)
noncomputable def v13Az (q : ℕ) : ℝ := v13AzSolved q (v13Ax q) (v13Av q)

theorem v13Ax_nonneg (q : ℕ) : 0 ≤ v13Ax q := by
  by_cases hq : 2 ≤ q ∧ q ≤ 7
  · rcases hq with ⟨h2, h7⟩
    interval_cases q <;> norm_num [v13Ax, hxQ, IK.val]
  · rcases not_and_or.mp hq with hlt | hgt
    · interval_cases q <;> norm_num [v13Ax, hxQ, IK.val]
    · push_neg at hgt
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 8 := ⟨q - 8, by omega⟩
      norm_num [v13Ax, hxQ, IK.val]

theorem v13Av_nonneg (q : ℕ) : 0 ≤ v13Av q := by
  by_cases hq : 2 ≤ q ∧ q ≤ 7
  · rcases hq with ⟨h2, h7⟩
    interval_cases q <;> norm_num [v13Av, hvQ, IK.val]
  · rcases not_and_or.mp hq with hlt | hgt
    · interval_cases q <;> norm_num [v13Av, hvQ, IK.val]
    · push_neg at hgt
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 8 := ⟨q - 8, by omega⟩
      norm_num [v13Av, hvQ, IK.val]

theorem v13_sigmaBudget_le_vSigma {q : ℕ} (hq : SignedVBaseRange q) :
    sigmaBudget (v13Ax q) (v13Av q) (v13Az0 q) ≤ vSigma q := by
  rcases hq with ⟨h2, h7⟩
  interval_cases q <;>
    norm_num [sigmaBudget, densityTransferBudget, potentialModulusCoefficient,
      xMass, vMass, zMass, v13Ax, v13Av, v13Az0, hxQ, hvQ, hzQ, pqCeilNum,
      IK.val, vSigma]

theorem v13Az0_le_v13Az {q : ℕ} (hq : SignedVBaseRange q) :
    v13Az0 q ≤ v13Az q :=
  le_v13AzSolved_of_sigmaBudget_le (v13_sigmaBudget_le_vSigma hq)

theorem v13Az_nonneg {q : ℕ} (hq : SignedVBaseRange q) : 0 ≤ v13Az q := by
  have h0 : 0 ≤ v13Az0 q := by
    rcases hq with ⟨h2, h7⟩
    interval_cases q <;> norm_num [v13Az0, hzQ, pqCeilNum, IK.val]
  exact h0.trans (v13Az0_le_v13Az hq)

theorem v13_sigma_eq (q : ℕ) :
    vSigma q = sigmaBudget (v13Ax q) (v13Av q) (v13Az q) :=
  sigmaBudget_v13AzSolved q (v13Ax q) (v13Av q)

/-! ### Finite `decide +kernel` checks for `q = 2..7` -/

theorem q2_s5_checks :
    (chainCellsOK q2XHeader q2XEntries (hxQ 2) &&
     chainCellsOK q2YHeader q2YEntries (hvQ 2) &&
     chainCellsOK q2ZHeader q2ZEntries (hzQ 2) &&
     q2D.full.all v13PoissonRowOK &&
     decide ((q2D.full.map v13PoissonTermCeil).sum = pqCeilNum 2)) = true := by
  decide +kernel

theorem q3_s5_checks :
    (chainCellsOK q3XHeader q3XEntries (hxQ 3) &&
     chainCellsOK q3YHeader q3YEntries (hvQ 3) &&
     chainCellsOK q3ZHeader q3ZEntries (hzQ 3) &&
     q3D.full.all v13PoissonRowOK &&
     decide ((q3D.full.map v13PoissonTermCeil).sum = pqCeilNum 3)) = true := by
  decide +kernel

theorem q4_s5_checks :
    (chainCellsOK q4XHeader q4XEntries (hxQ 4) &&
     chainCellsOK q4YHeader q4YEntries (hvQ 4) &&
     chainCellsOK q4ZHeader q4ZEntries (hzQ 4) &&
     q4D.full.all v13PoissonRowOK &&
     decide ((q4D.full.map v13PoissonTermCeil).sum = pqCeilNum 4)) = true := by
  decide +kernel

theorem q5_s5_checks :
    (chainCellsOK q5XHeader q5XEntries (hxQ 5) &&
     chainCellsOK q5YHeader q5YEntries (hvQ 5) &&
     chainCellsOK q5ZHeader q5ZEntries (hzQ 5) &&
     q5D.full.all v13PoissonRowOK &&
     decide ((q5D.full.map v13PoissonTermCeil).sum = pqCeilNum 5)) = true := by
  decide +kernel

theorem q6_s5_checks :
    (chainCellsOK q6XHeader q6XEntries (hxQ 6) &&
     chainCellsOK q6YHeader q6YEntries (hvQ 6) &&
     chainCellsOK q6ZHeader q6ZEntries (hzQ 6) &&
     q6D.full.all v13PoissonRowOK &&
     decide ((q6D.full.map v13PoissonTermCeil).sum = pqCeilNum 6)) = true := by
  decide +kernel

theorem q7_s5_checks :
    (chainCellsOK q7XHeader q7XEntries (hxQ 7) &&
     chainCellsOK q7YHeader q7YEntries (hvQ 7) &&
     chainCellsOK q7ZHeader q7ZEntries (hzQ 7) &&
     q7D.full.all v13PoissonRowOK &&
     decide ((q7D.full.map v13PoissonTermCeil).sum = pqCeilNum 7)) = true := by
  decide +kernel

set_option maxRecDepth 2000000 in
private theorem raw_ball_bounds_of_checks
    {q : ℕ} (hq : SignedVBaseRange q) (D : V.EnergyCertI.IData)
    {hx_hdr hv_hdr hz_hdr : V.Q2Certificate.ChainHeader}
    {ex ev ez : List V.Q2Certificate.ChainEntry}
    {pp : List V.Q2Certificate.PoissonEntry}
    (hxp : D.xp = V.EnergyCertI.chainCP hx_hdr ex)
    (hvp : D.vp = V.EnergyCertI.chainCP hv_hdr ev)
    (hzp : D.zp = V.EnergyCertI.chainCP hz_hdr ez)
    (hchk :
      (chainCellsOK hx_hdr ex (hxQ q) &&
       chainCellsOK hv_hdr ev (hvQ q) &&
       chainCellsOK hz_hdr ez (hzQ q) &&
       D.full.all v13PoissonRowOK &&
       decide ((D.full.map
         v13PoissonTermCeil).sum = pqCeilNum q)) = true) :
    VBallBound (v13DecodedChainMeasure D.xp) (v13Ax q) ∧
      VBallBound (v13DecodedChainMeasure D.vp) (v13Av q) ∧
      VBallBound (v13DecodedChainMeasure D.zp + v13PoissonMeasure D.full) (v13Az q) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hx, hv⟩, hz⟩, hp⟩, hpsum⟩
  have hx0 := v13DecodedChainMeasure_ballBound_of_chainCellsOK hx
  have hx_bound : VBallBound (v13DecodedChainMeasure D.xp) (v13Ax q) := by
    rw [hxp]
    exact hx0
  have hv0 := v13DecodedChainMeasure_ballBound_of_chainCellsOK hv
  have hv_bound : VBallBound (v13DecodedChainMeasure D.vp) (v13Av q) := by
    rw [hvp]
    exact hv0
  have hz0 := v13DecodedChainMeasure_ballBound_of_chainCellsOK hz
  have hz_chain : VBallBound (v13DecodedChainMeasure D.zp) (2 * IK.val (hzQ q)) := by
    rw [hzp]
    exact hz0
  have hz_poi := v13PoissonMeasure_ballBound_of_rowOK hp
  rw [hpsum] at hz_poi
  exact ⟨hx_bound, hv_bound,
    vBallBound_of_le (vBallBound_add_toReal hz_chain hz_poi) (v13Az0_le_v13Az hq)⟩

private theorem q2_s5_ball_bounds {hq : SignedVBaseRange 2} :
    VBallBound (v13DecodedChainMeasure q2D.xp) (v13Ax 2) ∧
      VBallBound (v13DecodedChainMeasure q2D.vp) (v13Av 2) ∧
      VBallBound (v13DecodedChainMeasure q2D.zp + v13PoissonMeasure q2D.full)
        (v13Az 2) := by
  exact raw_ball_bounds_of_checks (q := 2) (hq := hq) (D := q2D)
    (hx_hdr := q2XHeader) (hv_hdr := q2YHeader) (hz_hdr := q2ZHeader)
    (ex := q2XEntries) (ev := q2YEntries) (ez := q2ZEntries)
    (pp := q2PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q2_s5_checks)

private theorem q3_s5_ball_bounds {hq : SignedVBaseRange 3} :
    VBallBound (v13DecodedChainMeasure q3D.xp) (v13Ax 3) ∧
      VBallBound (v13DecodedChainMeasure q3D.vp) (v13Av 3) ∧
      VBallBound (v13DecodedChainMeasure q3D.zp + v13PoissonMeasure q3D.full)
        (v13Az 3) := by
  exact raw_ball_bounds_of_checks (q := 3) (hq := hq) (D := q3D)
    (hx_hdr := q3XHeader) (hv_hdr := q3YHeader) (hz_hdr := q3ZHeader)
    (ex := q3XEntries) (ev := q3YEntries) (ez := q3ZEntries)
    (pp := q3PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q3_s5_checks)

private theorem q4_s5_ball_bounds {hq : SignedVBaseRange 4} :
    VBallBound (v13DecodedChainMeasure q4D.xp) (v13Ax 4) ∧
      VBallBound (v13DecodedChainMeasure q4D.vp) (v13Av 4) ∧
      VBallBound (v13DecodedChainMeasure q4D.zp + v13PoissonMeasure q4D.full)
        (v13Az 4) := by
  exact raw_ball_bounds_of_checks (q := 4) (hq := hq) (D := q4D)
    (hx_hdr := q4XHeader) (hv_hdr := q4YHeader) (hz_hdr := q4ZHeader)
    (ex := q4XEntries) (ev := q4YEntries) (ez := q4ZEntries)
    (pp := q4PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q4_s5_checks)

private theorem q5_s5_ball_bounds {hq : SignedVBaseRange 5} :
    VBallBound (v13DecodedChainMeasure q5D.xp) (v13Ax 5) ∧
      VBallBound (v13DecodedChainMeasure q5D.vp) (v13Av 5) ∧
      VBallBound (v13DecodedChainMeasure q5D.zp + v13PoissonMeasure q5D.full)
        (v13Az 5) := by
  exact raw_ball_bounds_of_checks (q := 5) (hq := hq) (D := q5D)
    (hx_hdr := q5XHeader) (hv_hdr := q5YHeader) (hz_hdr := q5ZHeader)
    (ex := q5XEntries) (ev := q5YEntries) (ez := q5ZEntries)
    (pp := q5PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q5_s5_checks)

private theorem q6_s5_ball_bounds {hq : SignedVBaseRange 6} :
    VBallBound (v13DecodedChainMeasure q6D.xp) (v13Ax 6) ∧
      VBallBound (v13DecodedChainMeasure q6D.vp) (v13Av 6) ∧
      VBallBound (v13DecodedChainMeasure q6D.zp + v13PoissonMeasure q6D.full)
        (v13Az 6) := by
  exact raw_ball_bounds_of_checks (q := 6) (hq := hq) (D := q6D)
    (hx_hdr := q6XHeader) (hv_hdr := q6YHeader) (hz_hdr := q6ZHeader)
    (ex := q6XEntries) (ev := q6YEntries) (ez := q6ZEntries)
    (pp := q6PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q6_s5_checks)

private theorem q7_s5_ball_bounds {hq : SignedVBaseRange 7} :
    VBallBound (v13DecodedChainMeasure q7D.xp) (v13Ax 7) ∧
      VBallBound (v13DecodedChainMeasure q7D.vp) (v13Av 7) ∧
      VBallBound (v13DecodedChainMeasure q7D.zp + v13PoissonMeasure q7D.full)
        (v13Az 7) := by
  exact raw_ball_bounds_of_checks (q := 7) (hq := hq) (D := q7D)
    (hx_hdr := q7XHeader) (hv_hdr := q7YHeader) (hz_hdr := q7ZHeader)
    (ex := q7XEntries) (ev := q7YEntries) (ez := q7ZEntries)
    (pp := q7PoissonPrefix) (hxp := by rfl) (hvp := by rfl) (hzp := by rfl)
    (hchk := q7_s5_checks)

/-- Uniform S5 package: for any decoded v13 reference source `R : V13DecodedRows q`
and normalization `N`, `v13Ax q`, `v13Av q`, `v13Az q` satisfy nonnegativity,
the three `VBallBound` obligations on `(v13RefMeasure R N).μ{x,v,z}`, and the
exact equality `vSigma q = sigmaBudget (v13Ax q) (v13Av q) (v13Az q)`. -/
theorem v13RefMeasure_ball_and_sigma
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) :
    0 ≤ v13Ax q ∧ 0 ≤ v13Av q ∧ 0 ≤ v13Az q ∧
      VBallBound (v13RefMeasure R N).μx (v13Ax q) ∧
      VBallBound (v13RefMeasure R N).μv (v13Av q) ∧
      VBallBound (v13RefMeasure R N).μz (v13Az q) ∧
      vSigma q = sigmaBudget (v13Ax q) (v13Av q) (v13Az q) := by
  refine ⟨v13Ax_nonneg q, v13Av_nonneg q, v13Az_nonneg hq, ?_⟩
  change VBallBound (v13DecodedChainMeasure R.data.xp) (v13Ax q) ∧
    VBallBound (v13DecodedChainMeasure R.data.vp) (v13Av q) ∧
    VBallBound (v13DecodedChainMeasure R.data.zp + v13PoissonMeasure R.data.full) (v13Az q) ∧
    vSigma q = sigmaBudget (v13Ax q) (v13Av q) (v13Az q)
  have hballs :
      VBallBound (v13DecodedChainMeasure R.data.xp) (v13Ax q) ∧
      VBallBound (v13DecodedChainMeasure R.data.vp) (v13Av q) ∧
      VBallBound (v13DecodedChainMeasure R.data.zp + v13PoissonMeasure R.data.full)
        (v13Az q) := by
    rcases R.source with ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩ |
        ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩ <;> rw [hD]
    · exact q2_s5_ball_bounds (hq := hq)
    · exact q4_s5_ball_bounds (hq := hq)
    · exact q5_s5_ball_bounds (hq := hq)
    · exact q7_s5_ball_bounds (hq := hq)
    · exact q6_s5_ball_bounds (hq := hq)
    · exact q3_s5_ball_bounds (hq := hq)
  exact ⟨hballs.1, hballs.2.1, hballs.2.2, v13_sigma_eq q⟩

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13ChainMeasureComplex_ballBound_of_adjacent
#print axioms Li2Lean.B3.v13PoissonMeasure_ballBound
#print axioms Li2Lean.B3.v13RefMeasure_ball_and_sigma
