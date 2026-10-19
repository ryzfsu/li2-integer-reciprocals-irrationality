/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13ReferenceMeasure

namespace Li2Lean.B3

open MeasureTheory Set
open scoped ENNReal

private lemma ofReal_two_mul_pos {D t : ℝ} (hD : 0 ≤ D) (ht : 0 < t) :
    ENNReal.ofReal (2 * D * t) = ENNReal.ofReal D * ENNReal.ofReal (2 * t) := by
  rw [← ENNReal.ofReal_mul hD]
  congr 1
  ring

private lemma real_preimage_ball_subset (w : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.ofReal ⁻¹' Metric.ball w t ⊆ Set.Ioo (w.re - t) (w.re + t) := by
  intro x hx
  have hxnorm : ‖(x : ℂ) - w‖ < t := by
    change dist (x : ℂ) w < t at hx
    rw [Complex.dist_eq] at hx
    exact hx
  have hreal : |x - w.re| ≤ ‖(x : ℂ) - w‖ := by
    simpa [Complex.ofReal_sub, Complex.normSq_apply, Real.norm_eq_abs] using
      (Complex.abs_re_le_norm ((x : ℂ) - w))
  have habs : |x - w.re| < t := lt_of_le_of_lt hreal hxnorm
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  constructor <;> linarith

private lemma chain_cell_ball_le {c : V13ChainCell} {w : ℂ} {t D : ℝ}
    (ht : 0 < t) (hc0 : 0 ≤ c.density) (hcD : c.density ≤ D) (hD : 0 ≤ D) :
    (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right))
        (Complex.ofReal ⁻¹' Metric.ball w t) ≤ ENNReal.ofReal (2 * D * t) := by
  have hmeas : MeasurableSet (Complex.ofReal ⁻¹' Metric.ball w t) := by
    exact Metric.isOpen_ball.measurableSet.preimage Complex.continuous_ofReal.measurable
  rw [Measure.smul_apply, Measure.restrict_apply hmeas]
  have hsub : (Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioc c.left c.right ⊆
      Ioo (w.re - t) (w.re + t) := by
    intro x hx
    exact real_preimage_ball_subset w ht hx.1
  have hvol : volume ((Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioc c.left c.right) ≤
      ENNReal.ofReal (2 * t) := by
    calc
      volume ((Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioc c.left c.right) ≤
          volume (Ioo (w.re - t) (w.re + t)) := measure_mono hsub
      _ = ENNReal.ofReal (2 * t) := by
        rw [Real.volume_Ioo]
        congr 1
        ring
  have hcoef : ENNReal.ofReal c.density ≤ ENNReal.ofReal D :=
    ENNReal.ofReal_le_ofReal hcD
  calc
    ENNReal.ofReal c.density *
          volume ((Complex.ofReal ⁻¹' Metric.ball w t) ∩ Ioc c.left c.right) ≤
        ENNReal.ofReal D * ENNReal.ofReal (2 * t) := by
      exact mul_le_mul hcoef hvol (by positivity) (by positivity)
    _ = ENNReal.ofReal (2 * D * t) := by
      calc
        ENNReal.ofReal D * ENNReal.ofReal (2 * t) =
            ENNReal.ofReal (D * (2 * t)) := (ENNReal.ofReal_mul hD).symm
        _ = ENNReal.ofReal (2 * D * t) := by congr 1 <;> ring

private theorem chain_measure_ball_le (cells : List V13ChainCell)
    (w : ℂ) (t D : ℝ) (ht : 0 < t) (hD : 0 ≤ D)
    (hc0 : ∀ c ∈ cells, 0 ≤ c.density)
    (hcD : ∀ c ∈ cells, c.density ≤ D) :
    v13ChainMeasure cells (Complex.ofReal ⁻¹' Metric.ball w t) ≤
      ENNReal.ofReal (2 * D * cells.length * t) := by
  induction cells generalizing w t D with
  | nil =>
      simp [v13ChainMeasure]
  | cons c cells ih =>
      have hc0' : 0 ≤ c.density := hc0 c (by simp)
      have hcD' : c.density ≤ D := hcD c (by simp)
      have hrest0 : ∀ c ∈ cells, 0 ≤ c.density := by
        intro c hc
        exact hc0 c (by simp [hc])
      have hrestD : ∀ c ∈ cells, c.density ≤ D := by
        intro c hc
        exact hcD c (by simp [hc])
      unfold v13ChainMeasure
      change (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
          v13ChainMeasure cells) (Complex.ofReal ⁻¹' Metric.ball w t) ≤ _
      calc
        (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cells) (Complex.ofReal ⁻¹' Metric.ball w t) ≤
          ENNReal.ofReal (2 * D * t) + ENNReal.ofReal (2 * D * cells.length * t) := by
            exact add_le_add (chain_cell_ball_le ht hc0' hcD' hD)
              (ih w t D ht hD hrest0 hrestD)
        _ = ENNReal.ofReal (2 * D * (c :: cells).length * t) := by
          rw [List.length_cons]
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * D * t)
            (by positivity : 0 ≤ 2 * D * cells.length * t)]
          congr 1
          push_cast
          ring

theorem v13ChainMeasure_isFinite (cells : List V13ChainCell) :
    IsFiniteMeasure (v13ChainMeasure cells) := by
  rw [isFiniteMeasure_iff]
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cells ih =>
      unfold v13ChainMeasure
      have hcoef : ENNReal.ofReal c.density < ∞ := ENNReal.ofReal_lt_top
      have hvol : volume (Ioc c.left c.right) < ∞ := by
        simp [Real.volume_Ioc]
      have hsmul :
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) univ < ∞ := by
        rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
          univ_inter, Real.volume_Ioc]
        exact ENNReal.mul_lt_top hcoef (by simpa using hvol)
      have hi : v13ChainMeasure cells univ < ∞ := ih
      exact (ENNReal.add_lt_top.mpr ⟨hsmul, hi⟩)

theorem v13ChainMeasureComplex_isFinite (cells : List V13ChainCell) :
    IsFiniteMeasure (v13ChainMeasureComplex cells) := by
  rw [isFiniteMeasure_iff]
  rw [v13ChainMeasureComplex,
    Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
  simpa using (show v13ChainMeasure cells (Complex.ofReal ⁻¹' (Set.univ : Set ℂ)) < ∞ by
    simpa using (v13ChainMeasure_isFinite cells).measure_univ_lt_top)

theorem v13ChainMeasureComplex_ballBound_of_density
    (cells : List V13ChainCell) (D : ℝ)
    (hc0 : ∀ c ∈ cells, 0 ≤ c.density)
    (hcD : ∀ c ∈ cells, c.density ≤ D) (hD : 0 ≤ D) :
    VBallBound (v13ChainMeasureComplex cells) (2 * D * cells.length) := by
  intro w t ht
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.continuous_ofReal.measurable Metric.isOpen_ball.measurableSet]
  have h := chain_measure_ball_le cells w t D ht hD hc0 hcD
  have htop : ENNReal.ofReal (2 * D * cells.length * t) ≠ ∞ := by
    simp
  have hreal := ENNReal.toReal_mono htop h
  simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * D * cells.length * t)] using hreal

end Li2Lean.B3
