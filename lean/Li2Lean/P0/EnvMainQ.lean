/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvAndreiefQ
import Li2Lean.P0.PositiveBaseEnvelopeMatrix
import Li2Lean.P0.PositiveBaseFrequencyTailFactor
import Li2Lean.P0.PositiveBaseEnvelopeCore

/-!
# Signed coefficient envelope for positive integer bases

The actual q-dependent frequency truncations are bounded by the q contour
envelope using row splitting, block reduction and continuous Andreief.
The source-bank limit and the concrete frequency-tail bound give the full
signed coefficient estimate.
-/

open Finset MeasureTheory Filter Topology

namespace Li2Lean.P0.Env

noncomputable section
open Li2Lean.P0.PositiveBase

/-- The integrand of `norm_det_pinnedD_le`, before the pinned and frequency factors. -/
def contourIntegrandQ (q m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) : ℝ :=
  (∏ l, ‖p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m (u l))‖) *
    ‖contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l))‖ *
    ‖(contourQMinors S h4 hSI r.val r.property.1 (fun l => p0EllipsePoint m (u l))).2.2‖ *
    ∏ l, contourArcDensity m (u l)

theorem envelopeTermQ_eq (q m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    qEnvelopeTerm q m h4 S hSI r u =
      ((∏ l, qFrequencyWeightRealQ q (m / 2) (r.val l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
          (fun j => ((r.val j : ℕ) : ℂ))‖) *
        ((∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) * contourIntegrandQ q m S h4 hSI r u) := by
  simp only [qEnvelopeTerm, qContourQValue, contourIntegrandQ, norm_mul]
  have h1 : (contourQMinors S h4 hSI r.val r.property.1
      (fun l => p0EllipsePoint m (u l))).1 =
      contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l)) := rfl
  have h2 : (contourQMinors S h4 hSI r.val r.property.1
      (fun l => p0EllipsePoint m (u l))).2.1 =
      cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
        (fun j => ((r.val j : ℕ) : ℂ)) := rfl
  rw [h1, h2]
  simp only [qFrequencyWeightRealQ, qFrequencyWeightReal]
  ring

theorem tOf_image_rowIndexQ (m : ℕ) (t : Finset (Fin m)) :
    tOf m (t.image (rowIndex m)) = t := by
  ext i
  simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    rw [rowIndex_injective m hji] at hj
    exact hj
  · intro hi; exact ⟨i, hi, rfl⟩

/-- Contour bound for `[K_{R,J}; C]`, summed over pinned sets. -/
theorem norm_det_YmatQ_le (q : ℕ) (hq : 2 ≤ q) (hq11 : q ≤ 11) (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (r : IncreasingFrequencyTuple (m / 2) m) :
    ‖(YmatQ q m r.val).det‖ ≤ ∑ S ∈ (Iset m).powerset,
      if hSI : S ⊆ Iset m then
        (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) * (((m - S.card).factorial : ℝ)⁻¹ *
          ∫ u, contourIntegrandQ q m S h4 hSI r u
            ∂(ContourKit.productMeasure contourParameterMeasure))
      else 0 := by
  classical
  rw [det_split_rows (YmatQ q m r.val) (PpQ q m) (QpQ q m) (YmatQ_inr_split q m ⟨by exact_mod_cast hq, by exact_mod_cast hq11⟩ h4 r.val)]
  refine (norm_sum_le _ _).trans ?_
  have hre : (∑ t : Finset (Fin m), ‖(splitMat (YmatQ q m r.val) (PpQ q m) (QpQ q m) t).det‖) =
      ∑ S ∈ (Iset m).powerset,
        ‖(splitMat (YmatQ q m r.val) (PpQ q m) (QpQ q m) (tOf m S)).det‖ := by
    symm
    apply Finset.sum_nbij' (fun S => tOf m S) (fun t => t.image (rowIndex m))
    · intro S _; exact Finset.mem_univ _
    · intro t _
      rw [Finset.mem_powerset]
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · intro S hS; exact tOf_image m S (Finset.mem_powerset.mp hS)
    · intro t _; exact tOf_image_rowIndexQ m t
    · intro S _; rfl
  rw [hre]
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  rw [dite_eq_left hSI, norm_det_splitQ_eq q m hq hm h4 S hSI r.val, mul_comm]
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  exact mul_le_mul_of_nonneg_left (norm_det_pinnedD_leQ q m hm h4 S hSI r.val r.property.1)
    (Finset.prod_nonneg (fun a _ => mul_nonneg (Real.log_nonneg hqR)
      (by unfold qUReal; positivity)))

/-- The truncated determinants are bounded by the finite envelope `qE q m H`. -/
theorem norm_det_truncQ_le_E (q : ℕ) (hq : 2 ≤ q) (hq11 : q ≤ 11) (m H : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    ‖(truncMatrixQ q m H).det‖ ≤ qE q m H h4 := by
  classical
  refine (norm_det_truncQ_le q m H).trans ?_
  set c : FrequencyCutoff.IncreasingTuple (m / 2) m → ℝ := fun r =>
    (∏ l, qFrequencyWeightRealQ q (m / 2) (r.val l)) *
      ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) (fun j => ((r.val j : ℕ) : ℂ))‖
  have hc0 : ∀ r, 0 ≤ c r := fun r => mul_nonneg
    (Finset.prod_nonneg (fun l _ => by unfold qFrequencyWeightRealQ; positivity)) (norm_nonneg _)
  have step1 : (∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
      (∏ l, qFrequencyWeightRealQ q (m / 2) (r.val l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
            (fun j => ((r.val j : ℕ) : ℂ))‖ * ‖(YmatQ q m r.val).det‖) ≤
      ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H, c r *
        ∑ S ∈ (Iset m).powerset,
          if hSI : S ⊆ Iset m then
            (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) * (((m - S.card).factorial : ℝ)⁻¹ *
              ∫ u, contourIntegrandQ q m S h4 hSI r u
                ∂(ContourKit.productMeasure contourParameterMeasure))
          else 0 := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (norm_det_YmatQ_le q hq hq11 m hm h4 r) (hc0 r)
  refine step1.trans (le_of_eq ?_)
  unfold qE
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  have hint : ∀ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
      Integrable (fun u => qEnvelopeTerm q m h4 S hSI r u)
        (ContourKit.productMeasure contourParameterMeasure) := fun r _ =>
    FrequencyRegularity.integrable_parameter
      (continuous_qEnvelopeTerm q m hm h4 S hSI r)
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [envelopeTermQ_eq q m h4 S hSI r]
  rw [integral_const_mul, integral_const_mul]
  ring

end

end Li2Lean.P0.Env

namespace Li2Lean.P0.Env

open Li2Lean.P0.PositiveBase

/-- Every finite q-cutoff lies below the literal full q-envelope. -/
theorem qE_le_qEInfinity (q m H : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (hfin : qFullEnvelope q m h4 ≠ ⊤) :
    qE q m H h4 ≤ qEInfinity q m h4 := by
  have hle : qFiniteEnvelope q m H h4 ≤ qFullEnvelope q m h4 := by
    rw [qFullEnvelope_eq_iSup_qFiniteEnvelope q m hm h4]
    exact le_iSup (fun K => qFiniteEnvelope q m K h4) H
  have h' := ENNReal.toReal_mono hfin hle
  rw [qFiniteEnvelope_eq_ofReal q m H hm hq h4,
    ENNReal.toReal_ofReal (qE_nonneg q m H hq h4)] at h'
  exact h'

/-- The q full envelope is finite by the concrete frequency replacement producer. -/
theorem qFullEnvelope_ne_top_of_cutoff (q m : ℕ) (hm : 0 < m) (hq : 2 ≤ q)
    (h4 : 4 ∣ m) : qFullEnvelope q m h4 ≠ ⊤ := by
  have hfinite : ∀ H : ℕ, 20 * m ≤ H →
      qE q m H h4 ≤
        (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
    intro H hH
    exact qE_le_of_finiteQSum_le q m H (20 * m) hm hq h4
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m)
      (fun S hSI u =>
        Li2Lean.AllNAssembly.qFiniteQSum_cutoff_of_frequency_replacement
          q m H hm hq h4 hH S hSI u)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (qFullEnvelope_le_of_finiteCutoff q m hm hq h4 _ hfinite)

/-- The signed q coefficient is bounded by the literal q-envelope. -/
theorem norm_qGmBeta_le_qEInfinity
    (q : ℕ) (hq2 : 2 ≤ q) (hq11 : q ≤ 11)
    (m : ℕ) (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    ‖Li2Lean.P0.PositiveBase.qGmBeta q m‖ ≤ qEInfinity q m h4 := by
  have hm : 0 < m := by omega
  have hfin : qFullEnvelope q m h4 ≠ ⊤ :=
    qFullEnvelope_ne_top_of_cutoff q m hm hq2 h4
  have hbound : ∀ H : ℕ, ‖(truncMatrixQ q m H).det‖ ≤ qEInfinity q m h4 := by
    intro H
    exact (norm_det_truncQ_le_E q hq2 hq11 m H hm h4).trans
      (qE_le_qEInfinity q m H hm hq2 h4 hfin)
  have hlim : Tendsto (fun H => (truncMatrixQ q m H).det) atTop
      (𝓝 (Li2Lean.P0.PositiveBase.qGmBeta q m)) := by
    rw [Li2Lean.P0.PositiveBase.qGmBeta_eq_det_XbetaQ q m h4,
      det_XbetaQ_eq_det_XinfQ (q : ℤ) m hm]
    exact tendsto_det_truncMatrixQ q m hq2
  have hnorm : Tendsto (fun H => ‖(truncMatrixQ q m H).det‖) atTop
      (𝓝 ‖Li2Lean.P0.PositiveBase.qGmBeta q m‖) :=
    (continuous_norm.tendsto _).comp hlim
  exact le_of_tendsto' hnorm hbound

end Li2Lean.P0.Env
