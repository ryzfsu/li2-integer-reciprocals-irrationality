/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q4ReferenceVSupport
import Li2Lean.B3.V13ChainLogEndpoint
import Li2Lean.B3.ReferenceMeasureSupportCircle
import Li2Lean.V.EnergyCertI.IFieldEval
import Li2Lean.V.EnergyCertI.Consts
import Li2Lean.V.EnergyCertI.ISoundEval

namespace Li2Lean

noncomputable section

namespace V.EnergyCertI

open IK

/-- Finite q=4 endpoint/field checks from the v13 integer evaluator. -/
theorem q4Endpoint_check_local :
    (hiLe (exUB fieldMode q4D 4) (exQ 4) && hiLe (evUB fieldMode q4D 4) (evQ 4) &&
      qlt (exQ 4) (kxQ 4) && qlt (evQ 4) (kvQ 4)) = true := by
  decide +kernel

end V.EnergyCertI

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK
open MeasureTheory Set
open scoped ENNReal

set_option maxHeartbeats 2000000 in
private theorem q4_x_cells_data :
    ∀ c ∈ v13ChainCells q4D.xp,
      0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density := by
  norm_num [q4D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    q4XHeader, q4XEntries, chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.correctedLength,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]

set_option maxHeartbeats 2000000 in
private theorem q4_x_rows_pos :
    ∀ p ∈ q4D.xp, 0 < p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2 := by
  norm_num [q4D, mkIData, chainCP, q4XHeader, q4XEntries,
    chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.correctedLength,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]

theorem q4_x_shift_integral_eq_jump_sum (δ : ℝ) (hδ : 0 < δ) :
    (∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure (v13ChainCells q4D.xp)) =
      ((v13ChainCells q4D.xp).map fun c => c.density *
        (LogSegment.primitive (c.right + δ) -
          LogSegment.primitive (c.left + δ))).sum := by
  have hb : ∀ c ∈ v13ChainCells q4D.xp,
      0 ≤ c.left ∧ c.left ≤ c.right := by
    intro c hc
    exact ⟨(q4_x_cells_data c hc).1, (q4_x_cells_data c hc).2.1⟩
  have hd : ∀ c ∈ v13ChainCells q4D.xp, 0 ≤ c.density := by
    intro c hc
    exact (q4_x_cells_data c hc).2.2
  exact integral_v13ChainMeasure_log_shift (v13ChainCells q4D.xp) δ hδ hb hd

set_option maxHeartbeats 2000000 in
private theorem q4_x_jump_val_sum_zero :
    (q4D.xp.map fun p => IK.val p.J).sum = 0 := by
  norm_num [q4D, mkIData, chainCP, q4XHeader, q4XEntries,
    chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.correctedLength,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]

private theorem list_sum_mul_sub_const {α : Type*} (xs : List α)
    (a : ℝ) (u v : α → ℝ) :
    (xs.map fun x => v x * (a - u x)).sum =
      (xs.map fun x => v x * a).sum - (xs.map fun x => v x * u x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, mul_sub]
      have ih' : (xs.map fun x => v x * a - v x * u x).sum =
          (xs.map fun x => v x * a).sum - (xs.map fun x => v x * u x).sum := by
        simpa only [mul_sub] using ih
      rw [ih']
      ring

private theorem q4_x_jpos_mem :
    IV.mem (jPos fieldMode q4D.xp)
      (-(q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + (1 / 250 : ℝ))).sum) := by
  unfold jPos
  apply IK.neg_mem
  apply IK.sumI_map_mem
  intro p hp
  have hrow := q4_x_rows_pos p hp
  have heden : 0 < p.e.2 := hrow.2.1
  have hjden : 0 < p.J.2 := hrow.2.2
  have hdden : 0 < DELTA.2 := by norm_num [DELTA]
  have hsden : 0 < (qadd p.e DELTA).2 := by
    simp only [qadd]
    exact Nat.mul_pos heden hdden
  have hsI := V.EnergyCertI.hsI_mem (md := fieldMode)
    (s := qadd p.e DELTA) hsden
  have hsmul := IK.smulQ_mem hjden hsI
  have hval := IK.val_qadd heden hdden
  have hdelta : IK.val DELTA = (1 / 250 : ℝ) := by
    norm_num [DELTA, IK.val]
  have hpos : 0 < IK.val p.e + (1 / 250 : ℝ) := by
    have hepos : 0 < IK.val p.e := by
      unfold IK.val
      exact div_pos (by exact_mod_cast hrow.1) (by exact_mod_cast heden)
    linarith
  have heq : IK.val p.J *
      (IK.val (qadd p.e DELTA) * Real.log |IK.val (qadd p.e DELTA)| -
        IK.val (qadd p.e DELTA)) =
      IK.val p.J * LogSegment.primitive (IK.val p.e + (1 / 250 : ℝ)) := by
    rw [hval, hdelta, LogSegment.primitive, abs_of_pos hpos]
    ring
  exact IK.mem_of_eq hsmul heq

theorem q4_x_shift_integral_eq_closed_jump_sum (δ : ℝ) (hδ : 0 < δ) :
    (∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure (v13ChainCells q4D.xp)) =
      - (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + δ)).sum := by
  rw [q4_x_shift_integral_eq_jump_sum δ hδ]
  change ((v13ChainCellsAux 0 q4D.xp).map fun c => c.density *
      (LogSegment.primitive (c.right + δ) -
        LogSegment.primitive (c.left + δ))).sum = _
  rw [v13ChainCellsAux_log_primitive_sum]
  have hconst : (q4D.xp.map fun p => IK.val p.J *
      LogSegment.primitive (v13ChainRowsLast q4D.xp + δ)).sum = 0 := by
    calc
      _ = (q4D.xp.map fun p => IK.val p.J).sum *
          LogSegment.primitive (v13ChainRowsLast q4D.xp + δ) := by
            simp [List.sum_map_mul_right]
      _ = 0 := by rw [q4_x_jump_val_sum_zero]; simp
  simp only [zero_mul]
  have hsplit : (q4D.xp.map fun p => IK.val p.J *
      (LogSegment.primitive (v13ChainRowsLast q4D.xp + δ) -
        LogSegment.primitive (IK.val p.e + δ))).sum =
      (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (v13ChainRowsLast q4D.xp + δ)).sum -
      (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + δ)).sum := by
    exact list_sum_mul_sub_const q4D.xp
      (LogSegment.primitive (v13ChainRowsLast q4D.xp + δ))
      (fun p => LogSegment.primitive (IK.val p.e + δ))
      (fun p => IK.val p.J)
  rw [hsplit, hconst]
  ring

private theorem q4_x_log_integrable (w : ℂ)
    (hsep : ∀ c ∈ v13ChainCells q4D.xp, ∀ x ∈ Icc c.left c.right,
      w ≠ Complex.ofReal x) :
    Integrable (fun z : ℂ => Real.log ‖w - z‖)
      (v13ChainMeasureComplex (v13ChainCells q4D.xp)) := by
  have hreal : Integrable (fun x : ℝ => Real.log ‖w - Complex.ofReal x‖)
      (v13ChainMeasure (v13ChainCells q4D.xp)) := by
    apply integrable_v13ChainMeasure_of_continuousOn_cells
    intro c hc
    have hsub : ContinuousOn (fun x : ℝ => w - Complex.ofReal x)
        (Icc c.left c.right) :=
      continuousOn_const.sub Complex.continuous_ofReal.continuousOn
    have hnorm : ContinuousOn (fun x : ℝ => ‖w - Complex.ofReal x‖)
        (Icc c.left c.right) := continuous_norm.comp_continuousOn hsub
    have hne : Set.MapsTo (fun x : ℝ => ‖w - Complex.ofReal x‖)
        (Icc c.left c.right) ({0} : Set ℝ)ᶜ := by
      intro x hx
      apply norm_ne_zero_iff.mpr
      exact sub_ne_zero.mpr (hsep c hc x hx)
    exact Real.continuousOn_log.comp hnorm hne
  let emb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap := (emb.integrable_map_iff
      (g := fun z : ℂ => Real.log ‖w - z‖)).mpr hreal
  simpa [v13ChainMeasureComplex] using hmap

private theorem q4_x_support_ae :
    ∀ᵐ x ∂v13ChainMeasure (v13ChainCells q4D.xp),
      x ∈ Icc ((3349364905389 : ℝ) / (5 * 10 ^ 13)) 1 := by
  rw [ae_iff]
  apply v13ChainMeasure_outside_Icc
  intro c hc
  exact v13_q4_x_bounds c hc

private theorem q4_v_support_ae (N : q4ReferenceNormalizationGoal) :
    ∀ᵐ t ∂(q4ReferenceMeasure N).μv,
      t ∈ Complex.ofReal '' Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  exact q4ReferenceMeasure_v_support_full N

private theorem q4_v_cross_integrable (N : q4ReferenceNormalizationGoal)
    (w : ℂ) (hw : ‖w‖ ≤ (1 / 250 : ℝ)) :
    Integrable (fun t : ℂ => Real.log ‖(4 : ℂ) + w * t‖)
      (q4ReferenceMeasure N).μv := by
  let μ := (q4ReferenceMeasure N).μv
  have hfinite : μ Set.univ ≠ ⊤ := (q4ReferenceMeasure N).finite_v
  letI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hfinite⟩
  have hcontinuous : Continuous (fun t : ℂ => (4 : ℂ) + w * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hmeas : Measurable (fun t : ℂ => Real.log ‖(4 : ℂ) + w * t‖) :=
    Real.measurable_log.comp hcontinuous.norm.measurable
  have hstrong : AEStronglyMeasurable
      (fun t : ℂ => Real.log ‖(4 : ℂ) + w * t‖) μ := hmeas.aestronglyMeasurable
  apply Integrable.mono' (integrable_const (Real.log 5)) hstrong
  filter_upwards [q4_v_support_ae N] with t ht
  rcases ht with ⟨x, hx, rfl⟩
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hwt : ‖w * Complex.ofReal x‖ ≤ (1 / 250 : ℝ) := by
    calc
      ‖w * Complex.ofReal x‖ = ‖w‖ * ‖Complex.ofReal x‖ := norm_mul _ _
      _ = ‖w‖ * x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
      _ ≤ 1 / 250 := by nlinarith [hw, hx1]
  have hlow : 1 ≤ ‖(4 : ℂ) + w * Complex.ofReal x‖ := by
    have hcancel : ((4 : ℂ) + w * Complex.ofReal x) -
        (w * Complex.ofReal x) = (4 : ℂ) := by abel
    have htriangle := norm_sub_le ((4 : ℂ) + w * Complex.ofReal x)
      (w * Complex.ofReal x)
    have hfive : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [hcancel, hfive] at htriangle
    nlinarith
  have hupp : ‖(4 : ℂ) + w * Complex.ofReal x‖ ≤ 5 := by
    calc
      ‖(4 : ℂ) + w * Complex.ofReal x‖ ≤ ‖(4 : ℂ)‖ + ‖w * Complex.ofReal x‖ :=
        norm_add_le _ _
      _ ≤ 4 + 1 / 250 := by rw [show ‖(4 : ℂ)‖ = 4 by norm_num]; nlinarith [hwt]
      _ ≤ 5 := by norm_num
  have hlog0 : 0 ≤ Real.log ‖(4 : ℂ) + w * Complex.ofReal x‖ :=
    Real.log_nonneg hlow
  have hnormpos : 0 < ‖(4 : ℂ) + w * Complex.ofReal x‖ := by linarith
  have hlog6 : Real.log ‖(4 : ℂ) + w * Complex.ofReal x‖ ≤ Real.log 5 :=
    Real.log_le_log hnormpos hupp
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0]
  exact hlog6

theorem q4ReferenceMeasure_x_endpoint_disk
    (N : q4ReferenceNormalizationGoal) (w : ℂ)
    (hw0 : 0 < ‖w‖) (hw : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldX (q4ReferenceMeasure N) w ≤ (vEx 4 : ℝ) := by
  let δ : ℝ := 1 / 250
  have hδ : 0 < δ := by norm_num [δ]
  have hxrows : ∀ c ∈ v13ChainCells q4D.xp,
      ((3349364905389 : ℝ) / (5 * 10 ^ 13)) ≤ c.left ∧ c.right ≤ 1 :=
    v13_q4_x_bounds
  have hxmem : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells q4D.xp),
      x ∈ Icc ((3349364905389 : ℝ) / (5 * 10 ^ 13)) 1 := q4_x_support_ae
  have hae_nonneg : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells q4D.xp), 0 ≤ x := by
    filter_upwards [hxmem] with x hx
    exact le_trans (by norm_num : (0 : ℝ) ≤ (3349364905389 : ℝ) / (5 * 10 ^ 13)) hx.1
  have hsep : ∀ c ∈ v13ChainCells q4D.xp, ∀ x ∈ Icc c.left c.right,
      w ≠ Complex.ofReal x := by
    intro c hc x hx heq
    have hcell := hxrows c hc
    have hxlower : (3349364905389 : ℝ) / (5 * 10 ^ 13) ≤ x := le_trans hcell.1 hx.1
    have hnorm : ‖w‖ = x := by
      have hn := congrArg norm heq
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤
          (3349364905389 : ℝ) / (5 * 10 ^ 13)) hxlower)] at hn
      exact hn
    have hδlt : (1 / 250 : ℝ) < (3349364905389 : ℝ) / (5 * 10 ^ 13) := by norm_num
    linarith [hw, hnorm, hxlower]
  have hae_ne : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells q4D.xp),
      w ≠ Complex.ofReal x := by
    filter_upwards [hxmem] with x hx heq
    have hn := congrArg norm heq
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤
        (3349364905389 : ℝ) / (5 * 10 ^ 13)) hx.1)] at hn
    have hδlt : (1 / 250 : ℝ) < (3349364905389 : ℝ) / (5 * 10 ^ 13) := by norm_num
    linarith [hw, hx.1, hn]
  have hInt := q4_x_log_integrable w hsep
  have hX := integral_chainMeasureComplex_log_norm_sub_le_shift
    (v13ChainCells q4D.xp) δ w hδ (by simpa [δ] using hw)
    (by
      intro c hc
      have h := q4_x_cells_data c hc
      exact ⟨h.1, h.2.1⟩)
    hae_nonneg hae_ne hInt
  have hX' : (∫ t : ℂ, Real.log ‖w - t‖ ∂(q4ReferenceMeasure N).μx) ≤
      - (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + δ)).sum := by
    calc
      _ ≤ ∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure (v13ChainCells q4D.xp) := by
        simpa [q4ReferenceMeasure, v13RefMeasure, V13RawMeasures.toSigned,
          q4DecodedRows, q4RawReferenceMeasures, v13RefRaw,
          v13DecodedChainMeasure, v13ChainMeasureComplex] using hX
      _ = - (q4D.xp.map fun p => IK.val p.J *
          LogSegment.primitive (IK.val p.e + δ)).sum :=
        q4_x_shift_integral_eq_closed_jump_sum δ hδ
  have hXchain : (∫ t : ℂ, Real.log ‖w - t‖ ∂
      v13ChainMeasureComplex (v13ChainCells q4D.xp)) ≤
      - (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + δ)).sum := by
    simpa [q4ReferenceMeasure, v13RefMeasure, V13RawMeasures.toSigned,
      q4DecodedRows, q4RawReferenceMeasures, v13RefRaw,
      v13DecodedChainMeasure, v13ChainMeasureComplex] using hX'
  have hxposmem := q4_x_jpos_mem
  have hJclosed : IV.mem (jPos fieldMode q4D.xp)
      (- (q4D.xp.map fun p => IK.val p.J *
        LogSegment.primitive (IK.val p.e + δ)).sum) := by
    apply IK.mem_of_eq hxposmem
    simp [δ]
  have hqsubval : IK.val (qsub (Int.ofNat 4, 1) DELTA) = 4 - δ := by
    norm_num [IK.val, qsub, qneg, qadd, DELTA, δ]
  have hlogsub : IV.mem (logQ fieldMode.ntl (qsub (Int.ofNat 4, 1) DELTA))
      (Real.log (4 - δ)) := by
    apply IK.mem_of_eq (logQ_mem fieldMode.ntl
      (by norm_num [qsub, qneg, qadd, DELTA])
      (by norm_num [qsub, qneg, qadd, DELTA]))
    rw [hqsubval]
  have hlogδ : IV.mem (logQ fieldMode.ntl DELTA) (Real.log δ) := by
    apply IK.mem_of_eq (logQ_mem fieldMode.ntl (by norm_num [DELTA])
      (by norm_num [DELTA]))
    norm_num [IK.val, DELTA, δ]
  have hJ2 := smulInt_mem 2 hJclosed
  have hexub : IV.mem (exUB fieldMode q4D 4)
      (2 * (- (q4D.xp.map fun p => IK.val p.J *
          LogSegment.primitive (IK.val p.e + δ)).sum) +
        (- (5 / 4 : ℝ)) * Real.log (4 - δ) +
        (3 / 4 : ℝ) * Real.log δ) := by
    unfold exUB
    have h1 : IV.mem (smulInt 2 (jPos fieldMode q4D.xp))
        (2 * (- (q4D.xp.map fun p => IK.val p.J *
          LogSegment.primitive (IK.val p.e + δ)).sum)) := hJ2
    have h2 : IV.mem (smulQ (-5, 4)
        (logQ fieldMode.ntl (qsub (Int.ofNat 4, 1) DELTA)))
        ((- (5 / 4 : ℝ)) * Real.log (4 - δ)) := by
      apply IK.mem_of_eq (smulQ_mem (by norm_num : 0 < (4 : ℕ)) hlogsub)
      norm_num [IK.val]
    have h3 : IV.mem (smulQ (3, 4) (logQ fieldMode.ntl DELTA))
        ((3 / 4 : ℝ) * Real.log δ) := by
      apply IK.mem_of_eq (smulQ_mem (by norm_num : 0 < (4 : ℕ)) hlogδ)
      norm_num [IK.val]
    exact add_mem (add_mem h1 h2) h3
  have hCrossInt := q4_v_cross_integrable N w (by simpa [δ] using hw)
  let μv := (q4ReferenceMeasure N).μv
  have hfinite : μv Set.univ ≠ ⊤ := (q4ReferenceMeasure N).finite_v
  letI : IsFiniteMeasure μv := ⟨lt_top_iff_ne_top.mpr hfinite⟩
  have hconst : Integrable (fun _ : ℂ => Real.log (4 - δ)) μv := integrable_const _
  have hcrosslower : ∀ᵐ t ∂μv,
      Real.log (4 - δ) ≤ V.vCrossKernel 4 w t := by
    filter_upwards [q4_v_support_ae N] with t ht
    rcases ht with ⟨x, hx, rfl⟩
    have hnormwt : ‖w * Complex.ofReal x‖ ≤ δ := by
      calc
        ‖w * Complex.ofReal x‖ = ‖w‖ * x := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
        _ ≤ δ := by
          calc
            ‖w‖ * x ≤ (1 / 250) * x := mul_le_mul_of_nonneg_right hw hx.1
            _ ≤ 1 / 250 := by
              nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 250)
                (sub_nonneg.mpr hx.2)]
    have hnormlower : 4 - δ ≤ ‖(4 : ℂ) + w * Complex.ofReal x‖ := by
      have hcancel : ((4 : ℂ) + w * Complex.ofReal x) -
          (w * Complex.ofReal x) = (4 : ℂ) := by abel
      have htri := norm_sub_le ((4 : ℂ) + w * Complex.ofReal x)
        (w * Complex.ofReal x)
      have hfive : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [hcancel, hfive] at htri
      nlinarith [hnormwt]
    have hpos : 0 < 4 - δ := by norm_num [δ]
    change Real.log (4 - δ) ≤ Real.log ‖(4 : ℂ) + w * Complex.ofReal x‖
    exact Real.log_le_log hpos hnormlower
  have hcrossIntegral := integral_mono_ae hconst hCrossInt hcrosslower
  have hcrossValue : (∫ t : ℂ, V.vCrossKernel 4 w t ∂μv) ≥
      (5 / 4 : ℝ) * Real.log (4 - δ) := by
    change (∫ _ : ℂ, Real.log (4 - δ) ∂μv) ≤
      ∫ t : ℂ, V.vCrossKernel 4 w t ∂μv at hcrossIntegral
    have hmass : μv.real Set.univ = (5 / 4 : ℝ) := by
      simpa [Measure.real_def, μv] using
        congrArg ENNReal.toReal (q4ReferenceMeasure N).mass_v
    have hconstIntegral : (∫ _ : ℂ, Real.log (4 - δ) ∂μv) =
        (5 / 4 : ℝ) * Real.log (4 - δ) := by
      rw [integral_const, smul_eq_mul, hmass]
    rw [hconstIntegral] at hcrossIntegral
    exact hcrossIntegral
  have hlognorm : Real.log ‖w‖ ≤ Real.log δ := by
    exact Real.log_le_log hw0 (by simpa [δ] using hw)
  have hfieldBound : V.signedVFullFieldX (q4ReferenceMeasure N) w ≤
      2 * (- (q4D.xp.map fun p => IK.val p.J *
          LogSegment.primitive (IK.val p.e + δ)).sum) +
        (- (5 / 4 : ℝ)) * Real.log (4 - δ) +
        (3 / 4 : ℝ) * Real.log δ := by
    unfold V.signedVFullFieldX V.signedVFieldX
    rw [show (q4ReferenceMeasure N).q = 4 by rfl]
    rw [show (q4ReferenceMeasure N).μx = v13ChainMeasureComplex
      (v13ChainCells q4D.xp) by rfl]
    have hcrossRewrite : (∫ t : ℂ,
        V.vCrossKernel 4 w t ∂(q4ReferenceMeasure N).μv) =
        ∫ t : ℂ, V.vCrossKernel 4 w t ∂μv := by rfl
    rw [hcrossRewrite]
    have hXscaled := mul_le_mul_of_nonneg_left hXchain (by norm_num : 0 ≤ (2 : ℝ))
    have hcrossscaled : -(∫ t : ℂ, V.vCrossKernel 4 w t ∂μv) ≤
        -((5 / 4 : ℝ) * Real.log (4 - δ)) := neg_le_neg hcrossValue
    have hlogscaled := mul_le_mul_of_nonneg_left hlognorm
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
    linarith
  have hcheck : hiLe (exUB fieldMode q4D 4) (exQ 4) = true := by
    have h := q4Endpoint_check_local
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1
  have hupperUB : (2 * (- (q4D.xp.map fun p => IK.val p.J *
      LogSegment.primitive (IK.val p.e + δ)).sum) +
        (- (5 / 4 : ℝ)) * Real.log (4 - δ) +
        (3 / 4 : ℝ) * Real.log δ) ≤ IK.val (exQ 4) :=
    hiLe_spec (by norm_num [exQ]) hexub hcheck
  have hupper : V.signedVFullFieldX (q4ReferenceMeasure N) w ≤
      IK.val (exQ 4) := le_trans hfieldBound hupperUB
  have hv : IK.val (exQ 4) = (vEx 4 : ℝ) := by
    norm_num [exQ, vEx, IK.val]
  rw [← hv]
  exact hupper


end B3

end

end Li2Lean
