/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
import Li2Lean.B3.V13RowFacts

set_option maxHeartbeats 2000000

/-!
# Circle-Arc Cell Soundness, Arc Cover, and Conjugation Symmetry (`H6-S3`)

This module proves the `q`-generic circle-arc obligations (`S3` on the H6 closure board,
the proof plan §2.S3) for `z_field` on `V.vContourTrace q`:

1. `v13ArcPoint`: rational quarter-circle parametrisation of the upper semicircle of radius `3/5`
   (`quarter = 1` for `θ = 2 arctan s ∈ [0, π/2]`, `quarter = 2` for `θ = π - 2 arctan s ∈ [π/2, π]`).
2. `v13_field_arc_cell_on`: cellwise soundness of `fzArcUB` (`fieldUB R.data q lr .arc1` / `.arc2`)
   on `[0, 1]` for `s ↦ V.signedVFullFieldZ (v13RefMeasure R N) (v13ArcPoint quarter s)`.
3. `v13_upperArc_cover`: every point `V.vUpperArc t` (`t ∈ [0, 1]`) is of the form
   `v13ArcPoint quarter s` for some `quarter ∈ ({1, 2} : Finset ℕ)` and `s ∈ Set.Icc (0 : ℝ) 1`.
4. `signedVFullFieldZ_v13RefMeasure_conj` and `vLowerArc_eq_conj_vUpperArc`: conjugation
   invariance of `V.signedVFullFieldZ (v13RefMeasure R N)` and reflection of the lower arc onto
   the upper arc (`V.vLowerArc t = starRingEnd ℂ (V.vUpperArc (1 - t))`).
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Section 1: Rational quarter-circle parametrisation `v13ArcPoint` -/

/-- Rational quarter-circle parametrisation of the upper semicircle of radius `3/5`:
for `quarter = 1`, `X₁(s) = (3/5)(1 - s²)/(1 + s²)`, `Y(s) = (3/5)(2s)/(1 + s²)`;
for `quarter ≠ 1` (`quarter = 2`), `X₂(s) = -(3/5)(1 - s²)/(1 + s²)`, `Y(s) = (3/5)(2s)/(1 + s²)`. -/
noncomputable def v13ArcPoint (quarter : ℕ) (s : ℝ) : ℂ :=
  ⟨(if quarter = 1 then 1 else -1) * (3 / 5) * (1 - s ^ 2) / (1 + s ^ 2),
    (3 / 5) * (2 * s) / (1 + s ^ 2)⟩

theorem v13ArcPoint_re (quarter : ℕ) (s : ℝ) :
    (v13ArcPoint quarter s).re =
      (if quarter = 1 then 1 else -1) * (3 / 5) * (1 - s ^ 2) / (1 + s ^ 2) := rfl

theorem v13ArcPoint_im (quarter : ℕ) (s : ℝ) :
    (v13ArcPoint quarter s).im = (3 / 5) * (2 * s) / (1 + s ^ 2) := rfl

theorem v13ArcPoint_sq_sum (quarter : ℕ) (s : ℝ) :
    (v13ArcPoint quarter s).re ^ 2 + (v13ArcPoint quarter s).im ^ 2 = (9 / 25 : ℝ) := by
  have hden : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  unfold v13ArcPoint
  dsimp only
  split_ifs <;> { field_simp [hden]; ring }

theorem norm_v13ArcPoint (quarter : ℕ) (s : ℝ) :
    ‖v13ArcPoint quarter s‖ = (3 / 5 : ℝ) := by
  have hsq : ‖v13ArcPoint quarter s‖ ^ 2 = (3 / 5 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have h := v13ArcPoint_sq_sum quarter s
    linarith
  have hnonneg : 0 ≤ ‖v13ArcPoint quarter s‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖v13ArcPoint quarter s‖ - 3 / 5)]

theorem abs_v13ArcPoint_re_le (quarter : ℕ) (s : ℝ) :
    |(v13ArcPoint quarter s).re| ≤ (3 / 5 : ℝ) := by
  have hsq : (v13ArcPoint quarter s).re ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
    nlinarith [v13ArcPoint_sq_sum quarter s, sq_nonneg (v13ArcPoint quarter s).im]
  rw [← sq_abs] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp hsq

private theorem wX_den_pos (quarter : ℕ) {q : QF} (hq : 0 < q.2) :
    0 < (wX quarter q).2 := by
  have h1sq_den : 0 < (qadd (1, 1) (qsq q)).2 := qadd_den_pos (by decide) (qsq_den_pos hq)
  have h1sq_val : 0 < IK.val (qadd (1, 1) (qsq q)) := by
    rw [val_qadd (by decide) (qsq_den_pos hq), val_qsq_local]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [h1]
    positivity
  have h1sq_ne : (qadd (1, 1) (qsq q)).1 ≠ 0 := (fst_pos_of_val_pos h1sq_den h1sq_val).ne'
  have hnum_den : 0 < (qmul R (qsub (1, 1) (qsq q))).2 :=
    qmul_den_pos (by decide) (qsub_den_pos (by decide) (qsq_den_pos hq))
  unfold wX
  split_ifs
  · exact qdiv_den_pos hnum_den h1sq_ne
  · exact qneg_den_pos (qdiv_den_pos hnum_den h1sq_ne)

private theorem wY_den_pos {q : QF} (hq : 0 < q.2) :
    0 < (wY q).2 := by
  have h1sq_den : 0 < (qadd (1, 1) (qsq q)).2 := qadd_den_pos (by decide) (qsq_den_pos hq)
  have h1sq_val : 0 < IK.val (qadd (1, 1) (qsq q)) := by
    rw [val_qadd (by decide) (qsq_den_pos hq), val_qsq_local]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [h1]
    positivity
  have h1sq_ne : (qadd (1, 1) (qsq q)).1 ≠ 0 := (fst_pos_of_val_pos h1sq_den h1sq_val).ne'
  have hnum_den : 0 < (qmul R (qmul (2, 1) q)).2 :=
    qmul_den_pos (by decide) (qmul_den_pos (by decide) hq)
  exact qdiv_den_pos hnum_den h1sq_ne

private theorem val_wX_eq_v13ArcPoint_re (quarter : ℕ) {q : QF} (hq : 0 < q.2) :
    IK.val (wX quarter q) = (v13ArcPoint quarter (IK.val q)).re := by
  have h1sq_den : 0 < (qadd (1, 1) (qsq q)).2 := qadd_den_pos (by decide) (qsq_den_pos hq)
  have h1sq_val : IK.val (qadd (1, 1) (qsq q)) = 1 + (IK.val q) ^ 2 := by
    rw [val_qadd (by decide) (qsq_den_pos hq), val_qsq_local]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [h1]
  have h1sq_pos : 0 < IK.val (qadd (1, 1) (qsq q)) := by rw [h1sq_val]; positivity
  have h1sq_ne : (qadd (1, 1) (qsq q)).1 ≠ 0 := (fst_pos_of_val_pos h1sq_den h1sq_pos).ne'
  have hnum_den : 0 < (qmul R (qsub (1, 1) (qsq q))).2 :=
    qmul_den_pos (by decide) (qsub_den_pos (by decide) (qsq_den_pos hq))
  have hnum_val : IK.val (qmul R (qsub (1, 1) (qsq q))) = (3 / 5 : ℝ) * (1 - (IK.val q) ^ 2) := by
    rw [val_qmul, val_qsub (by decide) (qsq_den_pos hq), val_qsq_local]
    have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [hR, h1]
  unfold wX v13ArcPoint
  dsimp only
  split_ifs
  · rw [val_qdiv hnum_den h1sq_den h1sq_ne, hnum_val, h1sq_val]
    ring
  · rw [val_qneg, val_qdiv hnum_den h1sq_den h1sq_ne, hnum_val, h1sq_val]
    ring

private theorem val_wY_eq_v13ArcPoint_im (quarter : ℕ) {q : QF} (hq : 0 < q.2) :
    IK.val (wY q) = (v13ArcPoint quarter (IK.val q)).im := by
  have h1sq_den : 0 < (qadd (1, 1) (qsq q)).2 := qadd_den_pos (by decide) (qsq_den_pos hq)
  have h1sq_val : IK.val (qadd (1, 1) (qsq q)) = 1 + (IK.val q) ^ 2 := by
    rw [val_qadd (by decide) (qsq_den_pos hq), val_qsq_local]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [h1]
  have h1sq_pos : 0 < IK.val (qadd (1, 1) (qsq q)) := by rw [h1sq_val]; positivity
  have h1sq_ne : (qadd (1, 1) (qsq q)).1 ≠ 0 := (fst_pos_of_val_pos h1sq_den h1sq_pos).ne'
  have hnum_den : 0 < (qmul R (qmul (2, 1) q)).2 :=
    qmul_den_pos (by decide) (qmul_den_pos (by decide) hq)
  have hnum_val : IK.val (qmul R (qmul (2, 1) q)) = (3 / 5 : ℝ) * (2 * IK.val q) := by
    rw [val_qmul, val_qmul]
    have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
    rw [hR, h2]
  unfold wY v13ArcPoint
  dsimp only
  rw [val_qdiv hnum_den h1sq_den h1sq_ne, hnum_val, h1sq_val]

/-! ## Section 2: Monotonicity of `v13ArcPoint` and chain-potential bounds (`uChainAt`) -/

private theorem weierstrassCos_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (3 / 5 : ℝ) * (1 - b ^ 2) / (1 + b ^ 2) ≤ (3 / 5 : ℝ) * (1 - a ^ 2) / (1 + a ^ 2) := by
  have hda : 0 < 1 + a ^ 2 := by positivity
  have hdb : 0 < 1 + b ^ 2 := by positivity
  have hdiff : (3 / 5 : ℝ) * (1 - a ^ 2) / (1 + a ^ 2) -
      (3 / 5 : ℝ) * (1 - b ^ 2) / (1 + b ^ 2) =
      (6 / 5 : ℝ) * (b - a) * (b + a) / ((1 + a ^ 2) * (1 + b ^ 2)) := by
    field_simp [hda.ne', hdb.ne']
    ring
  have hnonneg : 0 ≤ (6 / 5 : ℝ) * (b - a) * (b + a) / ((1 + a ^ 2) * (1 + b ^ 2)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)) (by linarith)
    · exact mul_nonneg hda.le hdb.le
  linarith

/-- On any cell `[s0, s1] ⊆ [0, ∞)`, with `sa = if quarter = 1 then s0 else s1` and
`sb = if quarter = 1 then s1 else s0`, the real part `X(s) = (v13ArcPoint quarter s).re`
satisfies `X(sb) ≤ X(s) ≤ X(sa)` for all `s ∈ [s0, s1]`. -/
theorem v13ArcPoint_re_bounds (quarter : ℕ) {s0 s1 : QF} {s : ℝ}
    (hs0_nonneg : 0 ≤ IK.val s0) (hs0 : IK.val s0 ≤ s) (hs1 : s ≤ IK.val s1) :
    let sa := if quarter = 1 then s0 else s1
    let sb := if quarter = 1 then s1 else s0
    (v13ArcPoint quarter (IK.val sb)).re ≤ (v13ArcPoint quarter s).re ∧
      (v13ArcPoint quarter s).re ≤ (v13ArcPoint quarter (IK.val sa)).re := by
  intro sa sb
  have hs_nonneg : 0 ≤ s := le_trans hs0_nonneg hs0
  have h1 := weierstrassCos_antitone hs0_nonneg hs0
  have h2 := weierstrassCos_antitone hs_nonneg hs1
  -- Factor the sign out so that both branches compare the same atoms `(3/5)(1-x^2)/(1+x^2)`.
  have hre : ∀ x : ℝ, (v13ArcPoint quarter x).re =
      (if quarter = 1 then (1 : ℝ) else -1) * ((3 / 5 : ℝ) * (1 - x ^ 2) / (1 + x ^ 2)) := by
    intro x
    rw [v13ArcPoint_re]
    ring
  dsimp only [sa, sb]
  simp only [hre]
  by_cases hq : quarter = 1
  · simp only [if_pos hq, one_mul]
    -- goal: X(s1) ≤ X(s) ∧ X(s) ≤ X(s0) with X antitone: h2, h1
    constructor <;> linarith
  · simp only [if_neg hq, neg_one_mul]
    -- goal: -X(s0) ≤ -X(s) ∧ -X(s) ≤ -X(s1): from h1, h2
    constructor <;> linarith

private theorem vEnergyA_formula (s y : ℝ) :
    vEnergyA s y =
      s / 2 * Real.log (s ^ 2 + y ^ 2) - s + y * Real.arctan (s / y) := by
  by_cases hy : y = 0
  · by_cases hs : s = 0
    · simp [vEnergyA, hy, hs]
    · subst hy
      have hsabs : |s| ≠ 0 := abs_ne_zero.mpr hs
      have hlog : Real.log (s ^ 2 + (0 : ℝ) ^ 2) = 2 * Real.log |s| := by
        have hsq : s ^ 2 + (0 : ℝ) ^ 2 = |s| * |s| := by
          rw [abs_mul_abs_self]
          ring
        rw [hsq, Real.log_mul hsabs hsabs]
        ring
      rw [vEnergyA, if_pos rfl, if_neg hs, hlog]
      ring
  · simp [vEnergyA, hy]

private theorem uChainAt_mem (md : Mode) (rows : List CP) {X Y : QF}
    (hX : 0 < X.2) (hY : 0 < Y.2)
    (hrows : ∀ p ∈ rows, 0 < p.e.2 ∧ 0 < p.J.2) :
    IV.mem (uChainAt md rows X Y)
      (- (rows.map fun p => IK.val p.J * vEnergyA (IK.val p.e - IK.val X) (IK.val Y)).sum) := by
  unfold uChainAt
  apply IK.neg_mem
  apply IK.sumI_map_mem
  intro p hp
  rcases hrows p hp with ⟨he, hJ⟩
  have hsub_den : 0 < (qsub p.e X).2 := qsub_den_pos he hX
  have ha := V.EnergyCertI.aI_mem md hsub_den hY
  have ha' : IV.mem (aI md (qsub p.e X) Y) (vEnergyA (IK.val p.e - IK.val X) (IK.val Y)) := by
    refine IK.mem_of_eq ha ?_
    rw [val_qsub he hX]
    exact (vEnergyA_formula _ _).symm
  exact IK.smulQ_mem hJ ha'

private theorem integral_zp_v13ArcPoint_le_sa
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (quarter : ℕ) {s0 s1 : QF} {s : ℝ}
    (hs0_den : 0 < s0.2) (hs1_den : 0 < s1.2)
    (hs0_nonneg : 0 ≤ IK.val s0) (hs0 : IK.val s0 ≤ s) (hs1 : s ≤ IK.val s1) :
    let sa := if quarter = 1 then s0 else s1
    (∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖ ∂v13DecodedChainMeasure R.data.zp) ≤
      - (R.data.zp.map fun p =>
        IK.val p.J * vEnergyA (IK.val p.e - IK.val (wX quarter sa)) (IK.val (wY sa))).sum := by
  intro sa
  have hsa_den : 0 < sa.2 := by dsimp [sa]; split_ifs <;> assumption
  rw [val_wX_eq_v13ArcPoint_re quarter hsa_den, val_wY_eq_v13ArcPoint_im quarter hsa_den,
    ← integral_v13DecodedChainMeasure_log_norm_sub_eq_vEnergyA R.data.zp
      (v13ArcPoint quarter (IK.val sa))
      (fun c hc => (hR.z_cells c hc).1) (fun c hc => (hR.z_cells c hc).2) hR.z_jump]
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap (t : ℝ) :
      (∫ z : ℂ, Real.log ‖v13ArcPoint quarter t - z‖ ∂v13DecodedChainMeasure R.data.zp) =
        ∫ u : ℝ, Real.log ‖v13ArcPoint quarter t - (u : ℂ)‖
          ∂v13ChainMeasure (v13ChainCells R.data.zp) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap s, hmap (IK.val sa)]
  have hInt1 := integrable_v13ChainMeasure_log_norm_sub_complex (v13ChainCells R.data.zp)
    (v13ArcPoint quarter s) (fun c hc => (hR.z_cells c hc).1)
  have hInt2 := integrable_v13ChainMeasure_log_norm_sub_complex (v13ChainCells R.data.zp)
    (v13ArcPoint quarter (IK.val sa)) (fun c hc => (hR.z_cells c hc).1)
  apply integral_mono_ae hInt1 hInt2
  filter_upwards [ae_le_of_right_le_v13ChainMeasure (v13ChainCells R.data.zp)
      (fun c hc => (v13DecodedRows_z_source_bounds R c hc).2),
    ae_ne_v13ChainMeasure (v13ChainCells R.data.zp) (-(3 / 5 : ℝ))] with u hu hne
  have hu_lt : u < -(3 / 5 : ℝ) := lt_of_le_of_ne hu hne
  have hre_le : (v13ArcPoint quarter s).re ≤ (v13ArcPoint quarter (IK.val sa)).re :=
    (v13ArcPoint_re_bounds quarter hs0_nonneg hs0 hs1).2
  have hnorm_sq (t : ℝ) :
      ‖v13ArcPoint quarter t - (u : ℂ)‖ ^ 2 =
        (9 / 25 : ℝ) + u ^ 2 - 2 * u * (v13ArcPoint quarter t).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    have h := v13ArcPoint_sq_sum quarter t
    linarith
  have hpos_s : 0 < ‖v13ArcPoint quarter s - (u : ℂ)‖ := by
    have habs := (abs_le.mp (abs_v13ArcPoint_re_le quarter s)).1
    have hsq_pos : 0 < ‖v13ArcPoint quarter s - (u : ℂ)‖ ^ 2 := by
      rw [hnorm_sq s]
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
    by_contra hle
    have h0 : ‖v13ArcPoint quarter s - (u : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [h0] at hsq_pos
    norm_num at hsq_pos
  have hsq_le : ‖v13ArcPoint quarter s - (u : ℂ)‖ ^ 2 ≤
      ‖v13ArcPoint quarter (IK.val sa) - (u : ℂ)‖ ^ 2 := by
    rw [hnorm_sq s, hnorm_sq (IK.val sa)]
    nlinarith
  have hnorm_le : ‖v13ArcPoint quarter s - (u : ℂ)‖ ≤
      ‖v13ArcPoint quarter (IK.val sa) - (u : ℂ)‖ := by
    nlinarith [norm_nonneg (v13ArcPoint quarter s - (u : ℂ)),
      norm_nonneg (v13ArcPoint quarter (IK.val sa) - (u : ℂ))]
  exact Real.log_le_log hpos_s hnorm_le

private theorem integral_vp_v13ArcPoint_le_sb
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (quarter : ℕ) {s0 s1 : QF} {s : ℝ}
    (hs0_den : 0 < s0.2) (hs1_den : 0 < s1.2)
    (hs0_nonneg : 0 ≤ IK.val s0) (hs0 : IK.val s0 ≤ s) (hs1 : s ≤ IK.val s1) :
    let sb := if quarter = 1 then s1 else s0
    (∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖ ∂v13DecodedChainMeasure R.data.vp) ≤
      - (R.data.vp.map fun p =>
        IK.val p.J * vEnergyA (IK.val p.e - IK.val (wX quarter sb)) (IK.val (wY sb))).sum := by
  intro sb
  have hsb_den : 0 < sb.2 := by dsimp [sb]; split_ifs <;> assumption
  rw [val_wX_eq_v13ArcPoint_re quarter hsb_den, val_wY_eq_v13ArcPoint_im quarter hsb_den,
    ← integral_v13DecodedChainMeasure_log_norm_sub_eq_vEnergyA R.data.vp
      (v13ArcPoint quarter (IK.val sb))
      (fun c hc => (hR.v_cells c hc).2.1) (fun c hc => (hR.v_cells c hc).2.2) hR.v_jump]
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap (t : ℝ) :
      (∫ z : ℂ, Real.log ‖v13ArcPoint quarter t - z‖ ∂v13DecodedChainMeasure R.data.vp) =
        ∫ u : ℝ, Real.log ‖v13ArcPoint quarter t - (u : ℂ)‖
          ∂v13ChainMeasure (v13ChainCells R.data.vp) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap s, hmap (IK.val sb)]
  have hInt1 := integrable_v13ChainMeasure_log_norm_sub_complex (v13ChainCells R.data.vp)
    (v13ArcPoint quarter s) (fun c hc => (hR.v_cells c hc).2.1)
  have hInt2 := integrable_v13ChainMeasure_log_norm_sub_complex (v13ChainCells R.data.vp)
    (v13ArcPoint quarter (IK.val sb)) (fun c hc => (hR.v_cells c hc).2.1)
  apply integral_mono_ae hInt1 hInt2
  filter_upwards [ae_nonneg_v13ChainMeasure (v13ChainCells R.data.vp)
      (fun c hc => ⟨(hR.v_cells c hc).1, (hR.v_cells c hc).2.1⟩),
    ae_ne_v13ChainMeasure (v13ChainCells R.data.vp) (3 / 5 : ℝ)] with u hu hne
  have hre_ge : (v13ArcPoint quarter (IK.val sb)).re ≤ (v13ArcPoint quarter s).re :=
    (v13ArcPoint_re_bounds quarter hs0_nonneg hs0 hs1).1
  have hnorm_sq (t : ℝ) :
      ‖v13ArcPoint quarter t - (u : ℂ)‖ ^ 2 =
        (9 / 25 : ℝ) + u ^ 2 - 2 * u * (v13ArcPoint quarter t).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    have h := v13ArcPoint_sq_sum quarter t
    linarith
  have hpos_s : 0 < ‖v13ArcPoint quarter s - (u : ℂ)‖ := by
    have habs := (abs_le.mp (abs_v13ArcPoint_re_le quarter s)).2
    have hsq_pos : 0 < ‖v13ArcPoint quarter s - (u : ℂ)‖ ^ 2 := by
      rw [hnorm_sq s]
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
    by_contra hle
    have h0 : ‖v13ArcPoint quarter s - (u : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [h0] at hsq_pos
    norm_num at hsq_pos
  have hsq_le : ‖v13ArcPoint quarter s - (u : ℂ)‖ ^ 2 ≤
      ‖v13ArcPoint quarter (IK.val sb) - (u : ℂ)‖ ^ 2 := by
    rw [hnorm_sq s, hnorm_sq (IK.val sb)]
    nlinarith
  have hnorm_le : ‖v13ArcPoint quarter s - (u : ℂ)‖ ≤
      ‖v13ArcPoint quarter (IK.val sb) - (u : ℂ)‖ := by
    nlinarith [norm_nonneg (v13ArcPoint quarter s - (u : ℂ)),
      norm_nonneg (v13ArcPoint quarter (IK.val sb) - (u : ℂ))]
  exact Real.log_le_log hpos_s hnorm_le

/-! ## Section 3: Poisson arc-cell enclosure `poiArc` -/

private theorem circle_chord_decomp
    {X Y Xm Ym xc yc : ℝ}
    (hXY : X ^ 2 + Y ^ 2 = (9 / 25 : ℝ))
    (hXmYm : Xm ^ 2 + Ym ^ 2 = (9 / 25 : ℝ)) :
    ((X - xc) ^ 2 + (Y - yc) ^ 2) - ((Xm - xc) ^ 2 + (Ym - yc) ^ 2) =
      (xc * Xm + yc * Ym) * (((X - Xm) ^ 2 + (Y - Ym) ^ 2) / (9 / 25 : ℝ)) +
        2 * (Ym * xc - Xm * yc) * ((Xm * Y - Ym * X) / (9 / 25 : ℝ)) := by
  have h1 : (X - Xm) ^ 2 + (Y - Ym) ^ 2 =
      (X ^ 2 + Y ^ 2) + (Xm ^ 2 + Ym ^ 2) - 2 * (X * Xm + Y * Ym) := by ring
  have h2 : ((X - xc) ^ 2 + (Y - yc) ^ 2) - ((Xm - xc) ^ 2 + (Ym - yc) ^ 2) =
      (X ^ 2 + Y ^ 2) - (Xm ^ 2 + Ym ^ 2) + 2 * xc * (Xm - X) + 2 * yc * (Ym - Y) := by ring
  rw [h1, h2, hXY, hXmYm]
  have h3 : (xc * Xm + yc * Ym) * ((9 / 25 + 9 / 25 - 2 * (X * Xm + Y * Ym)) / (9 / 25 : ℝ)) +
      2 * (Ym * xc - Xm * yc) * ((Xm * Y - Ym * X) / (9 / 25 : ℝ)) =
      (25 / 9 : ℝ) * ((xc * Xm + yc * Ym) * (2 * (Xm ^ 2 + Ym ^ 2) - 2 * (X * Xm + Y * Ym)) +
        2 * (Ym * xc - Xm * yc) * (Xm * Y - Ym * X)) := by
    rw [hXmYm]
    ring
  rw [h3]
  have h4 : (xc * Xm + yc * Ym) * (2 * (Xm ^ 2 + Ym ^ 2) - 2 * (X * Xm + Y * Ym)) +
      2 * (Ym * xc - Xm * yc) * (Xm * Y - Ym * X) =
      (Xm ^ 2 + Ym ^ 2) * (2 * xc * (Xm - X) + 2 * yc * (Ym - Y)) := by ring
  rw [h4, hXmYm]
  ring

private theorem v13ArcPoint_chord_sq (quarter : ℕ) (sm s : ℝ) :
    (((v13ArcPoint quarter s).re - (v13ArcPoint quarter sm).re) ^ 2 +
      ((v13ArcPoint quarter s).im - (v13ArcPoint quarter sm).im) ^ 2) / (9 / 25 : ℝ) =
      4 * (s - sm) ^ 2 / ((1 + sm ^ 2) * (1 + s ^ 2)) := by
  have hd1 : (1 + sm ^ 2 : ℝ) ≠ 0 := by positivity
  have hd2 : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  unfold v13ArcPoint
  dsimp only
  split_ifs <;> { field_simp [hd1, hd2]; ring }

private theorem v13ArcPoint_cross_sq (quarter : ℕ) (sm s : ℝ) :
    (((v13ArcPoint quarter sm).re * (v13ArcPoint quarter s).im -
      (v13ArcPoint quarter sm).im * (v13ArcPoint quarter s).re) / (9 / 25 : ℝ)) ^ 2 =
      4 * (s - sm) ^ 2 * (1 + sm * s) ^ 2 / ((1 + sm ^ 2) ^ 2 * (1 + s ^ 2) ^ 2) := by
  have hd1 : (1 + sm ^ 2 : ℝ) ≠ 0 := by positivity
  have hd2 : (1 + s ^ 2 : ℝ) ≠ 0 := by positivity
  unfold v13ArcPoint
  dsimp only
  split_ifs <;> { field_simp [hd1, hd2]; ring }

private theorem poiArc_mem_and_bound
    (c : PR)
    (hc : 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
      c.w.2 = U ∧ c.w.1 ≤ (U : Int) ∧
      (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2)
    (quarter : ℕ) {s0 s1 : QF}
    (hs0_den : 0 < s0.2) (hs1_den : 0 < s1.2)
    (hs0_nonneg : 0 ≤ IK.val s0) (hs01 : IK.val s0 < IK.val s1) :
    let sm := qhalf (qadd s0 s1)
    let Th := qdiv (qsub s1 s0) (qadd (1, 1) (qsq s0))
    ∃ Uc : ℝ, IV.mem (poiArc fieldMode c (wX quarter sm) (wY sm) Th) Uc ∧
      ∀ s, IK.val s0 ≤ s → s ≤ IK.val s1 →
        IK.val c.w *
          ((1 / 2 : ℝ) * Real.log
            (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
              ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2)) ≤ Uc := by
  intro sm Th
  rcases hc with ⟨hcx2, hcy2, hw2, hw1, hwU, hw_le_U, hrad⟩
  have hsm_den : 0 < sm.2 := qhalf_den_pos (qadd_den_pos hs0_den hs1_den)
  have hsm_val : IK.val sm = (IK.val s0 + IK.val s1) / 2 := by
    dsimp [sm]; rw [val_qhalf_local, val_qadd hs0_den hs1_den]
  have h1s0_den : 0 < (qadd (1, 1) (qsq s0)).2 := qadd_den_pos (by decide) (qsq_den_pos hs0_den)
  have h1s0_val : IK.val (qadd (1, 1) (qsq s0)) = 1 + (IK.val s0) ^ 2 := by
    rw [val_qadd (by decide) (qsq_den_pos hs0_den), val_qsq_local]
    have h1 : IK.val (1, 1) = 1 := by norm_num [IK.val]
    rw [h1]
  have h1s0_pos : 0 < IK.val (qadd (1, 1) (qsq s0)) := by rw [h1s0_val]; positivity
  have h1s0_ne : (qadd (1, 1) (qsq s0)).1 ≠ 0 := (fst_pos_of_val_pos h1s0_den h1s0_pos).ne'
  have hTh_den : 0 < Th.2 := qdiv_den_pos (qsub_den_pos hs1_den hs0_den) h1s0_ne
  have hTh_val : IK.val Th = (IK.val s1 - IK.val s0) / (1 + (IK.val s0) ^ 2) := by
    dsimp [Th]
    rw [val_qdiv (qsub_den_pos hs1_den hs0_den) h1s0_den h1s0_ne,
      val_qsub hs1_den hs0_den, h1s0_val]
  have hTh_pos : 0 < IK.val Th := by
    rw [hTh_val]
    exact div_pos (sub_pos.mpr hs01) (by positivity)
  let Xm := wX quarter sm
  let Ym := wY sm
  have hXm_den : 0 < Xm.2 := wX_den_pos quarter hsm_den
  have hYm_den : 0 < Ym.2 := wY_den_pos hsm_den
  have hXm_val : IK.val Xm = (v13ArcPoint quarter (IK.val sm)).re :=
    val_wX_eq_v13ArcPoint_re quarter hsm_den
  have hYm_val : IK.val Ym = (v13ArcPoint quarter (IK.val sm)).im :=
    val_wY_eq_v13ArcPoint_im quarter hsm_den
  let Dm := qadd (qsq (qsub Xm c.cx)) (qsq (qsub Ym c.cy))
  let Sv := qsub (qmul Ym c.cx) (qmul Xm c.cy)
  let rcU := qhalf (qadd R2 (qadd (qsq c.cx) (qsq c.cy)))
  let Dlo := qsub (qsub Dm (qmul (qmul (2, 1) (qabs Sv)) Th)) (qmul rcU (qsq Th))
  have hDm_den : 0 < Dm.2 :=
    qadd_den_pos (qsq_den_pos (qsub_den_pos hXm_den hcx2))
      (qsq_den_pos (qsub_den_pos hYm_den hcy2))
  have hSv_den : 0 < Sv.2 := qsub_den_pos (qmul_den_pos hYm_den hcx2) (qmul_den_pos hXm_den hcy2)
  have hrcU_den : 0 < rcU.2 :=
    qhalf_den_pos (qadd_den_pos (by decide) (qadd_den_pos (qsq_den_pos hcx2) (qsq_den_pos hcy2)))
  have hDlo_den : 0 < Dlo.2 :=
    qsub_den_pos
      (qsub_den_pos hDm_den (qmul_den_pos (qmul_den_pos (by decide) (qabs_den_pos hSv_den)) hTh_den))
      (qmul_den_pos hrcU_den (qsq_den_pos hTh_den))
  have hw_nonneg : 0 ≤ IK.val c.w := by
    unfold IK.val
    exact div_nonneg (by exact_mod_cast hw1) (by exact_mod_cast hw2.le)
  have hw_le_one : IK.val c.w ≤ 1 := by
    unfold IK.val
    rw [hwU]
    have hUpos : (0 : ℝ) < (U : ℝ) := by norm_num [U]
    exact (div_le_one hUpos).mpr (by exact_mod_cast hw_le_U)
  have hDs_pos : ∀ s : ℝ,
      0 < ((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
        ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2 := by
    intro s
    have hnorm_sq : ‖v13ArcPoint quarter s - v13PoissonPoint c‖ ^ 2 =
        ((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
          ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [v13PoissonPoint]
      ring
    have hpc_lt : ‖v13PoissonPoint c‖ < (3 / 5 : ℝ) := by
      rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num)]
      rw [Complex.sq_norm]
      simpa [v13PoissonPoint, Complex.normSq, pow_two] using hrad
    have htri := norm_sub_norm_le (v13ArcPoint quarter s) (v13PoissonPoint c)
    rw [norm_v13ArcPoint] at htri
    have hpos : 0 < ‖v13ArcPoint quarter s - v13PoissonPoint c‖ := by linarith
    rw [← hnorm_sq]
    exact sq_pos_of_pos hpos
  by_cases hfail : qle Dlo (0, 1) = true
  · refine ⟨1000, ?_, ?_⟩
    · unfold poiArc
      dsimp only
      rw [if_pos hfail]
      unfold IV.mem FAIL IK.S
      norm_num
    · intro s _ _
      have hDs_le : ((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
          ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2 ≤ 4 := by
        have h1 := v13ArcPoint_sq_sum quarter s
        have h2 : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := le_of_lt hrad
        nlinarith [sq_nonneg ((v13ArcPoint quarter s).re + IK.val c.cx),
          sq_nonneg ((v13ArcPoint quarter s).im + IK.val c.cy)]
      have hlog_le : Real.log (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
          ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2) ≤ 3 := by
        have h := Real.log_le_sub_one_of_pos (hDs_pos s)
        linarith
      by_cases hlog_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.log
          (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
            ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2)
      · have hprod : IK.val c.w * ((1 / 2 : ℝ) * Real.log
            (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
              ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2)) ≤
            1 * ((1 / 2 : ℝ) * 3) := by
          exact mul_le_mul hw_le_one (by linarith) hlog_nonneg zero_le_one
        linarith
      · push_neg at hlog_nonneg
        have hprod : IK.val c.w * ((1 / 2 : ℝ) * Real.log
            (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
              ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hw_nonneg (le_of_lt hlog_nonneg)
        linarith
  · have hDlo_pos : 0 < IK.val Dlo := by
      have hnot : ¬ (IK.val Dlo ≤ IK.val (0, 1)) :=
        mt (qle_spec hDlo_den (by decide)).mpr hfail
      have h0 : IK.val (0, 1) = 0 := by norm_num [IK.val]
      rw [h0] at hnot
      exact not_le.mp hnot
    have hDm_val : IK.val Dm =
        (IK.val Xm - IK.val c.cx) ^ 2 + (IK.val Ym - IK.val c.cy) ^ 2 := by
      dsimp [Dm]
      rw [val_qadd (qsq_den_pos (qsub_den_pos hXm_den hcx2))
          (qsq_den_pos (qsub_den_pos hYm_den hcy2)),
        val_qsq_local, val_qsq_local, val_qsub hXm_den hcx2, val_qsub hYm_den hcy2]
    have hSv_val : IK.val Sv = IK.val Ym * IK.val c.cx - IK.val Xm * IK.val c.cy := by
      dsimp [Sv]
      rw [val_qsub (qmul_den_pos hYm_den hcx2) (qmul_den_pos hXm_den hcy2),
        val_qmul, val_qmul]
    have hrcU_val : IK.val rcU =
        ((9 / 25 : ℝ) + ((IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)) / 2 := by
      dsimp [rcU]
      rw [val_qhalf_local,
        val_qadd (by decide) (qadd_den_pos (qsq_den_pos hcx2) (qsq_den_pos hcy2)),
        val_qadd (qsq_den_pos hcx2) (qsq_den_pos hcy2), val_qsq_local, val_qsq_local]
      have hR2 : IK.val R2 = (9 / 25 : ℝ) := by norm_num [R2, IK.val]
      rw [hR2]
    have hrcU_pos : 0 < IK.val rcU := by rw [hrcU_val]; positivity
    have hDlo_val : IK.val Dlo =
        IK.val Dm - 2 * |IK.val Sv| * IK.val Th - IK.val rcU * (IK.val Th) ^ 2 := by
      dsimp [Dlo]
      rw [val_qsub
          (qsub_den_pos hDm_den
            (qmul_den_pos (qmul_den_pos (by decide) (qabs_den_pos hSv_den)) hTh_den))
          (qmul_den_pos hrcU_den (qsq_den_pos hTh_den)),
        val_qsub hDm_den (qmul_den_pos (qmul_den_pos (by decide) (qabs_den_pos hSv_den)) hTh_den),
        val_qmul, val_qmul, val_qabs_local hSv_den, val_qmul, val_qsq_local]
      have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
      rw [h2]
    have hDm_pos : 0 < IK.val Dm := by
      rw [hDm_val, hXm_val, hYm_val]
      exact hDs_pos (IK.val sm)
    have hDm1 : 0 < Dm.1 := fst_pos_of_val_pos hDm_den hDm_pos
    have h2Dlo_den : 0 < (qmul (2, 1) Dlo).2 := qmul_den_pos (by decide) hDlo_den
    have h2Dlo_val : IK.val (qmul (2, 1) Dlo) = 2 * IK.val Dlo := by
      rw [val_qmul]
      have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
      rw [h2]
    have h2Dlo_pos : 0 < IK.val (qmul (2, 1) Dlo) := by rw [h2Dlo_val]; linarith
    have h2Dlo1 : (qmul (2, 1) Dlo).1 ≠ 0 := (fst_pos_of_val_pos h2Dlo_den h2Dlo_pos).ne'
    let tailQ := qadd (qmul (qdiv (qabs Sv) Dm) Th)
      (qdiv (qmul (3, 1) (qmul rcU (qsq Th))) (qmul (2, 1) Dlo))
    have hdiv1_den : 0 < (qdiv (qabs Sv) Dm).2 := qdiv_den_pos (qabs_den_pos hSv_den) hDm1.ne'
    have hdiv2_den : 0 < (qdiv (qmul (3, 1) (qmul rcU (qsq Th))) (qmul (2, 1) Dlo)).2 :=
      qdiv_den_pos (qmul_den_pos (by decide) (qmul_den_pos hrcU_den (qsq_den_pos hTh_den))) h2Dlo1
    have htail_den : 0 < tailQ.2 := qadd_den_pos (qmul_den_pos hdiv1_den hTh_den) hdiv2_den
    have htail_val : IK.val tailQ =
        (|IK.val Sv| / IK.val Dm) * IK.val Th +
          3 * (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo) := by
      dsimp [tailQ]
      rw [val_qadd (qmul_den_pos hdiv1_den hTh_den) hdiv2_den,
        val_qmul, val_qdiv (qabs_den_pos hSv_den) hDm_den hDm1.ne', val_qabs_local hSv_den,
        val_qdiv (qmul_den_pos (by decide) (qmul_den_pos hrcU_den (qsq_den_pos hTh_den)))
          h2Dlo_den h2Dlo1,
        val_qmul, val_qmul, val_qsq_local, h2Dlo_val]
      have h3 : IK.val (3, 1) = 3 := by norm_num [IK.val]
      rw [h3]
    refine ⟨IK.val c.w * ((1 / 2 : ℝ) * Real.log (IK.val Dm) + IK.val tailQ), ?_, ?_⟩
    · unfold poiArc
      dsimp only
      rw [if_neg hfail]
      have hlog := IK.logQ_mem fieldMode.ntl hDm1 hDm_den
      have hsmul_half := IK.smulQ_mem (c := (1, 2)) (by decide) hlog
      have hhalf_val : IK.val (1, 2) = (1 / 2 : ℝ) := by norm_num [IK.val]
      have hsmul_half' := IK.mem_of_eq hsmul_half (by rw [hhalf_val])
      have hadd := IK.add_mem hsmul_half' (IK.ofQ_mem htail_den)
      exact IK.smulQ_mem hw2 hadd
    · intro s hs0 hs1
      apply mul_le_mul_of_nonneg_left _ hw_nonneg
      rw [htail_val]
      let Ds := ((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
        ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2
      have hlog_le : (1 / 2 : ℝ) * Real.log Ds - (1 / 2 : ℝ) * Real.log (IK.val Dm) ≤
          (Ds - IK.val Dm) / (2 * IK.val Dm) := by
        have hdiv_pos : 0 < Ds / IK.val Dm := div_pos (hDs_pos s) hDm_pos
        have h1 : Real.log Ds - Real.log (IK.val Dm) = Real.log (Ds / IK.val Dm) :=
          (Real.log_div (ne_of_gt (hDs_pos s)) (ne_of_gt hDm_pos)).symm
        have h2 : Real.log (Ds / IK.val Dm) ≤ Ds / IK.val Dm - 1 :=
          Real.log_le_sub_one_of_pos hdiv_pos
        have h3 : Ds / IK.val Dm - 1 = (Ds - IK.val Dm) / IK.val Dm := by
          field_simp [ne_of_gt hDm_pos]
        have h4 : (Ds - IK.val Dm) / (2 * IK.val Dm) =
            (1 / 2 : ℝ) * ((Ds - IK.val Dm) / IK.val Dm) := by ring
        linarith
      have hdecomp : Ds - IK.val Dm =
          (IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym) *
            ((((v13ArcPoint quarter s).re - IK.val Xm) ^ 2 +
              ((v13ArcPoint quarter s).im - IK.val Ym) ^ 2) / (9 / 25 : ℝ)) +
            2 * IK.val Sv *
              ((IK.val Xm * (v13ArcPoint quarter s).im -
                IK.val Ym * (v13ArcPoint quarter s).re) / (9 / 25 : ℝ)) := by
        dsimp [Ds]
        rw [hDm_val, hSv_val, hXm_val, hYm_val]
        exact circle_chord_decomp (v13ArcPoint_sq_sum quarter s)
          (v13ArcPoint_sq_sum quarter (IK.val sm))
      let δ2 := (((v13ArcPoint quarter s).re - IK.val Xm) ^ 2 +
        ((v13ArcPoint quarter s).im - IK.val Ym) ^ 2) / (9 / 25 : ℝ)
      let σ := (IK.val Xm * (v13ArcPoint quarter s).im -
        IK.val Ym * (v13ArcPoint quarter s).re) / (9 / 25 : ℝ)
      have hδ2_nonneg : 0 ≤ δ2 := by dsimp [δ2]; positivity
      have hδ2_le : δ2 ≤ (IK.val Th) ^ 2 := by
        dsimp [δ2]
        rw [hXm_val, hYm_val, v13ArcPoint_chord_sq, hTh_val]
        have hnum_le : 4 * (s - IK.val sm) ^ 2 ≤ (IK.val s1 - IK.val s0) ^ 2 := by
          rw [hsm_val]
          nlinarith
        have hsm_ge : IK.val s0 ≤ IK.val sm := by rw [hsm_val]; linarith
        have hden1 : (1 + (IK.val s0) ^ 2) ^ 2 ≤
            (1 + (IK.val sm) ^ 2) * (1 + s ^ 2) := by
          have hsq1 : (IK.val s0) ^ 2 ≤ (IK.val sm) ^ 2 := by nlinarith
          have hsq2 : (IK.val s0) ^ 2 ≤ s ^ 2 := by nlinarith
          nlinarith
        have hden0_pos : 0 < (1 + (IK.val s0) ^ 2) ^ 2 := by positivity
        calc
          4 * (s - IK.val sm) ^ 2 / ((1 + (IK.val sm) ^ 2) * (1 + s ^ 2)) ≤
              (IK.val s1 - IK.val s0) ^ 2 / ((1 + (IK.val sm) ^ 2) * (1 + s ^ 2)) :=
            div_le_div_of_nonneg_right hnum_le (by positivity)
          _ ≤ (IK.val s1 - IK.val s0) ^ 2 / (1 + (IK.val s0) ^ 2) ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _) hden0_pos hden1
          _ = ((IK.val s1 - IK.val s0) / (1 + (IK.val s0) ^ 2)) ^ 2 :=
            (div_pow (IK.val s1 - IK.val s0) (1 + (IK.val s0) ^ 2) 2).symm
      have hσ_abs_le : |σ| ≤ IK.val Th := by
        have hσ_sq_le : σ ^ 2 ≤ δ2 := by
          dsimp [σ, δ2]
          rw [hXm_val, hYm_val, v13ArcPoint_cross_sq, v13ArcPoint_chord_sq]
          have hcs : (1 + IK.val sm * s) ^ 2 ≤ (1 + (IK.val sm) ^ 2) * (1 + s ^ 2) := by
            nlinarith [sq_nonneg (s - IK.val sm)]
          have hd_pos : 0 < (1 + (IK.val sm) ^ 2) * (1 + s ^ 2) := by positivity
          calc
            4 * (s - IK.val sm) ^ 2 * (1 + IK.val sm * s) ^ 2 /
                ((1 + (IK.val sm) ^ 2) ^ 2 * (1 + s ^ 2) ^ 2) ≤
              4 * (s - IK.val sm) ^ 2 * ((1 + (IK.val sm) ^ 2) * (1 + s ^ 2)) /
                ((1 + (IK.val sm) ^ 2) ^ 2 * (1 + s ^ 2) ^ 2) := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hcs (by positivity)
              · positivity
            _ = 4 * (s - IK.val sm) ^ 2 / ((1 + (IK.val sm) ^ 2) * (1 + s ^ 2)) := by
              field_simp [hd_pos.ne']
        have hsq : |σ| ^ 2 ≤ (IK.val Th) ^ 2 := by
          rw [sq_abs]
          exact le_trans hσ_sq_le hδ2_le
        exact (sq_le_sq₀ (abs_nonneg _) hTh_pos.le).mp hsq
      have hdot_le : IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym ≤ IK.val rcU := by
        rw [hrcU_val, hXm_val, hYm_val]
        have h := v13ArcPoint_sq_sum quarter (IK.val sm)
        nlinarith [sq_nonneg ((v13ArcPoint quarter (IK.val sm)).re - IK.val c.cx),
          sq_nonneg ((v13ArcPoint quarter (IK.val sm)).im - IK.val c.cy)]
      have hterm1 : (IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym) * δ2 ≤
          IK.val rcU * (IK.val Th) ^ 2 := by
        calc
          (IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym) * δ2 ≤ IK.val rcU * δ2 :=
            mul_le_mul_of_nonneg_right hdot_le hδ2_nonneg
          _ ≤ IK.val rcU * (IK.val Th) ^ 2 :=
            mul_le_mul_of_nonneg_left hδ2_le hrcU_pos.le
      have hterm2 : 2 * IK.val Sv * σ ≤ 2 * |IK.val Sv| * IK.val Th := by
        calc
          2 * IK.val Sv * σ ≤ |2 * IK.val Sv * σ| := le_abs_self _
          _ = 2 * |IK.val Sv| * |σ| := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          _ ≤ 2 * |IK.val Sv| * IK.val Th :=
            mul_le_mul_of_nonneg_left hσ_abs_le (by positivity)
      have hDs_sub_le : Ds - IK.val Dm ≤
          2 * |IK.val Sv| * IK.val Th + IK.val rcU * (IK.val Th) ^ 2 := by
        have hdecomp' : Ds - IK.val Dm =
            (IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym) * δ2 +
              2 * IK.val Sv * σ := by
          simpa [δ2, σ] using hdecomp
        calc
          Ds - IK.val Dm =
              (IK.val c.cx * IK.val Xm + IK.val c.cy * IK.val Ym) * δ2 +
                2 * IK.val Sv * σ := hdecomp'
          _ ≤ IK.val rcU * (IK.val Th) ^ 2 +
              2 * |IK.val Sv| * IK.val Th := add_le_add hterm1 hterm2
          _ = 2 * |IK.val Sv| * IK.val Th + IK.val rcU * (IK.val Th) ^ 2 := by ring
      have hdiv_le : (Ds - IK.val Dm) / (2 * IK.val Dm) ≤
          (|IK.val Sv| / IK.val Dm) * IK.val Th +
            (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) := by
        have h1 : (Ds - IK.val Dm) / (2 * IK.val Dm) ≤
            (2 * |IK.val Sv| * IK.val Th + IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) :=
          div_le_div_of_nonneg_right hDs_sub_le (by linarith)
        have h2 : (2 * |IK.val Sv| * IK.val Th + IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) =
            (|IK.val Sv| / IK.val Dm) * IK.val Th +
              (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) := by
          field_simp [ne_of_gt hDm_pos]
        linarith
      have hDlo_le_Dm : IK.val Dlo ≤ IK.val Dm := by
        rw [hDlo_val]
        have hnonneg1 : 0 ≤ 2 * |IK.val Sv| * IK.val Th := by positivity
        have hnonneg2 : 0 ≤ IK.val rcU * (IK.val Th) ^ 2 := by positivity
        linarith
      have hquad_le : (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) ≤
          3 * (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo) := by
        have h1 : (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dm) ≤
            (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        have h2 : 0 ≤ (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo) := by positivity
        have h3 : 3 * (IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo) =
            3 * ((IK.val rcU * (IK.val Th) ^ 2) / (2 * IK.val Dlo)) := by ring
        linarith
      linarith

private theorem poiArcSum_mem_and_bound
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (quarter : ℕ) {s0 s1 : QF}
    (hs0_den : 0 < s0.2) (hs1_den : 0 < s1.2)
    (hs0_nonneg : 0 ≤ IK.val s0) (hs01 : IK.val s0 < IK.val s1) :
    let sm := qhalf (qadd s0 s1)
    let Th := qdiv (qsub s1 s0) (qadd (1, 1) (qsq s0))
    ∃ Up : ℝ,
      IV.mem (sumI (R.data.full.map fun c => poiArc fieldMode c (wX quarter sm) (wY sm) Th)) Up ∧
      ∀ s, IK.val s0 ≤ s → s ≤ IK.val s1 →
        (∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖ ∂v13PoissonMeasure R.data.full) ≤ Up := by
  intro sm Th
  rcases v13DecodedRows_poisson_split R with ⟨_, _, _, _, hmult⟩
  have hrow_props : ∀ c ∈ R.data.full,
      0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
        c.w.2 = U ∧ c.w.1 ≤ (U : Int) ∧
        (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
    intro c hc
    have hok := (List.all_eq_true.mp hR.full_ok) c hc
    rcases of_decide_eq_true hok with ⟨_, _, hwU, _, _, _⟩
    rcases v13PrOk_props hok with ⟨hcx2, hcy2, hw2, hw1, _, _, hrad, _⟩
    exact ⟨hcx2, hcy2, hw2, hw1, hwU, (hmult c hc).2, hrad⟩
  rcases sumI_map_exists_upper R.data.full
    (fun c => poiArc fieldMode c (wX quarter sm) (wY sm) Th)
    (fun s c => IK.val c.w *
      ((1 / 2 : ℝ) * Real.log
        (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
          ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2)))
    (a0 := IK.val s0) (b0 := IK.val s1)
    (fun c hc => poiArc_mem_and_bound c (hrow_props c hc) quarter hs0_den hs1_den hs0_nonneg hs01)
    with ⟨Up, hUp_mem, hUp_le⟩
  refine ⟨Up, hUp_mem, ?_⟩
  intro s hs0 hs1
  have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
    intro c hc
    rcases hR.full_rows_data c hc with ⟨_, _, hw2, hw1, _, _, _, hnorm⟩
    exact ⟨hw1, hw2, hnorm⟩
  rw [integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex R.data.full
    (v13ArcPoint quarter s) hrows]
  have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
        ∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
      R.data.full.map (fun c => IK.val c.w *
        ((1 / 2 : ℝ) * Real.log
          (((v13ArcPoint quarter s).re - IK.val c.cx) ^ 2 +
            ((v13ArcPoint quarter s).im - IK.val c.cy) ^ 2))) := by
    refine List.map_congr_left (fun c hc => ?_)
    have hnorm := (hrows c hc).2.2
    have hw_out : (3 / 5 : ℝ) ≤ ‖v13ArcPoint quarter s‖ :=
      le_of_eq (norm_v13ArcPoint quarter s).symm
    have hcmult : (c.mult : ℝ) = 1 := by exact_mod_cast (hmult c hc).1
    rw [hcmult, one_mul, integral_v13GlobalCirclePoissonMeasure_outside_complex hnorm hw_out]
    rfl
  rw [hmap]
  exact hUp_le s hs0 hs1

/-! ## Section 4: Circle-arc cell soundness `v13_field_arc_cell_on` -/

private theorem v13_μz_integral_log_norm_sub_complex
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R)) (w : ℂ) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂(v13RefMeasure R N).μz) =
      (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure R.data.zp) +
        (∫ z : ℂ, Real.log ‖w - z‖ ∂v13PoissonMeasure R.data.full) := by
  change (∫ z : ℂ, Real.log ‖w - z‖
    ∂(v13DecodedChainMeasure R.data.zp + v13PoissonMeasure R.data.full)) = _
  have hIntZ := integrable_v13DecodedChainMeasure_log_norm_sub_uncond R.data.zp w
  have hIntP := integrable_v13PoissonMeasure_log_norm_sub_complex R.data.full w
    (fun c hc => (v13PrOk_props ((List.all_eq_true.mp (v13DecodedRows_full_ok R)) c hc)).2.2.2.2.2.2.2)
  exact integral_add_measure hIntZ hIntP

/-- Circle-arc cell soundness (`S3`) on `[0, 1]` for `quarter = 1` (`.arc1`) and
`quarter = 2` (`.arc2`). -/
theorem v13_field_arc_cell_on {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (quarter : ℕ) (hqt : quarter = 1 ∨ quarter = 2)
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    CellSoundnessOn (0, 1) (1, 1)
      (fieldUB R.data q lr (if quarter = 1 then .arc1 else .arc2))
      (fun s => V.signedVFullFieldZ (v13RefMeasure R N) (v13ArcPoint quarter s)) := by
  intro s0 s1 hs0_den hs1_den hlo hs01 _hhi
  have hs0_nonneg : 0 ≤ IK.val s0 := by
    have h0 : IK.val (0, 1) = 0 := by norm_num [IK.val]
    linarith
  let sa := if quarter = 1 then s0 else s1
  let sb := if quarter = 1 then s1 else s0
  let sm := qhalf (qadd s0 s1)
  let Th := qdiv (qsub s1 s0) (qadd (1, 1) (qsq s0))
  have hsa_den : 0 < sa.2 := by dsimp [sa]; split_ifs <;> assumption
  have hsb_den : 0 < sb.2 := by dsimp [sb]; split_ifs <;> assumption
  rcases poiArcSum_mem_and_bound R hR quarter hs0_den hs1_den hs0_nonneg hs01
    with ⟨Up, hUp_mem, hUp_le⟩
  let Uz := - (R.data.zp.map fun p =>
    IK.val p.J * vEnergyA (IK.val p.e - IK.val (wX quarter sa)) (IK.val (wY sa))).sum
  let Uv := - (R.data.vp.map fun p =>
    IK.val p.J * vEnergyA (IK.val p.e - IK.val (wX quarter sb)) (IK.val (wY sb))).sum
  let Ulog := - ((5 / 4 : ℝ) * Real.log (3 / 5 : ℝ))
  refine ⟨(2 * (Uz + Up) + Uv) + Ulog, ?_, ?_⟩
  · have hfieldUB : fieldUB R.data q lr (if quarter = 1 then .arc1 else .arc2) s0 s1 =
        fzArcUB fieldMode R.data quarter s0 s1 lr := by
      rcases hqt with rfl | rfl <;> rfl
    rw [hfieldUB]
    unfold fzArcUB
    have hUz : IV.mem (uChainAt fieldMode R.data.zp (wX quarter sa) (wY sa)) Uz :=
      uChainAt_mem fieldMode R.data.zp (wX_den_pos quarter hsa_den) (wY_den_pos hsa_den) hR.z_rows
    have hUzp : IV.mem (IK.add (uChainAt fieldMode R.data.zp (wX quarter sa) (wY sa))
        (sumI (R.data.full.map fun c => poiArc fieldMode c (wX quarter sm) (wY sm) Th)))
        (Uz + Up) :=
      IK.add_mem hUz hUp_mem
    have h2Uzp : IV.mem (smulInt 2 (IK.add (uChainAt fieldMode R.data.zp (wX quarter sa) (wY sa))
        (sumI (R.data.full.map fun c => poiArc fieldMode c (wX quarter sm) (wY sm) Th))))
        (2 * (Uz + Up)) := by
      simpa using IK.smulInt_mem 2 hUzp
    have hUv : IV.mem (uChainAt fieldMode R.data.vp (wX quarter sb) (wY sb)) Uv :=
      uChainAt_mem fieldMode R.data.vp (wX_den_pos quarter hsb_den) (wY_den_pos hsb_den)
        (fun p hp => ⟨(hR.v_rows p hp).2.1, (hR.v_rows p hp).2.2⟩)
    have hlog : IV.mem (IK.neg (smulQ (5, 4) lr)) Ulog := by
      have h := IK.smulQ_mem (c := (5, 4)) (by decide) hlr
      have h54 : IK.val (5, 4) = (5 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.neg_mem (IK.mem_of_eq h (by rw [h54]))
    exact IK.add_mem (IK.add_mem h2Uzp hUv) hlog
  · intro s hs0 hs1
    unfold V.signedVFullFieldZ V.signedVFieldZ
    dsimp only
    rw [show (v13RefMeasure R N).μv = v13DecodedChainMeasure R.data.vp by rfl]
    rw [v13_μz_integral_log_norm_sub_complex R N (v13ArcPoint quarter s)]
    rw [norm_v13ArcPoint quarter s]
    have hz_le : (∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖
        ∂v13DecodedChainMeasure R.data.zp) ≤ Uz :=
      integral_zp_v13ArcPoint_le_sa R hR quarter hs0_den hs1_den hs0_nonneg hs0 hs1
    have hp_le := hUp_le s hs0 hs1
    have hv_le : (∫ z : ℂ, Real.log ‖v13ArcPoint quarter s - z‖
        ∂v13DecodedChainMeasure R.data.vp) ≤ Uv :=
      integral_vp_v13ArcPoint_le_sb R hR quarter hs0_den hs1_den hs0_nonneg hs0 hs1
    dsimp [Ulog]
    linarith

/-! ## Section 5: Upper-arc cover `v13_upperArc_cover` -/

private theorem sin_div_cos_mul_cos (α : ℝ) (hcos : Real.cos α ≠ 0) :
    Real.sin α / Real.cos α * Real.cos α = Real.sin α := by
  first
    | exact div_mul_cancel₀ (Real.sin α) hcos
    | field_simp

/-- `cos 2α = (1 - tan² α)/(1 + tan² α)`; proved by clearing the (positive) denominator and an
explicit `linear_combination` with `u = sin α / cos α`, `u * cos α = sin α`. -/
private theorem cos_two_mul_eq_tan (α : ℝ) (hcos : Real.cos α ≠ 0) :
    Real.cos (2 * α) = (1 - Real.tan α ^ 2) / (1 + Real.tan α ^ 2) := by
  have h1 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq α
  have hu : Real.sin α / Real.cos α * Real.cos α = Real.sin α := sin_div_cos_mul_cos α hcos
  have hden : 1 + (Real.sin α / Real.cos α) ^ 2 ≠ 0 := by positivity
  rw [Real.cos_two_mul', Real.tan_eq_sin_div_cos, eq_div_iff hden]
  -- (c²-s²)(1+u²) - (1-u²) = (1-u²)(c²+s²-1) + 2(uc+s)(uc-s)
  linear_combination (1 - (Real.sin α / Real.cos α) ^ 2) * h1 +
    2 * (Real.sin α / Real.cos α * Real.cos α + Real.sin α) * hu

/-- `sin 2α = 2 tan α/(1 + tan² α)`, same method as `cos_two_mul_eq_tan`. -/
private theorem sin_two_mul_eq_tan (α : ℝ) (hcos : Real.cos α ≠ 0) :
    Real.sin (2 * α) = 2 * Real.tan α / (1 + Real.tan α ^ 2) := by
  have h1 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq α
  have hu : Real.sin α / Real.cos α * Real.cos α = Real.sin α := sin_div_cos_mul_cos α hcos
  have hden : 1 + (Real.sin α / Real.cos α) ^ 2 ≠ 0 := by positivity
  rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos, eq_div_iff hden]
  -- 2sc(1+u²) - 2u = 2u(c²+s²-1) + (2us-2c)(uc-s)
  linear_combination (2 * (Real.sin α / Real.cos α)) * h1 +
    (2 * (Real.sin α / Real.cos α) * Real.sin α - 2 * Real.cos α) * hu

/-- Componentwise form of `circleMap` centred at `0`. -/
private theorem circleMap_zero_eq_mk (r θ : ℝ) :
    circleMap 0 r θ = ⟨r * Real.cos θ, r * Real.sin θ⟩ := by
  apply Complex.ext
  · first
      | (simp only [circleMap, zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]; done)
      | simp [circleMap, Complex.exp_re, Complex.exp_im]
  · first
      | (simp only [circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]; done)
      | simp [circleMap, Complex.exp_re, Complex.exp_im]

private theorem tan_mem_Icc_zero_one {α : ℝ} (h0 : 0 ≤ α) (h4 : α ≤ Real.pi / 4) :
    Real.tan α ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hα_mem : α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have h4_mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  constructor
  · rw [← Real.tan_zero]
    exact Real.strictMonoOn_tan.monotoneOn h0_mem hα_mem h0
  · rw [← Real.tan_pi_div_four]
    exact Real.strictMonoOn_tan.monotoneOn hα_mem h4_mem h4

/-- Every point `V.vUpperArc t` (`t ∈ [0, 1]`) is covered by the rational quarter-circle
parametrisation `v13ArcPoint quarter s` for `quarter ∈ {1, 2}` and `s ∈ [0, 1]`. -/
theorem v13_upperArc_cover (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ quarter ∈ ({1, 2} : Finset ℕ), ∃ s ∈ Set.Icc (0 : ℝ) 1,
      V.vUpperArc t = v13ArcPoint quarter s := by
  rcases ht with ⟨ht0, ht1⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hhalf : t ≤ (1 / 2 : ℝ)
  · let α := Real.pi * t / 2
    have hα0 : 0 ≤ α := by dsimp [α]; positivity
    have hα4 : α ≤ Real.pi / 4 := by dsimp [α]; nlinarith
    have hcos_pos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    refine ⟨1, by simp, Real.tan α, tan_mem_Icc_zero_one hα0 hα4, ?_⟩
    have h2α : 2 * α = Real.pi * t := by dsimp [α]; ring
    have hc := cos_two_mul_eq_tan α hcos_pos.ne'
    have hs := sin_two_mul_eq_tan α hcos_pos.ne'
    rw [V.vUpperArc, ContourKit.p0CirclePoint_eq_circleMap, circleMap_zero_eq_mk]
    apply Complex.ext
    · show (3 / 5 : ℝ) * Real.cos (Real.pi * t) =
        (if (1 : ℕ) = 1 then (1 : ℝ) else -1) * (3 / 5) * (1 - Real.tan α ^ 2) /
          (1 + Real.tan α ^ 2)
      rw [← h2α, if_pos (rfl : (1 : ℕ) = 1), hc]
      ring
    · show (3 / 5 : ℝ) * Real.sin (Real.pi * t) =
        (3 / 5) * (2 * Real.tan α) / (1 + Real.tan α ^ 2)
      rw [← h2α, hs]
      ring
  · push_neg at hhalf
    let α := (Real.pi - Real.pi * t) / 2
    have hα0 : 0 ≤ α := by dsimp [α]; nlinarith
    have hα4 : α ≤ Real.pi / 4 := by dsimp [α]; nlinarith
    have hcos_pos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    refine ⟨2, by simp, Real.tan α, tan_mem_Icc_zero_one hα0 hα4, ?_⟩
    have h2α : 2 * α = Real.pi - Real.pi * t := by dsimp [α]; ring
    have hcos : Real.cos (Real.pi * t) = -Real.cos (2 * α) := by
      rw [h2α, Real.cos_pi_sub, neg_neg]
    have hsin : Real.sin (Real.pi * t) = Real.sin (2 * α) := by
      rw [h2α, Real.sin_pi_sub]
    have hc := cos_two_mul_eq_tan α hcos_pos.ne'
    have hs := sin_two_mul_eq_tan α hcos_pos.ne'
    rw [V.vUpperArc, ContourKit.p0CirclePoint_eq_circleMap, circleMap_zero_eq_mk]
    apply Complex.ext
    · show (3 / 5 : ℝ) * Real.cos (Real.pi * t) =
        (if (2 : ℕ) = 1 then (1 : ℝ) else -1) * (3 / 5) * (1 - Real.tan α ^ 2) /
          (1 + Real.tan α ^ 2)
      rw [hcos, if_neg (show ¬ ((2 : ℕ) = 1) by decide), hc]
      ring
    · show (3 / 5 : ℝ) * Real.sin (Real.pi * t) =
        (3 / 5) * (2 * Real.tan α) / (1 + Real.tan α ^ 2)
      rw [hsin, hs]
      ring

/-! ## Section 6: Conjugation symmetry of `signedVFullFieldZ` and lower-arc reflection -/

private theorem integral_v13GlobalCirclePoissonMeasure_log_norm_sub_conj
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    (∫ z : ℂ, Real.log ‖starRingEnd ℂ w - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      ∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure (starRingEnd ℂ p) := by
  have hp_conj : ‖starRingEnd ℂ p‖ < v13GlobalPoissonRadius := by
    simpa [norm_conj] using hp
  by_cases hw : (3 / 5 : ℝ) ≤ ‖w‖
  · have hw_conj : (3 / 5 : ℝ) ≤ ‖starRingEnd ℂ w‖ := by simpa [norm_conj] using hw
    rw [integral_v13GlobalCirclePoissonMeasure_outside_complex hp hw_conj,
      integral_v13GlobalCirclePoissonMeasure_outside_complex hp_conj hw]
    congr 2
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  · push_neg at hw
    have hw_le : ‖w‖ ≤ (3 / 5 : ℝ) := le_of_lt hw
    have hw_conj : ‖starRingEnd ℂ w‖ ≤ (3 / 5 : ℝ) := by simpa [norm_conj] using hw_le
    rw [integral_v13GlobalCirclePoissonMeasure_inside_complex hp hw_conj,
      integral_v13GlobalCirclePoissonMeasure_inside_complex hp_conj hw_le]
    congr 3
    simp only [Complex.conj_re, Complex.conj_im]
    ring

private theorem sum_poissonFull_conj_invariant
    (pts : List Li2Lean.V.Q2Certificate.PoissonPoint)
    (hlast : ∀ p ∈ pts.getLast?, p.yUnits = 0)
    (G H : Li2Lean.V.Q2Certificate.PoissonPoint → ℝ)
    (hGH : ∀ p, G p = H (Li2Lean.V.Q2Certificate.conjugatePoisson p))
    (hHG : ∀ p, G (Li2Lean.V.Q2Certificate.conjugatePoisson p) = H p) :
    ((Li2Lean.V.Q2Certificate.poissonFull pts).map G).sum =
      ((Li2Lean.V.Q2Certificate.poissonFull pts).map H).sum := by
  -- Split off the last point instead of inducting on the list.
  have hsplit : pts = [] ∨ ∃ (L : List Li2Lean.V.Q2Certificate.PoissonPoint)
      (b : Li2Lean.V.Q2Certificate.PoissonPoint), pts = L ++ [b] := by
    cases hrev : pts.reverse with
    | nil =>
        left
        simpa using hrev
    | cons b L' =>
        right
        refine ⟨L'.reverse, b, ?_⟩
        first
          | (rw [← List.reverse_reverse pts, hrev, List.reverse_cons])
          | simpa using congrArg List.reverse hrev
  rcases hsplit with hnil | ⟨L, b, hpts⟩
  · subst hnil
    simp [Li2Lean.V.Q2Certificate.poissonFull]
  · subst hpts
    have hb : b.yUnits = 0 := hlast b (by
      first
        | simp
        | (rw [List.getLast?_concat]; rfl))
    have hcb : Li2Lean.V.Q2Certificate.conjugatePoisson b = b := by
      cases b
      dsimp [Li2Lean.V.Q2Certificate.conjugatePoisson] at hb ⊢
      congr
      omega
    have hdl : (L ++ [b]).dropLast = L := List.dropLast_concat
    have e1 : (L.map (G ∘ Li2Lean.V.Q2Certificate.conjugatePoisson)).sum = (L.map H).sum := by
      congr 1
      exact List.map_congr_left (fun p _ => hHG p)
    have e2 : (L.map (H ∘ Li2Lean.V.Q2Certificate.conjugatePoisson)).sum = (L.map G).sum := by
      congr 1
      exact List.map_congr_left (fun p _ => (hGH p).symm)
    have hbGH : G b = H b := by rw [hGH b, hcb]
    unfold Li2Lean.V.Q2Certificate.poissonFull
    rw [hdl]
    simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
      List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    first
      | linarith [e1, e2, hbGH]
      | (rw [e1, e2, hbGH]; ring)

/-- Conjugation symmetry of `V.signedVFullFieldZ` for any decoded v13 reference measure. -/
theorem signedVFullFieldZ_v13RefMeasure_conj {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R)) (w : ℂ) :
    V.signedVFullFieldZ (v13RefMeasure R N) (starRingEnd ℂ w) =
      V.signedVFullFieldZ (v13RefMeasure R N) w := by
  have hchain_conj : ∀ rows : List CP,
      (∫ z : ℂ, Real.log ‖starRingEnd ℂ w - z‖ ∂v13DecodedChainMeasure rows) =
        ∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure rows := by
    intro rows
    let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map, hEmb.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hconj : starRingEnd ℂ (w - (u : ℂ)) = starRingEnd ℂ w - (u : ℂ) := by simp
    change Real.log ‖starRingEnd ℂ w - (u : ℂ)‖ = Real.log ‖w - (u : ℂ)‖
    have hn : ‖starRingEnd ℂ w - (u : ℂ)‖ = ‖w - (u : ℂ)‖ := by
      rw [← hconj, norm_conj]
    rw [hn]
  have hpoi_conj :
      (∫ z : ℂ, Real.log ‖starRingEnd ℂ w - z‖ ∂v13PoissonMeasure R.data.full) =
        ∫ z : ℂ, Real.log ‖w - z‖ ∂v13PoissonMeasure R.data.full := by
    have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
        ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
      intro c hc
      rcases v13PrOk_props ((List.all_eq_true.mp (v13DecodedRows_full_ok R)) c hc)
        with ⟨_, _, hw2, hw1, _, _, _, hnorm⟩
      exact ⟨hw1, hw2, hnorm⟩
    rw [integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex R.data.full (starRingEnd ℂ w) hrows,
      integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex R.data.full w hrows]
    have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
          ∫ z : ℂ, Real.log ‖starRingEnd ℂ w - z‖
            ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
        R.data.full.map (fun c => (c.mult : ℝ) * IK.val c.w *
          ∫ z : ℂ, Real.log ‖w - z‖
            ∂v13GlobalCirclePoissonMeasure (starRingEnd ℂ (v13PoissonPoint c))) := by
      refine List.map_congr_left (fun c hc => ?_)
      rw [integral_v13GlobalCirclePoissonMeasure_log_norm_sub_conj (hrows c hc).2.2 w]
    rw [hmap]
    rcases v13DecodedRows_poisson_split R with ⟨pts, _, hfull, hlast, _⟩
    rw [hfull, List.map_map, List.map_map]
    have hpt_conj : ∀ pt : Li2Lean.V.Q2Certificate.PoissonPoint,
        v13PoissonPoint (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson pt)) =
          starRingEnd ℂ (v13PoissonPoint (prow 1 pt)) := by
      intro pt
      unfold v13PoissonPoint prow Li2Lean.V.Q2Certificate.conjugatePoisson IK.val
      apply Complex.ext <;> dsimp <;> push_cast <;> ring
    have hcp_inv : ∀ pt : Li2Lean.V.Q2Certificate.PoissonPoint,
        Li2Lean.V.Q2Certificate.conjugatePoisson (Li2Lean.V.Q2Certificate.conjugatePoisson pt) =
          pt := by
      intro pt
      cases pt
      simp [Li2Lean.V.Q2Certificate.conjugatePoisson]
    refine sum_poissonFull_conj_invariant pts hlast
      (fun pt => ((prow 1 pt).mult : ℝ) * IK.val (prow 1 pt).w *
        ∫ z : ℂ, Real.log ‖w - z‖
          ∂v13GlobalCirclePoissonMeasure (starRingEnd ℂ (v13PoissonPoint (prow 1 pt))))
      (fun pt => ((prow 1 pt).mult : ℝ) * IK.val (prow 1 pt).w *
        ∫ z : ℂ, Real.log ‖w - z‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint (prow 1 pt)))
      (fun pt => ?_) (fun pt => ?_)
    · rw [← hpt_conj pt]
      rfl
    · have h := hpt_conj (Li2Lean.V.Q2Certificate.conjugatePoisson pt)
      rw [hcp_inv pt] at h
      rw [← h]
      rfl
  unfold V.signedVFullFieldZ V.signedVFieldZ
  rw [show (v13RefMeasure R N).μv = v13DecodedChainMeasure R.data.vp by rfl]
  rw [v13_μz_integral_log_norm_sub_complex R N (starRingEnd ℂ w),
    v13_μz_integral_log_norm_sub_complex R N w,
    hchain_conj R.data.zp, hchain_conj R.data.vp, hpoi_conj, norm_conj]

/-- Every point on the lower semicircle `V.vLowerArc t` is the complex conjugate of
`V.vUpperArc (1 - t)` (`1 - t ∈ [0, 1]` when `t ∈ [0, 1]`). -/
theorem vLowerArc_eq_conj_vUpperArc (t : ℝ) :
    V.vLowerArc t = starRingEnd ℂ (V.vUpperArc (1 - t)) := by
  unfold V.vLowerArc V.vUpperArc
  have hangle : Real.pi * (1 - t) = Real.pi - Real.pi * t := by ring
  have hshift : Real.pi + Real.pi * t = Real.pi * t + Real.pi := by ring
  rw [ContourKit.p0CirclePoint_eq_circleMap, ContourKit.p0CirclePoint_eq_circleMap,
    circleMap_zero_eq_mk, circleMap_zero_eq_mk]
  apply Complex.ext
  · rw [Complex.conj_re]
    show vContourRadius * Real.cos (Real.pi + Real.pi * t) =
      vContourRadius * Real.cos (Real.pi * (1 - t))
    rw [hshift, Real.cos_add_pi, hangle, Real.cos_pi_sub]
  · rw [Complex.conj_im]
    show vContourRadius * Real.sin (Real.pi + Real.pi * t) =
      -(vContourRadius * Real.sin (Real.pi * (1 - t)))
    rw [hshift, Real.sin_add_pi, hangle, Real.sin_pi_sub]
    ring

end

end Li2Lean.B3
