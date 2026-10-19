/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
import Li2Lean.B3.EnergySoundnessMeasureFacts
import Li2Lean.B3.Q2ReferencePackageFacts
import Li2Lean.B3.Q3ReferenceRowBounds
import Li2Lean.B3.Q4ReferenceZSourceBounds
import Li2Lean.B3.Q6ReferenceSupportLow
import Li2Lean.B3.Q7ReferenceMeasureFacts
import Li2Lean.B3.V13ChainLogEndpoint
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.P0.TubeExteriorBoundary
import Li2Lean.V.EnergyCertI.ISoundEval

/-!
# Shared Row-Fact Bundle and Potential Lemmas for v13 Reference Measures (`H6-S7` / `H6-S3`)

This module provides the `q`-generic infrastructure shared across the H6 reference-package
soundness proofs (`V13TotalIdentity.lean`, `V13ArcCell.lean`, `V13FieldCellGeneric.lean`):

1. `v13PrOk` and `V13FieldRowFacts`: the finite row-well-formedness bundle for an arbitrary
   decoded source `R : V13DecodedRows q`, together with unconditional consequences of `R.source`
   (`v13DecodedRows_z_source_bounds` and `v13DecodedRows_poisson_split`).
2. General rational-pair (`QF`) arithmetic and summation-by-parts helpers (`v13ChainCells_diff_sum`,
   `half_log_quadratic_upper`).
3. Complex-source chain potential evaluation (`integral_v13DecodedChainMeasure_log_norm_sub_eq_vEnergyA`),
   valid for every `w : ℂ` (both on and off the real axis).
4. Complex-source Poisson harmonic-measure circle-average identities
   (`integral_v13GlobalCirclePoissonMeasure_outside_complex` and
   `integral_v13GlobalCirclePoissonMeasure_inside_complex`) and their `full`/`pre` row-sum
   counterparts.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Section 1: Finite row-well-formedness bundle `V13FieldRowFacts` -/

/-- Decidable check for a decoded Poisson row: denominator `U`, nonnegative weight,
nonzero centre, and radius strictly inside `3/5` (`30000000000000 / U = 3 / 5`). -/
def v13PrOk (c : PR) : Bool :=
  decide (c.cx.2 = U ∧ c.cy.2 = U ∧ c.w.2 = U ∧ 0 ≤ c.w.1 ∧
    0 < c.cx.1 ^ 2 + c.cy.1 ^ 2 ∧
    c.cx.1 ^ 2 + c.cy.1 ^ 2 < (30000000000000 : Int) ^ 2)

/-- Finite row-well-formedness facts for a decoded v13 reference table `R : V13DecodedRows q`. -/
structure V13FieldRowFacts {q : ℕ} (R : V13DecodedRows q) : Prop where
  x_cells : ∀ c ∈ v13ChainCells R.data.xp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
  v_cells : ∀ c ∈ v13ChainCells R.data.vp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
  z_cells : ∀ c ∈ v13ChainCells R.data.zp, c.left ≤ c.right ∧ 0 ≤ c.density
  x_rows : ∀ p ∈ R.data.xp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
  v_rows : ∀ p ∈ R.data.vp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
  z_rows : ∀ p ∈ R.data.zp, 0 < p.e.2 ∧ 0 < p.J.2
  x_jump : (R.data.xp.map fun p => IK.val p.J).sum = 0
  v_jump : (R.data.vp.map fun p => IK.val p.J).sum = 0
  z_jump : (R.data.zp.map fun p => IK.val p.J).sum = 0
  pre_ok : R.data.pre.all v13PrOk = true
  full_ok : R.data.full.all v13PrOk = true

theorem v13PrOk_props {c : PR} (h : v13PrOk c = true) :
    0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
      ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) ∧
      0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ∧
      (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
  unfold v13PrOk at h
  rcases of_decide_eq_true h with ⟨hcx2, hcy2, hw2, hw1, hpos, hlt⟩
  have hU : 0 < U := by norm_num [U]
  have hcxpos : 0 < c.cx.2 := hcx2.symm ▸ hU
  have hcypos : 0 < c.cy.2 := hcy2.symm ▸ hU
  have hwpos : 0 < c.w.2 := hw2.symm ▸ hU
  have hnot0 : ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) := by
    rintro ⟨hx0, hy0⟩
    rw [hx0, hy0] at hpos
    norm_num at hpos
  have hposR : (0 : ℝ) < (c.cx.1 : ℝ) ^ 2 + (c.cy.1 : ℝ) ^ 2 := by exact_mod_cast hpos
  have hltR : (c.cx.1 : ℝ) ^ 2 + (c.cy.1 : ℝ) ^ 2 < (30000000000000 : ℝ) ^ 2 := by
    exact_mod_cast hlt
  have hval_pos : 0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
    unfold IK.val
    rw [hcx2, hcy2]
    norm_num [U]
    nlinarith
  have hval_lt : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
    unfold IK.val
    rw [hcx2, hcy2]
    norm_num [U]
    nlinarith
  have hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num [v13GlobalPoissonRadius])]
    rw [Complex.sq_norm]
    simpa [v13PoissonPoint, v13GlobalPoissonRadius, Complex.normSq, pow_two] using hval_lt
  exact ⟨hcxpos, hcypos, hwpos, hw1, hnot0, hval_pos, hval_lt, hnorm⟩

theorem V13FieldRowFacts.pre_rows_data {q : ℕ} {R : V13DecodedRows q}
    (hR : V13FieldRowFacts R) :
    ∀ c ∈ R.data.pre,
      0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
        ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) ∧
        0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ∧
        (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 ∧
        ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
  intro c hc
  exact v13PrOk_props ((List.all_eq_true.mp hR.pre_ok) c hc)

theorem V13FieldRowFacts.full_rows_data {q : ℕ} {R : V13DecodedRows q}
    (hR : V13FieldRowFacts R) :
    ∀ c ∈ R.data.full,
      0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
        ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) ∧
        0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ∧
        (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 ∧
        ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
  intro c hc
  exact v13PrOk_props ((List.all_eq_true.mp hR.full_ok) c hc)

/-- Every decoded `z`-chain cell of any `R : V13DecodedRows q` lies in `[-q, -3/5]`. -/
theorem v13DecodedRows_z_source_bounds {q : ℕ} (R : V13DecodedRows q) :
    ∀ c ∈ v13ChainCells R.data.zp,
      (-(q : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  rcases R.source with ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩ | ⟨rfl, hD⟩
  · rw [hD]; simpa using v13_q2_z_source_bounds
  · rw [hD]; simpa using v13_q4_z_source_bounds
  · rw [hD]; simpa using v13_q5_z_source_bounds
  · rw [hD]; simpa using v13_q7_z_source_bounds
  · rw [hD]; simpa using v13_q6_z_source_bounds
  · rw [hD]; simpa [q3DecodedRows] using q3_decoded_row_bounds.z_source

private def v13FullRowAuxOk (c : PR) : Bool :=
  decide (c.mult = 1 ∧ c.w.1 ≤ (U : Int))

/-- Every `R : V13DecodedRows q` arises from a prefix list `pts` of `PoissonPoint`s with
`R.data.pre = preRowsI pts`, `R.data.full = (poissonFull pts).map (prow 1)`, real last point,
and unit multiplicity / weight bounded by `1` on `R.data.full`. -/
theorem v13DecodedRows_poisson_split {q : ℕ} (R : V13DecodedRows q) :
    ∃ pts : List Li2Lean.V.Q2Certificate.PoissonPoint,
      R.data.pre = preRowsI pts ∧
      R.data.full = (Li2Lean.V.Q2Certificate.poissonFull pts).map (prow 1) ∧
      (∀ p ∈ pts.getLast?, p.yUnits = 0) ∧
      (∀ c ∈ R.data.full, c.mult = 1 ∧ c.w.1 ≤ (U : Int)) := by
  rcases R.source with ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q2PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q2D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q4PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q4D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q5PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q5D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q7PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q7D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q6PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q6D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)
  · refine ⟨Li2Lean.V.Q2Certificate.decodePoisson q3PoissonPrefix,
      by rw [hD]; rfl, by rw [hD]; rfl, by decide, ?_⟩
    rw [hD]
    have hok : q3D.full.all v13FullRowAuxOk = true := by decide +kernel
    intro c hc
    exact of_decide_eq_true ((List.all_eq_true.mp hok) c hc)

theorem v13DecodedRows_pre_ok {q : ℕ} (R : V13DecodedRows q) :
    R.data.pre.all v13PrOk = true := by
  rcases R.source with ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ <;>
    { rw [hD]; decide +kernel }

theorem v13DecodedRows_full_ok {q : ℕ} (R : V13DecodedRows q) :
    R.data.full.all v13PrOk = true := by
  rcases R.source with ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ | ⟨_, hD⟩ <;>
    { rw [hD]; decide +kernel }

/-! ## Section 2: General `QF` arithmetic and summation-by-parts helpers -/

theorem val_qabs_local {s : QF} (hs : 0 < s.2) :
    IK.val (qabs s) = |IK.val s| := by
  change ((s.1.natAbs : ℝ) / (s.2 : ℝ)) = |(s.1 : ℝ) / (s.2 : ℝ)|
  rw [natAbs_cast, abs_div]
  have hsR : (0 : ℝ) < (s.2 : ℝ) := by exact_mod_cast hs
  rw [abs_of_pos hsR]

theorem val_qsq_local (s : QF) : IK.val (qsq s) = IK.val s ^ 2 := by
  change IK.val (qmul s s) = IK.val s ^ 2
  rw [val_qmul]
  ring

theorem val_qhalf_local (s : QF) : IK.val (qhalf s) = IK.val s / 2 := by
  unfold qhalf IK.val
  push_cast
  ring

theorem qmul_den_pos {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (qmul a b).2 :=
  Nat.mul_pos ha hb

theorem qsq_den_pos {a : QF} (ha : 0 < a.2) : 0 < (qsq a).2 :=
  Nat.mul_pos ha ha

theorem qhalf_den_pos {a : QF} (ha : 0 < a.2) : 0 < (qhalf a).2 :=
  Nat.mul_pos (by decide) ha

theorem qabs_den_pos {a : QF} (ha : 0 < a.2) : 0 < (qabs a).2 := ha

theorem qneg_den_pos {a : QF} (ha : 0 < a.2) : 0 < (qneg a).2 := ha

theorem qdiv_den_pos {a b : QF} (ha : 0 < a.2) (hb : b.1 ≠ 0) :
    0 < (qdiv a b).2 :=
  Nat.mul_pos ha (Int.natAbs_pos.mpr hb)

theorem fst_pos_of_val_pos {q : QF} (hq2 : 0 < q.2) (hval : 0 < IK.val q) :
    0 < q.1 := by
  unfold IK.val at hval
  have hden : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hq2
  have hnum : (0 : ℝ) < (q.1 : ℝ) := (div_pos_iff_of_pos_right hden).mp hval
  exact_mod_cast hnum

theorem clampQ_den_pos {t0 t1 x : QF}
    (ht0 : 0 < t0.2) (ht1 : 0 < t1.2) (hx : 0 < x.2) :
    0 < (clampQ t0 t1 x).2 := by
  unfold clampQ
  split_ifs <;> assumption

theorem clampQ_bounds_and_sq_le {t0 t1 x : QF}
    (ht0 : 0 < t0.2) (ht1 : 0 < t1.2) (hx : 0 < x.2)
    (hab : IK.val t0 ≤ IK.val t1) :
    IK.val t0 ≤ IK.val (clampQ t0 t1 x) ∧
      IK.val (clampQ t0 t1 x) ≤ IK.val t1 ∧
      (IK.val (clampQ t0 t1 x) - IK.val x) ^ 2 ≤
        ((IK.val t0 + IK.val t1) / 2 - IK.val x) ^ 2 := by
  unfold clampQ
  by_cases h1 : qlt x t0 = true
  · rw [if_pos h1]
    have hxlt : IK.val x < IK.val t0 := (qlt_spec hx ht0).mp h1
    refine ⟨le_rfl, hab, ?_⟩
    nlinarith
  · rw [if_neg h1]
    have hxge : IK.val t0 ≤ IK.val x := not_lt.mp (mt (qlt_spec hx ht0).mpr h1)
    by_cases h2 : qlt t1 x = true
    · rw [if_pos h2]
      have hxgt : IK.val t1 < IK.val x := (qlt_spec ht1 hx).mp h2
      refine ⟨hab, le_rfl, ?_⟩
      nlinarith
    · rw [if_neg h2]
      have hxle : IK.val x ≤ IK.val t1 := not_lt.mp (mt (qlt_spec ht1 hx).mpr h2)
      refine ⟨hxge, hxle, ?_⟩
      have hzero : (IK.val x - IK.val x) ^ 2 = 0 := by ring
      rw [hzero]
      exact sq_nonneg _

theorem list_sum_mul_sub_const {α : Type*} (xs : List α)
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

theorem v13ChainCellsAux_diff_sum
    (f : ℝ → ℝ) (h : ℝ) (rows : List CP) :
    ((v13ChainCellsAux h rows).map fun c => c.density *
      (f c.right - f c.left)).sum =
      h * (f (v13ChainRowsLast rows) - f (v13ChainRowsFirst rows)) +
      (rows.map fun p => IK.val p.J *
        (f (v13ChainRowsLast rows) - f (IK.val p.e))).sum := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainRowsFirst, v13ChainRowsLast]
  | cons c rows ih =>
      cases rows with
      | nil => simp [v13ChainCellsAux, v13ChainRowsFirst, v13ChainRowsLast]
      | cons d ds =>
          simp only [v13ChainCellsAux, List.map_cons, List.sum_cons,
            v13ChainRowsFirst, v13ChainRowsLast]
          have htail := ih (h + IK.val c.J)
          simp only [v13ChainRowsFirst] at htail
          rw [htail]
          simp only [List.map_cons, List.sum_cons]
          ring_nf

theorem v13ChainCells_diff_sum
    (f : ℝ → ℝ) (rows : List CP)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    ((v13ChainCells rows).map fun c => c.density *
      (f c.right - f c.left)).sum =
      - (rows.map fun p => IK.val p.J * f (IK.val p.e)).sum := by
  change ((v13ChainCellsAux 0 rows).map fun c => c.density *
      (f c.right - f c.left)).sum = _
  rw [v13ChainCellsAux_diff_sum]
  have hconst : (rows.map fun p => IK.val p.J * f (v13ChainRowsLast rows)).sum = 0 := by
    calc
      _ = (rows.map fun p => IK.val p.J).sum * f (v13ChainRowsLast rows) := by
        simp [List.sum_map_mul_right]
      _ = 0 := by rw [hsum]; simp
  simp only [zero_mul, zero_add]
  rw [list_sum_mul_sub_const rows (f (v13ChainRowsLast rows))
    (fun p => f (IK.val p.e)) (fun p => IK.val p.J), hconst, zero_sub]

theorem list_map_sum_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ c ∈ l, f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h c (by simp)) (ih fun d hd => h d (by simp [hd]))

theorem sumI_map_exists_upper {α : Type*} (l : List α)
    (f : α → IV) (g : ℝ → α → ℝ) {a0 b0 : ℝ}
    (h : ∀ c ∈ l, ∃ Uc : ℝ, IV.mem (f c) Uc ∧
      ∀ t, a0 ≤ t → t ≤ b0 → g t c ≤ Uc) :
    ∃ U : ℝ, IV.mem (sumI (l.map f)) U ∧
      ∀ t, a0 ≤ t → t ≤ b0 → (l.map (g t)).sum ≤ U := by
  classical
  let u : α → ℝ := fun c => if hc : c ∈ l then Classical.choose (h c hc) else 0
  refine ⟨(l.map u).sum, ?_, ?_⟩
  · apply IK.sumI_map_mem
    intro c hc
    dsimp [u]
    rw [dif_pos hc]
    exact (Classical.choose_spec (h c hc)).1
  · intro t hta htb
    refine list_map_sum_le l (g t) u (fun c hc => ?_)
    dsimp [u]
    rw [dif_pos hc]
    exact (Classical.choose_spec (h c hc)).2 t hta htb

theorem half_log_quadratic_upper
    {gt gm gmin A B t m hw : ℝ}
    (hgt : 0 < gt) (hgm : 0 < gm) (hgmin : 0 < gmin) (hgmin_le : gmin ≤ gm)
    (hB : 0 ≤ B) (hhw : 0 ≤ hw) (htm : |t - m| ≤ hw)
    (hquad : gt - gm = 2 * A * (t - m) + B * (t - m) ^ 2) :
    (1 / 2 : ℝ) * Real.log gt ≤
      (1 / 2 : ℝ) * Real.log gm + (|A / gm| * hw + B * hw ^ 2 / (2 * gmin)) := by
  have hdiv_pos : 0 < gt / gm := div_pos hgt hgm
  have hlog_div : Real.log gt - Real.log gm = Real.log (gt / gm) :=
    (Real.log_div (ne_of_gt hgt) (ne_of_gt hgm)).symm
  have hlog_le : Real.log (gt / gm) ≤ gt / gm - 1 :=
    Real.log_le_sub_one_of_pos hdiv_pos
  have hstep1 : (1 / 2 : ℝ) * Real.log gt - (1 / 2 : ℝ) * Real.log gm ≤
      (gt - gm) / (2 * gm) := by
    have h1 : gt / gm - 1 = (gt - gm) / gm := by
      field_simp [ne_of_gt hgm]
    have h2 : (gt - gm) / (2 * gm) = (1 / 2 : ℝ) * ((gt - gm) / gm) := by ring
    linarith
  have hstep2 : (gt - gm) / (2 * gm) =
      (A / gm) * (t - m) + B * (t - m) ^ 2 / (2 * gm) := by
    rw [hquad]
    field_simp [ne_of_gt hgm]
  have hlin : (A / gm) * (t - m) ≤ |A / gm| * hw := by
    calc
      (A / gm) * (t - m) ≤ |(A / gm) * (t - m)| := le_abs_self _
      _ = |A / gm| * |t - m| := abs_mul _ _
      _ ≤ |A / gm| * hw := mul_le_mul_of_nonneg_left htm (abs_nonneg _)
  have hsq : (t - m) ^ 2 ≤ hw ^ 2 := by
    rw [← sq_abs]
    exact sq_le_sq₀ (abs_nonneg _) hhw |>.mpr htm
  have hquad_le : B * (t - m) ^ 2 / (2 * gm) ≤ B * hw ^ 2 / (2 * gmin) := by
    have hnum : B * (t - m) ^ 2 ≤ B * hw ^ 2 := mul_le_mul_of_nonneg_left hsq hB
    have h1 : B * (t - m) ^ 2 / (2 * gm) ≤ B * hw ^ 2 / (2 * gm) :=
      div_le_div_of_nonneg_right hnum (by linarith)
    have h2 : B * hw ^ 2 / (2 * gm) ≤ B * hw ^ 2 / (2 * gmin) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    exact le_trans h1 h2
  linarith

/-! ## Section 3: Almost-everywhere support lemmas for `v13ChainMeasure` -/

theorem ae_nonneg_v13ChainMeasure
    (cells : List V13ChainCell)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right) :
    ∀ᵐ u ∂v13ChainMeasure cells, 0 ≤ u := by
  rw [ae_iff]
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, 0 ≤ d.left ∧ d.left ≤ d.right :=
        fun d hd => hbounds d (by simp [hd])
      have h0l := (hbounds c hc).1
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      have hmeas : MeasurableSet {u : ℝ | ¬ 0 ≤ u} := measurableSet_Ici.compl
      rw [hsplit, Measure.add_apply, Measure.smul_apply,
        Measure.restrict_apply hmeas]
      have hempty : {u : ℝ | ¬ 0 ≤ u} ∩ Ioc c.left c.right = ∅ := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hnot hlu
        linarith
      rw [hempty, measure_empty, smul_zero, zero_add]
      exact ih hrest

theorem ae_le_of_right_le_v13ChainMeasure
    (cells : List V13ChainCell) {b : ℝ}
    (hbounds : ∀ c ∈ cells, c.right ≤ b) :
    ∀ᵐ u ∂v13ChainMeasure cells, u ≤ b := by
  rw [ae_iff]
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, d.right ≤ b := fun d hd => hbounds d (by simp [hd])
      have hrb := hbounds c hc
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      have hmeas : MeasurableSet {u : ℝ | ¬ u ≤ b} := measurableSet_Iic.compl
      rw [hsplit, Measure.add_apply, Measure.smul_apply,
        Measure.restrict_apply hmeas]
      have hempty : {u : ℝ | ¬ u ≤ b} ∩ Ioc c.left c.right = ∅ := by
        ext u
        constructor
        · rintro ⟨hnot, hIoc⟩
          exact (hnot (le_trans hIoc.2 hrb)).elim
        · intro hu
          exact (by simpa using hu : False).elim
      rw [hempty, measure_empty, smul_zero, zero_add]
      exact ih hrest

theorem ae_ne_v13ChainMeasure (cells : List V13ChainCell) (t : ℝ) :
    ∀ᵐ u ∂v13ChainMeasure cells, u ≠ t := by
  rw [ae_iff]
  have hset : {u : ℝ | ¬ u ≠ t} = {t} := by ext u; simp
  rw [hset]
  exact v13ChainMeasure_singleton cells t

/-! ## Section 4: Complex-source chain potential (`vEnergyA`) -/

theorem primitive_neg (x : ℝ) :
    LogSegment.primitive (-x) = -LogSegment.primitive x := by
  simp only [LogSegment.primitive, abs_neg]
  ring

theorem vEnergyA_neg (s y : ℝ) : vEnergyA (-s) y = -vEnergyA s y := by
  by_cases hy : y = 0
  · by_cases hs : s = 0
    · simp [vEnergyA, hy, hs]
    · have hns : -s ≠ 0 := neg_ne_zero.mpr hs
      simp [vEnergyA, hy, hs, hns, primitive_neg]
      ring
  · simp only [vEnergyA, if_neg hy]
    have hdiv : (-s) / y = -(s / y) := by ring
    rw [hdiv, Real.arctan_neg]
    have hsq : (-s) ^ 2 + y ^ 2 = s ^ 2 + y ^ 2 := by ring
    rw [hsq]
    ring

theorem vEnergyA_zero_left (y : ℝ) : vEnergyA 0 y = 0 := by
  by_cases hy : y = 0 <;> simp [vEnergyA, hy, LogSegment.primitive]

private theorem log_norm_sub_ofReal_eq (w : ℂ) (u : ℝ) :
    Real.log ‖w - (u : ℂ)‖ =
      if w.im = 0 then Real.log |w.re - u|
      else Real.log ((w.re - u) ^ 2 + w.im ^ 2) / 2 := by
  split_ifs with him
  · have hw : w - (u : ℂ) = ((w.re - u : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hw, Complex.norm_real, Real.norm_eq_abs]
  · have hw : w - (u : ℂ) = ((w.re - u : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hpos : 0 < (w.re - u) ^ 2 + w.im ^ 2 := by positivity
    rw [hw, Complex.norm_add_mul_I, Real.log_sqrt hpos.le]

private theorem hasDerivAt_vEnergyA_im_ne_zero {y : ℝ} (hy : y ≠ 0) (s : ℝ) :
    HasDerivAt (fun v => vEnergyA v y) (Real.log (s ^ 2 + y ^ 2) / 2) s := by
  have hpos : 0 < s ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun v : ℝ => v ^ 2 + y ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (y ^ 2)
  have hlog := h1.log hpos.ne'
  have hA := (hasDerivAt_id s).mul (((hlog.const_mul (1 / 2 : ℝ))).sub_const 1)
  have hq : HasDerivAt (fun v : ℝ => v / y) (1 / y) s := by
    simpa using (hasDerivAt_id s).div_const y
  have hB := (hq.arctan).const_mul y
  have h := hA.add hB
  convert h using 1
  · funext v
    simp [vEnergyA, hy, id]
    ring
  · simp only [id]
    field_simp [hy, hpos.ne']
    ring

private theorem continuous_logsq_im_ne_zero {y : ℝ} (hy : y ≠ 0) :
    Continuous (fun s : ℝ => Real.log (s ^ 2 + y ^ 2) / 2) := by
  apply Continuous.div_const
  apply Continuous.log (by fun_prop)
  intro s
  positivity

theorem integrableOn_Ioc_log_norm_sub_complex (w : ℂ) {α β : ℝ} (hαβ : α ≤ β) :
    IntegrableOn (fun u : ℝ => Real.log ‖w - (u : ℂ)‖) (Ioc α β) volume := by
  by_cases him : w.im = 0
  · have hbase : IntegrableOn (fun u : ℝ => Real.log |w.re - u|) (Ioc α β) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mp
        (LogSegment.intervalIntegrable_log_abs_sub w.re α β)
    refine hbase.congr_fun (fun u _ => ?_) measurableSet_Ioc
    rw [log_norm_sub_ofReal_eq, if_pos him]
  · have hcont : Continuous (fun u : ℝ => Real.log ‖w - (u : ℂ)‖) := by
      have heq : (fun u : ℝ => Real.log ‖w - (u : ℂ)‖) =
          (fun u : ℝ => Real.log ((w.re - u) ^ 2 + w.im ^ 2) / 2) := by
        ext u
        rw [log_norm_sub_ofReal_eq, if_neg him]
      rw [heq]
      exact (continuous_logsq_im_ne_zero him).comp (continuous_const.sub continuous_id)
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem integral_Ioc_log_norm_sub_complex (w : ℂ) {α β : ℝ} (hαβ : α ≤ β) :
    (∫ u in Ioc α β, Real.log ‖w - (u : ℂ)‖) =
      vEnergyA (β - w.re) w.im - vEnergyA (α - w.re) w.im := by
  rw [← intervalIntegral.integral_of_le hαβ]
  by_cases him : w.im = 0
  · have hcongr : (∫ u in α..β, Real.log ‖w - (u : ℂ)‖) =
        ∫ u in α..β, Real.log |w.re - u| := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [log_norm_sub_ofReal_eq, if_pos him]
    rw [hcongr, LogSegment.integral_log_abs_sub]
    have h1 : LogSegment.primitive (w.re - α) = -LogSegment.primitive (α - w.re) := by
      rw [show w.re - α = -(α - w.re) by ring, primitive_neg]
    have h2 : LogSegment.primitive (w.re - β) = -LogSegment.primitive (β - w.re) := by
      rw [show w.re - β = -(β - w.re) by ring, primitive_neg]
    have hvA (s : ℝ) : vEnergyA s 0 = LogSegment.primitive s := by
      by_cases hs : s = 0
      · simp [vEnergyA, hs, LogSegment.primitive]
      · simp [vEnergyA, hs, LogSegment.primitive]
        ring
    rw [him, hvA, hvA]
    linarith
  · have hcongr : (∫ u in α..β, Real.log ‖w - (u : ℂ)‖) =
        ∫ u in α..β, Real.log ((w.re - u) ^ 2 + w.im ^ 2) / 2 := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [log_norm_sub_ofReal_eq, if_neg him]
    rw [hcongr]
    rw [intervalIntegral.integral_comp_sub_left
      (fun s => Real.log (s ^ 2 + w.im ^ 2) / 2) w.re]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v => vEnergyA v w.im)
      (fun s _ => hasDerivAt_vEnergyA_im_ne_zero him s)
      ((continuous_logsq_im_ne_zero him).intervalIntegrable _ _)]
    have h1 : vEnergyA (w.re - α) w.im = -vEnergyA (α - w.re) w.im := by
      rw [show w.re - α = -(α - w.re) by ring, vEnergyA_neg]
    have h2 : vEnergyA (w.re - β) w.im = -vEnergyA (β - w.re) w.im := by
      rw [show w.re - β = -(β - w.re) by ring, vEnergyA_neg]
    linarith

theorem integrable_v13ChainMeasure_log_norm_sub_complex
    (cells : List V13ChainCell) (w : ℂ)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right) :
    Integrable (fun u : ℝ => Real.log ‖w - (u : ℂ)‖) (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hcell : Integrable (fun u : ℝ => Real.log ‖w - (u : ℂ)‖)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_log_norm_sub_complex w (hbounds c hc)).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure (ih hrest)

theorem integral_v13ChainMeasure_log_norm_sub_complex
    (cells : List V13ChainCell) (w : ℂ)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right)
    (hdensity : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ u : ℝ, Real.log ‖w - (u : ℂ)‖ ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        (vEnergyA (c.right - w.re) w.im - vEnergyA (c.left - w.re) w.im)).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrestB : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hrestD : ∀ d ∈ cs, 0 ≤ d.density := fun d hd => hdensity d (by simp [hd])
      have hcell : Integrable (fun u : ℝ => Real.log ‖w - (u : ℂ)‖)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_log_norm_sub_complex w (hbounds c hc)).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have htail := integrable_v13ChainMeasure_log_norm_sub_complex cs w hrestB
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell htail,
        integral_smul_measure, ENNReal.toReal_ofReal (hdensity c hc), smul_eq_mul,
        integral_Ioc_log_norm_sub_complex w (hbounds c hc), ih hrestB hrestD]
      simp

theorem integrable_v13DecodedChainMeasure_log_norm_sub_complex
    (rows : List CP) (w : ℂ)
    (hbounds : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right) :
    Integrable (fun z : ℂ => Real.log ‖w - z‖) (v13DecodedChainMeasure rows) := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [hEmb.integrable_map_iff]
  exact integrable_v13ChainMeasure_log_norm_sub_complex (v13ChainCells rows) w hbounds

theorem integrable_v13DecodedChainMeasure_log_norm_sub_uncond
    (rows : List CP) (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖w - z‖) (v13DecodedChainMeasure rows) := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [hEmb.integrable_map_iff]
  suffices ∀ cells : List V13ChainCell,
      Integrable (fun u : ℝ => Real.log ‖w - (u : ℂ)‖) (v13ChainMeasure cells) from
    this (v13ChainCells rows)
  intro cells
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hcell0 : IntegrableOn (fun u : ℝ => Real.log ‖w - (u : ℂ)‖)
          (Ioc c.left c.right) volume := by
        by_cases hle : c.left ≤ c.right
        · exact integrableOn_Ioc_log_norm_sub_complex w hle
        · rw [Set.Ioc_eq_empty (fun hlt => hle (le_of_lt hlt))]
          exact integrableOn_empty
      have hcell : Integrable (fun u : ℝ => Real.log ‖w - (u : ℂ)‖)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        hcell0.integrable.smul_measure ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure ih

theorem integral_v13DecodedChainMeasure_log_norm_sub_eq_vEnergyA
    (rows : List CP) (w : ℂ)
    (hbounds : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right)
    (hdensity : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure rows) =
      - (rows.map fun p => IK.val p.J * vEnergyA (IK.val p.e - w.re) w.im).sum := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap : (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure rows) =
      ∫ u : ℝ, Real.log ‖w - (u : ℂ)‖ ∂v13ChainMeasure (v13ChainCells rows) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap, integral_v13ChainMeasure_log_norm_sub_complex (v13ChainCells rows) w hbounds hdensity]
  exact v13ChainCells_diff_sum (fun u => vEnergyA (u - w.re) w.im) rows hsum

/-! ## Section 5: Complex-source Poisson circle-average and cloud lemmas -/

theorem integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖w - z‖)
      (v13GlobalCirclePoissonMeasure p) := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := w / (r : ℂ)
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have hmeas_f : AEStronglyMeasurable (fun z : ℂ => Real.log ‖w - z‖)
      (v13GlobalCirclePoissonMeasure p) :=
    (by fun_prop : Measurable (fun z : ℂ => Real.log ‖w - z‖)).aestronglyMeasurable
  unfold v13GlobalCirclePoissonMeasure
  rw [integrable_map_measure hmeas_f
    (continuous_circleMap 0 v13GlobalPoissonRadius).aemeasurable]
  have hmeas_d : Measurable (v13GlobalPoissonAngleDensity p) := by
    unfold v13GlobalPoissonAngleDensity poissonKernel
    fun_prop
  rw [integrable_withDensity_iff hmeas_d.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hInt1 : Integrable (fun θ : ℝ =>
      v13GlobalPoissonAngleDensity p θ * Real.log (3 / 5 : ℝ)) μ0 :=
    (integrable_v13GlobalPoissonAngleDensity hp).mul_const (Real.log (3 / 5 : ℝ))
  have hInt2 : Integrable (fun θ : ℝ =>
      (2 * Real.pi)⁻¹ * (poissonKernel 0 p' (circleMap 0 1 θ) *
        Real.log ‖circleMap 0 1 θ - a‖)) μ0 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp
      (P0.poisson_log_circleIntegrable (a := a) hp')).const_mul (2 * Real.pi)⁻¹
  refine (hInt1.add hInt2).congr ?_
  filter_upwards [P0.ae_circleMap_ne a μ0] with θ hθ
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (v13GlobalPoissonAngleDensity_nonneg hp θ)]
  have hr : r = (3 / 5 : ℝ) := by rfl
  have hfactor : w - circleMap 0 r θ =
      -(r : ℂ) * (circleMap 0 1 θ - a) := by
    dsimp [a, r, v13GlobalPoissonRadius, circleMap]
    push_cast
    ring
  have hnorm : ‖w - circleMap 0 r θ‖ =
      (3 / 5 : ℝ) * ‖circleMap 0 1 θ - a‖ := by
    rw [hfactor, norm_mul, norm_neg, hr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hne : ‖circleMap 0 1 θ - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ)
  rw [hnorm, Real.log_mul (by norm_num) hne]
  unfold v13GlobalPoissonAngleDensity
  dsimp [p', r]
  ring

theorem integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_complex
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      Real.log (3 / 5 : ℝ) +
        Real.circleAverage (fun ζ => poissonKernel 0 (p / (v13GlobalPoissonRadius : ℂ)) ζ *
          Real.log ‖ζ - w / (v13GlobalPoissonRadius : ℂ)‖) 0 1 := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := w / (r : ℂ)
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have hmeas_f : AEStronglyMeasurable (fun z : ℂ => Real.log ‖w - z‖)
      (v13GlobalCirclePoissonMeasure p) :=
    (by fun_prop : Measurable (fun z : ℂ => Real.log ‖w - z‖)).aestronglyMeasurable
  have hmeas_d : Measurable (v13GlobalPoissonAngleDensity p) := by
    unfold v13GlobalPoissonAngleDensity poissonKernel
    fun_prop
  unfold v13GlobalCirclePoissonMeasure
  rw [integral_map (continuous_circleMap 0 v13GlobalPoissonRadius).aemeasurable hmeas_f,
    integral_withDensity_eq_integral_toReal_smul hmeas_d.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hInt1 : Integrable (fun θ : ℝ =>
      v13GlobalPoissonAngleDensity p θ * Real.log (3 / 5 : ℝ)) μ0 :=
    (integrable_v13GlobalPoissonAngleDensity hp).mul_const (Real.log (3 / 5 : ℝ))
  have hInt2 : Integrable (fun θ : ℝ =>
      (2 * Real.pi)⁻¹ * (poissonKernel 0 p' (circleMap 0 1 θ) *
        Real.log ‖circleMap 0 1 θ - a‖)) μ0 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp
      (P0.poisson_log_circleIntegrable (a := a) hp')).const_mul (2 * Real.pi)⁻¹
  have hcongr : (∫ θ : ℝ, (ENNReal.ofReal (v13GlobalPoissonAngleDensity p θ)).toReal •
        Real.log ‖w - circleMap 0 r θ‖ ∂μ0) =
      ∫ θ : ℝ, (v13GlobalPoissonAngleDensity p θ * Real.log (3 / 5 : ℝ) +
        (2 * Real.pi)⁻¹ * (poissonKernel 0 p' (circleMap 0 1 θ) *
          Real.log ‖circleMap 0 1 θ - a‖)) ∂μ0 := by
    refine integral_congr_ae ?_
    filter_upwards [P0.ae_circleMap_ne a μ0] with θ hθ
    simp only [ENNReal.toReal_ofReal (v13GlobalPoissonAngleDensity_nonneg hp θ), smul_eq_mul]
    have hr : r = (3 / 5 : ℝ) := by rfl
    have hfactor : w - circleMap 0 r θ =
        -(r : ℂ) * (circleMap 0 1 θ - a) := by
      dsimp [a, r, v13GlobalPoissonRadius, circleMap]
      push_cast
      ring
    have hnorm : ‖w - circleMap 0 r θ‖ =
        (3 / 5 : ℝ) * ‖circleMap 0 1 θ - a‖ := by
      rw [hfactor, norm_mul, norm_neg, hr, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
    have hne : ‖circleMap 0 1 θ - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ)
    rw [hnorm, Real.log_mul (by norm_num) hne]
    unfold v13GlobalPoissonAngleDensity
    dsimp [p', r]
    ring
  rw [hcongr, integral_add hInt1 hInt2]
  have hterm1 : (∫ θ : ℝ, v13GlobalPoissonAngleDensity p θ * Real.log (3 / 5 : ℝ) ∂μ0) =
      Real.log (3 / 5 : ℝ) := by
    rw [integral_mul_const, integral_v13GlobalPoissonAngleDensity hp, one_mul]
  have hterm2 : (∫ θ : ℝ, (2 * Real.pi)⁻¹ * (poissonKernel 0 p' (circleMap 0 1 θ) *
        Real.log ‖circleMap 0 1 θ - a‖) ∂μ0) =
      Real.circleAverage (fun ζ => poissonKernel 0 p' ζ * Real.log ‖ζ - a‖) 0 1 := by
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le hπ, integral_const_mul]
    rfl
  rw [hterm1, hterm2]

theorem integral_v13GlobalCirclePoissonMeasure_outside_complex
    {p w : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (hw : (3 / 5 : ℝ) ≤ ‖w‖) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) := by
  rw [integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_complex hp w]
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := w / (r : ℂ)
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have ha : 1 ≤ ‖a‖ := by
    dsimp [a, r, v13GlobalPoissonRadius]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
    exact (one_le_div (by norm_num : (0 : ℝ) < 3 / 5)).mpr hw
  have hmean : Real.circleAverage (fun ζ => poissonKernel 0 p' ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖p' - a‖ := by
    rcases lt_or_eq_of_le ha with hlt | heq
    · exact P0.poisson_mean_log_norm_sub_outside hlt hp'
    · exact P0.poisson_mean_log_norm_sub_boundary heq.symm hp'
  rw [hmean]
  have hpa : p' - a ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hp'
    linarith
  have hprod : (3 / 5 : ℝ) * ‖p' - a‖ = ‖w - p‖ := by
    have hfactor : w - p = -((3 / 5 : ℝ) : ℂ) * (p' - a) := by
      dsimp [p', a, r, v13GlobalPoissonRadius]
      push_cast
      ring
    rw [hfactor, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hsq : ‖w - p‖ ^ 2 = (w.re - p.re) ^ 2 + (w.im - p.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  rw [← Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hpa), hprod,
    ← hsq, Real.log_pow, Nat.cast_ofNat]
  ring

theorem integral_v13GlobalCirclePoissonMeasure_inside_complex
    {p w : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (hw : ‖w‖ ≤ (3 / 5 : ℝ)) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log
        ((9 / 25 - (p.re * w.re + p.im * w.im)) ^ 2 + (p.re * w.im - p.im * w.re) ^ 2) -
        Real.log (3 / 5 : ℝ) := by
  rw [integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_complex hp w]
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := w / (r : ℂ)
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a, r, v13GlobalPoissonRadius]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
    exact (div_le_one (by norm_num : (0 : ℝ) < 3 / 5)).mpr hw
  rw [P0.poisson_mean_log_norm_sub_closed ha hp']
  have h1pos : 0 < ‖1 - conj a * p'‖ := by
    have hlt : ‖conj a * p'‖ < 1 := by
      rw [norm_mul, norm_conj]
      nlinarith [norm_nonneg a, norm_nonneg p']
    have htri := norm_sub_norm_le (1 : ℂ) (conj a * p')
    simp only [norm_one] at htri
    linarith
  have hfactor : ((9 / 25 : ℝ) : ℂ) - conj w * p =
      ((3 / 5 : ℝ) ^ 2 : ℂ) * (1 - conj a * p') := by
    dsimp [a, p', r, v13GlobalPoissonRadius]
    simp only [map_div₀, Complex.conj_ofReal]
    push_cast
    ring
  have hprod : (3 / 5 : ℝ) ^ 2 * ‖1 - conj a * p'‖ =
      ‖((9 / 25 : ℝ) : ℂ) - conj w * p‖ := by
    rw [hfactor, norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hsq : ‖((9 / 25 : ℝ) : ℂ) - conj w * p‖ ^ 2 =
      (9 / 25 - (p.re * w.re + p.im * w.im)) ^ 2 + (p.re * w.im - p.im * w.re) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hlog : Real.log ((3 / 5 : ℝ) ^ 2) + Real.log ‖1 - conj a * p'‖ =
      (1 / 2 : ℝ) * Real.log
        ((9 / 25 - (p.re * w.re + p.im * w.im)) ^ 2 + (p.re * w.im - p.im * w.re) ^ 2) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt h1pos), hprod, ← hsq,
      Real.log_pow, Nat.cast_ofNat]
    ring
  have hlogR2 : Real.log ((3 / 5 : ℝ) ^ 2) = 2 * Real.log (3 / 5 : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  linarith

theorem integral_v13GlobalCirclePoissonMeasure_outside
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) {t : ℝ} (ht : (3 / 5 : ℝ) ≤ |t|) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log ((t - p.re) ^ 2 + p.im ^ 2) := by
  have hw : (3 / 5 : ℝ) ≤ ‖(t : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using ht
  simpa using integral_v13GlobalCirclePoissonMeasure_outside_complex hp hw

theorem integral_v13GlobalCirclePoissonMeasure_inside
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) {t : ℝ} (ht : |t| ≤ (3 / 5 : ℝ)) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log ((9 / 25 - p.re * t) ^ 2 + (p.im * t) ^ 2) -
        Real.log (3 / 5 : ℝ) := by
  have hw : ‖(t : ℂ)‖ ≤ (3 / 5 : ℝ) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using ht
  have h := integral_v13GlobalCirclePoissonMeasure_inside_complex hp hw
  simpa [mul_comm] using h

theorem integrable_v13PoissonMeasure_log_norm_sub_complex
    (rows : List PR) (w : ℂ)
    (hrows : ∀ c ∈ rows, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    Integrable (fun z : ℂ => Real.log ‖w - z‖) (v13PoissonMeasure rows) := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hrows d (by simp [hd])
      have hatom : Integrable (fun z : ℂ => Real.log ‖w - z‖) (v13PoissonAtom c) :=
        (integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex (hrows c hc) w).smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [hsplit]
      exact hatom.add_measure (ih hrest)

theorem integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex
    (rows : List PR) (w : ℂ)
    (hrows : ∀ c ∈ rows, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13PoissonMeasure rows) =
      (rows.map fun c => (c.mult : ℝ) * IK.val c.w *
        ∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, 0 ≤ d.w.1 ∧ 0 < d.w.2 ∧
          ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hrows d (by simp [hd])
      rcases hrows c hc with ⟨hw1, hw2, hnorm⟩
      have hw_nonneg : 0 ≤ (c.mult : ℝ) * IK.val c.w := by
        apply mul_nonneg (Nat.cast_nonneg _)
        unfold IK.val
        exact div_nonneg (by exact_mod_cast hw1) (by exact_mod_cast hw2.le)
      have hatom : Integrable (fun z : ℂ => Real.log ‖w - z‖) (v13PoissonAtom c) :=
        (integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex hnorm w).smul_measure
          ENNReal.ofReal_ne_top
      have htail := integrable_v13PoissonMeasure_log_norm_sub_complex cs w
        (fun d hd => (hrest d hd).2.2)
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [hsplit, integral_add_measure hatom htail, v13PoissonAtom,
        integral_smul_measure, ENNReal.toReal_ofReal hw_nonneg, smul_eq_mul,
        ih hrest]
      simp

theorem sum_map_poissonFull_eq_preRowsI
    (pts : List Li2Lean.V.Q2Certificate.PoissonPoint) (g : ℝ → ℝ → ℝ) :
    let F : PR → ℝ := fun c => (c.mult : ℝ) * IK.val c.w *
      g (IK.val c.cx) ((IK.val c.cy) ^ 2)
    (((Li2Lean.V.Q2Certificate.poissonFull pts).map (prow 1)).map F).sum =
      ((preRowsI pts).map F).sum := by
  intro F
  have hconj (p : Li2Lean.V.Q2Certificate.PoissonPoint) :
      F (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson p)) = F (prow 1 p) := by
    dsimp [F, prow, Li2Lean.V.Q2Certificate.conjugatePoisson, IK.val]
    congr 2
    push_cast
    ring
  have htwo (p : Li2Lean.V.Q2Certificate.PoissonPoint) :
      F (prow 2 p) = F (prow 1 p) + F (prow 1 p) := by
    dsimp [F, prow]
    push_cast
    ring
  have haux : ∀ l : List Li2Lean.V.Q2Certificate.PoissonPoint,
      ((l.map (prow 1)).map F).sum +
        (((l.dropLast.map Li2Lean.V.Q2Certificate.conjugatePoisson).map (prow 1)).map F).sum =
        ((preRowsI l).map F).sum := by
    intro l
    induction l with
    | nil => simp [preRowsI]
    | cons p tl ih =>
        cases tl with
        | nil => simp [preRowsI]
        | cons q rest =>
            have hpre : preRowsI (p :: q :: rest) = prow 2 p :: preRowsI (q :: rest) := rfl
            rw [List.dropLast_cons_cons, hpre]
            simp only [List.map_cons, List.sum_cons] at ih ⊢
            rw [hconj p, htwo p]
            linarith [ih]
  unfold Li2Lean.V.Q2Certificate.poissonFull
  rw [List.map_append, List.map_append, List.sum_append,
    List.map_reverse, List.map_reverse, List.sum_reverse]
  exact haux pts

theorem integral_v13PoissonMeasure_outside_eq_pre_sum
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    {t : ℝ} (ht : (3 / 5 : ℝ) ≤ |t|) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure R.data.full) =
      (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        ((1 / 2 : ℝ) * Real.log ((t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2))).sum := by
  have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
    intro c hc
    rcases hR.full_rows_data c hc with ⟨_, _, hw2, hw1, _, _, _, hnorm⟩
    exact ⟨hw1, hw2, hnorm⟩
  rw [integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex R.data.full (t : ℂ) hrows]
  have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
        ∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
      R.data.full.map (fun c => (c.mult : ℝ) * IK.val c.w *
        ((1 / 2 : ℝ) * Real.log ((t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2))) := by
    refine List.map_congr_left (fun c hc => ?_)
    have hnorm := (hrows c hc).2.2
    rw [integral_v13GlobalCirclePoissonMeasure_outside hnorm ht]
    rfl
  rw [hmap]
  rcases v13DecodedRows_poisson_split R with ⟨pts, hpre, hfull, _, _⟩
  rw [hfull, hpre]
  exact sum_map_poissonFull_eq_preRowsI pts
    (fun x y2 => (1 / 2 : ℝ) * Real.log ((t - x) ^ 2 + y2))

theorem integral_v13PoissonMeasure_inside_eq_pre_sum
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    {t : ℝ} (ht : |t| ≤ (3 / 5 : ℝ)) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure R.data.full) =
      (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2) -
          Real.log (3 / 5 : ℝ))).sum := by
  have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := by
    intro c hc
    rcases hR.full_rows_data c hc with ⟨_, _, hw2, hw1, _, _, _, hnorm⟩
    exact ⟨hw1, hw2, hnorm⟩
  rw [integral_v13PoissonMeasure_log_norm_sub_eq_sum_complex R.data.full (t : ℂ) hrows]
  have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
        ∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
      R.data.full.map (fun c => (c.mult : ℝ) * IK.val c.w *
        ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2) -
          Real.log (3 / 5 : ℝ))) := by
    refine List.map_congr_left (fun c hc => ?_)
    have hnorm := (hrows c hc).2.2
    rw [integral_v13GlobalCirclePoissonMeasure_inside hnorm ht]
    rfl
  rw [hmap]
  rcases v13DecodedRows_poisson_split R with ⟨pts, hpre, hfull, _, _⟩
  rw [hfull, hpre]
  have heq := sum_map_poissonFull_eq_preRowsI pts
    (fun x y2 => (1 / 2 : ℝ) * Real.log ((9 / 25 - x * t) ^ 2 + y2 * t ^ 2) -
      Real.log (3 / 5 : ℝ))
  have hmul_sq (c : PR) : (IK.val c.cy) ^ 2 * t ^ 2 = (IK.val c.cy * t) ^ 2 := by ring
  simp only [hmul_sq] at heq
  exact heq

end

end Li2Lean.B3
