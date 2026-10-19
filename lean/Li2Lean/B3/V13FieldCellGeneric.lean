/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.V13ChainLogEndpoint
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.P0.TubeExteriorBoundary
import Li2Lean.V.EnergyCertI.ISoundEval
namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Part A: generic cell soundness (port of `Q5CellSoundnessProof` sections 2-6).

Mechanical port: `q5D ↦ Dr.data`, `5 ↦ q`, private q5 row facts ↦ fields of
`hDr : V13FieldRowFacts Dr`, q5 Poisson pre/full identities ↦ the generic
`integral_v13PoissonMeasure_{outside,inside}_eq_pre_sum` of `V13RowFacts`.
All copied declarations carry the suffix `_g` to avoid clashes with the
identically named public lemmas of `V13RowFacts`. -/

namespace H6CellGeneric

/-! ## Section 2: General summation by parts and arithmetic helpers -/

private theorem val_qabs_local_g {s : QF} (hs : 0 < s.2) :
    IK.val (qabs s) = |IK.val s| := by
  change ((s.1.natAbs : ℝ) / (s.2 : ℝ)) = |(s.1 : ℝ) / (s.2 : ℝ)|
  rw [natAbs_cast, abs_div]
  have hsR : (0 : ℝ) < (s.2 : ℝ) := by exact_mod_cast hs
  rw [abs_of_pos hsR]

private theorem val_qsq_local_g (s : QF) : IK.val (qsq s) = IK.val s ^ 2 := by
  change IK.val (qmul s s) = IK.val s ^ 2
  rw [val_qmul]
  ring

private theorem val_qhalf_local_g (s : QF) : IK.val (qhalf s) = IK.val s / 2 := by
  unfold qhalf IK.val
  push_cast
  ring

private theorem qmul_den_pos_g {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (qmul a b).2 :=
  Nat.mul_pos ha hb

private theorem qsq_den_pos_g {a : QF} (ha : 0 < a.2) : 0 < (qsq a).2 :=
  Nat.mul_pos ha ha

private theorem qhalf_den_pos_g {a : QF} (ha : 0 < a.2) : 0 < (qhalf a).2 :=
  Nat.mul_pos (by decide) ha

private theorem qabs_den_pos_g {a : QF} (ha : 0 < a.2) : 0 < (qabs a).2 := ha

private theorem qneg_den_pos_g {a : QF} (ha : 0 < a.2) : 0 < (qneg a).2 := ha

private theorem qdiv_den_pos_g {a b : QF} (ha : 0 < a.2) (hb : b.1 ≠ 0) :
    0 < (qdiv a b).2 :=
  Nat.mul_pos ha (Int.natAbs_pos.mpr hb)

private theorem fst_pos_of_val_pos_g {q : QF} (hq5 : 0 < q.2) (hval : 0 < IK.val q) :
    0 < q.1 := by
  unfold IK.val at hval
  have hden : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hq5
  have hnum : (0 : ℝ) < (q.1 : ℝ) := (div_pos_iff_of_pos_right hden).mp hval
  exact_mod_cast hnum

private theorem clampQ_den_pos_g {t0 t1 x : QF}
    (ht0 : 0 < t0.2) (ht1 : 0 < t1.2) (hx : 0 < x.2) :
    0 < (clampQ t0 t1 x).2 := by
  unfold clampQ
  split_ifs <;> assumption

private theorem clampQ_bounds_and_sq_le_g {t0 t1 x : QF}
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

private theorem list_sum_mul_sub_const_g {α : Type*} (xs : List α)
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

theorem v13ChainCellsAux_diff_sum_g
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

theorem v13ChainCells_diff_sum_g
    (f : ℝ → ℝ) (rows : List CP)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    ((v13ChainCells rows).map fun c => c.density *
      (f c.right - f c.left)).sum =
      - (rows.map fun p => IK.val p.J * f (IK.val p.e)).sum := by
  change ((v13ChainCellsAux 0 rows).map fun c => c.density *
      (f c.right - f c.left)).sum = _
  rw [v13ChainCellsAux_diff_sum_g]
  have hconst : (rows.map fun p => IK.val p.J * f (v13ChainRowsLast rows)).sum = 0 := by
    calc
      _ = (rows.map fun p => IK.val p.J).sum * f (v13ChainRowsLast rows) := by
        simp [List.sum_map_mul_right]
      _ = 0 := by rw [hsum]; simp
  simp only [zero_mul, zero_add]
  rw [list_sum_mul_sub_const_g rows (f (v13ChainRowsLast rows))
    (fun p => f (IK.val p.e)) (fun p => IK.val p.J), hconst, zero_sub]

/-! ## Section 3: Logarithmic cell envelope `kMax_g` and `psiReal_g` (`ubarI`) -/

noncomputable def kMax_g (a0 b0 u : ℝ) : ℝ :=
  if u ≤ (a0 + b0) / 2 then Real.log |b0 - u| else Real.log |u - a0|

noncomputable def psiReal_g (a0 b0 u : ℝ) : ℝ :=
  if u ≤ (a0 + b0) / 2 then -LogSegment.primitive (b0 - u)
  else LogSegment.primitive (u - a0) - 2 * LogSegment.primitive ((b0 - a0) / 2)

private theorem log_abs_sub_le_kMax_g {a0 b0 t u : ℝ}
    (hta : a0 ≤ t) (htb : t ≤ b0) (hut : t ≠ u) :
    Real.log |t - u| ≤ kMax_g a0 b0 u := by
  have hpos : 0 < |t - u| := abs_pos.mpr (sub_ne_zero.mpr hut)
  unfold kMax_g
  split_ifs with hu
  · have hbu : 0 ≤ b0 - u := by linarith
    have hle : |t - u| ≤ |b0 - u| := by
      rw [abs_of_nonneg hbu, abs_le]
      constructor <;> linarith
    exact Real.log_le_log hpos hle
  · push_neg at hu
    have hua : 0 ≤ u - a0 := by linarith
    have hle : |t - u| ≤ |u - a0| := by
      rw [abs_of_nonneg hua, abs_le]
      constructor <;> linarith
    exact Real.log_le_log hpos hle

private theorem primitive_neg_g (x : ℝ) :
    LogSegment.primitive (-x) = -LogSegment.primitive x := by
  simp only [LogSegment.primitive, abs_neg]
  ring

private theorem integrableOn_Ioc_kMax_left_g {a0 b0 α β : ℝ}
    (hαβ : α ≤ β) (hβm : β ≤ (a0 + b0) / 2) :
    IntegrableOn (kMax_g a0 b0) (Ioc α β) volume := by
  have hbase : IntegrableOn (fun u => Real.log |b0 - u|) (Ioc α β) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mp
      (LogSegment.intervalIntegrable_log_abs_sub b0 α β)
  refine hbase.congr_fun (fun u hu => ?_) measurableSet_Ioc
  have hum : u ≤ (a0 + b0) / 2 := le_trans hu.2 hβm
  simp [kMax_g, hum]

private theorem integral_Ioc_kMax_left_g {a0 b0 α β : ℝ}
    (hαβ : α ≤ β) (hβm : β ≤ (a0 + b0) / 2) :
    (∫ u in Ioc α β, kMax_g a0 b0 u) = psiReal_g a0 b0 β - psiReal_g a0 b0 α := by
  have hcongr : (∫ u in Ioc α β, kMax_g a0 b0 u) =
      ∫ u in Ioc α β, Real.log |b0 - u| := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hum : u ≤ (a0 + b0) / 2 := le_trans hu.2 hβm
    simp [kMax_g, hum]
  rw [hcongr, ← intervalIntegral.integral_of_le hαβ,
    LogSegment.integral_log_abs_sub]
  have hαm : α ≤ (a0 + b0) / 2 := le_trans hαβ hβm
  simp only [psiReal_g, if_pos hβm, if_pos hαm]
  ring

private theorem integrableOn_Ioc_kMax_right_g {a0 b0 α β : ℝ}
    (hαβ : α ≤ β) (hmα : (a0 + b0) / 2 ≤ α) :
    IntegrableOn (kMax_g a0 b0) (Ioc α β) volume := by
  have hbase : IntegrableOn (fun u => Real.log |a0 - u|) (Ioc α β) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mp
      (LogSegment.intervalIntegrable_log_abs_sub a0 α β)
  refine hbase.congr_fun (fun u hu => ?_) measurableSet_Ioc
  have hum : ¬ (u ≤ (a0 + b0) / 2) := not_le.mpr (lt_of_le_of_lt hmα hu.1)
  simp [kMax_g, hum, abs_sub_comm]

private theorem integral_Ioc_kMax_right_g {a0 b0 α β : ℝ}
    (hab : a0 ≤ b0) (hαβ : α ≤ β) (hmα : (a0 + b0) / 2 ≤ α) :
    (∫ u in Ioc α β, kMax_g a0 b0 u) = psiReal_g a0 b0 β - psiReal_g a0 b0 α := by
  have hcongr : (∫ u in Ioc α β, kMax_g a0 b0 u) =
      ∫ u in Ioc α β, Real.log |a0 - u| := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hum : ¬ (u ≤ (a0 + b0) / 2) := not_le.mpr (lt_of_le_of_lt hmα hu.1)
    simp [kMax_g, hum, abs_sub_comm]
  rw [hcongr, ← intervalIntegral.integral_of_le hαβ,
    LogSegment.integral_log_abs_sub]
  have h1 : LogSegment.primitive (a0 - α) = -LogSegment.primitive (α - a0) := by
    have heq : a0 - α = -(α - a0) := by ring
    rw [heq, primitive_neg_g]
  have h2 : LogSegment.primitive (a0 - β) = -LogSegment.primitive (β - a0) := by
    have heq : a0 - β = -(β - a0) := by ring
    rw [heq, primitive_neg_g]
  rw [h1, h2]
  have hα : psiReal_g a0 b0 α =
      LogSegment.primitive (α - a0) - 2 * LogSegment.primitive ((b0 - a0) / 2) := by
    unfold psiReal_g
    split_ifs with hle
    · have heq : α = (a0 + b0) / 2 := le_antisymm hle hmα
      have hb0 : b0 - α = (b0 - a0) / 2 := by linarith
      have ha0 : α - a0 = (b0 - a0) / 2 := by linarith
      rw [hb0, ha0]
      ring
    · rfl
  have hβ : psiReal_g a0 b0 β =
      LogSegment.primitive (β - a0) - 2 * LogSegment.primitive ((b0 - a0) / 2) := by
    unfold psiReal_g
    split_ifs with hle
    · have heq : β = (a0 + b0) / 2 := le_antisymm hle (le_trans hmα hαβ)
      have hb0 : b0 - β = (b0 - a0) / 2 := by linarith
      have ha0 : β - a0 = (b0 - a0) / 2 := by linarith
      rw [hb0, ha0]
      ring
    · rfl
  rw [hα, hβ]
  ring

private theorem integrableOn_Ioc_kMax_g {a0 b0 α β : ℝ}
    (hαβ : α ≤ β) :
    IntegrableOn (kMax_g a0 b0) (Ioc α β) volume := by
  let m0 := (a0 + b0) / 2
  by_cases hβm : β ≤ m0
  · exact integrableOn_Ioc_kMax_left_g hαβ hβm
  · push_neg at hβm
    by_cases hmα : m0 ≤ α
    · exact integrableOn_Ioc_kMax_right_g hαβ hmα
    · push_neg at hmα
      have hsplit : Ioc α β = Ioc α m0 ∪ Ioc m0 β :=
        (Ioc_union_Ioc_eq_Ioc (le_of_lt hmα) (le_of_lt hβm)).symm
      rw [hsplit]
      exact (integrableOn_Ioc_kMax_left_g (le_of_lt hmα) le_rfl).union
        (integrableOn_Ioc_kMax_right_g (le_of_lt hβm) le_rfl)

private theorem integral_Ioc_kMax_g {a0 b0 α β : ℝ}
    (hab : a0 ≤ b0) (hαβ : α ≤ β) :
    (∫ u in Ioc α β, kMax_g a0 b0 u) = psiReal_g a0 b0 β - psiReal_g a0 b0 α := by
  let m0 := (a0 + b0) / 2
  by_cases hβm : β ≤ m0
  · exact integral_Ioc_kMax_left_g hαβ hβm
  · push_neg at hβm
    by_cases hmα : m0 ≤ α
    · exact integral_Ioc_kMax_right_g hab hαβ hmα
    · push_neg at hmα
      have hsplit : Ioc α β = Ioc α m0 ∪ Ioc m0 β :=
        (Ioc_union_Ioc_eq_Ioc (le_of_lt hmα) (le_of_lt hβm)).symm
      rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (integrableOn_Ioc_kMax_left_g (le_of_lt hmα) le_rfl)
        (integrableOn_Ioc_kMax_right_g (le_of_lt hβm) le_rfl),
        integral_Ioc_kMax_left_g (le_of_lt hmα) le_rfl,
        integral_Ioc_kMax_right_g hab (le_of_lt hβm) le_rfl]
      ring

private theorem integrable_v13ChainMeasure_kMax_g
    (cells : List V13ChainCell) (a0 b0 : ℝ)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right) :
    Integrable (kMax_g a0 b0) (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hcell : Integrable (kMax_g a0 b0)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_kMax_g (hbounds c hc)).integrable.smul_measure ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure (ih hrest)

private theorem integral_v13ChainMeasure_kMax_g
    (cells : List V13ChainCell) (a0 b0 : ℝ) (hab : a0 ≤ b0)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right)
    (hdensity : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ u : ℝ, kMax_g a0 b0 u ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        (psiReal_g a0 b0 c.right - psiReal_g a0 b0 c.left)).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrestB : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hrestD : ∀ d ∈ cs, 0 ≤ d.density := fun d hd => hdensity d (by simp [hd])
      have hcell' : Integrable (kMax_g a0 b0)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_kMax_g (hbounds c hc)).integrable.smul_measure ENNReal.ofReal_ne_top
      have htailInt := integrable_v13ChainMeasure_kMax_g cs a0 b0 hrestB
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell' htailInt,
        integral_smul_measure, ENNReal.toReal_ofReal (hdensity c hc), smul_eq_mul,
        integral_Ioc_kMax_g hab (hbounds c hc), ih hrestB hrestD]
      simp

private theorem integrable_v13ChainMeasure_log_abs_sub_g
    (cells : List V13ChainCell) (t : ℝ)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right) :
    Integrable (fun u : ℝ => Real.log |t - u|) (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hcell0 : IntegrableOn (fun u : ℝ => Real.log |t - u|)
          (Ioc c.left c.right) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbounds c hc)).mp
          (LogSegment.intervalIntegrable_log_abs_sub t c.left c.right)
      have hcell : Integrable (fun u : ℝ => Real.log |t - u|)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        hcell0.integrable.smul_measure ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure (ih hrest)

private theorem integrable_v13DecodedChainMeasure_log_norm_sub_g
    (rows : List CP) (t : ℝ)
    (hbounds : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right) :
    Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖) (v13DecodedChainMeasure rows) := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [hEmb.integrable_map_iff]
  have hcongr : ((fun z : ℂ => Real.log ‖(t : ℂ) - z‖) ∘ Complex.ofReal) =
      fun u : ℝ => Real.log |t - u| := by
    ext u
    simp [Function.comp, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hcongr]
  exact integrable_v13ChainMeasure_log_abs_sub_g (v13ChainCells rows) t hbounds

private theorem integral_v13DecodedChainMeasure_le_kMax_g
    (rows : List CP) {a0 b0 t : ℝ}
    (hta : a0 ≤ t) (htb : t ≤ b0)
    (hbounds : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right)
    (hdensity : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure rows) ≤
      - (rows.map fun p => IK.val p.J * psiReal_g a0 b0 (IK.val p.e)).sum := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hInt1 := integrable_v13ChainMeasure_log_abs_sub_g (v13ChainCells rows) t hbounds
  have hInt2 := integrable_v13ChainMeasure_kMax_g (v13ChainCells rows) a0 b0 hbounds
  have hmap : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure rows) =
      ∫ u : ℝ, Real.log |t - u| ∂v13ChainMeasure (v13ChainCells rows) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [← Complex.ofReal_sub, Complex.norm_real]
  rw [hmap]
  have hae : ∀ᵐ u ∂v13ChainMeasure (v13ChainCells rows), t ≠ u := by
    rw [ae_iff]
    have hset : {u : ℝ | ¬ t ≠ u} = {t} := by ext u; simp [eq_comm]
    rw [hset]
    exact v13ChainMeasure_singleton (v13ChainCells rows) t
  have hle : (∫ u : ℝ, Real.log |t - u| ∂v13ChainMeasure (v13ChainCells rows)) ≤
      ∫ u : ℝ, kMax_g a0 b0 u ∂v13ChainMeasure (v13ChainCells rows) := by
    apply integral_mono_ae hInt1 hInt2
    filter_upwards [hae] with u hut
    exact log_abs_sub_le_kMax_g hta htb hut
  have hab : a0 ≤ b0 := le_trans hta htb
  rw [integral_v13ChainMeasure_kMax_g (v13ChainCells rows) a0 b0 hab hbounds hdensity,
    v13ChainCells_diff_sum_g (psiReal_g a0 b0) rows hsum] at hle
  exact hle

private theorem psiI_mem_g (md : Mode) {a b u : QF}
    (ha : 0 < a.2) (hb : 0 < b.2) (hu : 0 < u.2) :
    IV.mem (psiI md a b u (hsI md (qhalf (qsub b a))))
      (psiReal_g (IK.val a) (IK.val b) (IK.val u)) := by
  have hmid_den : 0 < (qhalf (qadd a b)).2 := qhalf_den_pos_g (qadd_den_pos ha hb)
  have hmid_val : IK.val (qhalf (qadd a b)) = (IK.val a + IK.val b) / 2 := by
    rw [val_qhalf_local_g, val_qadd ha hb]
  unfold psiI psiReal_g
  by_cases hle : qle u (qhalf (qadd a b)) = true
  · have hleR : IK.val u ≤ (IK.val a + IK.val b) / 2 := by
      rw [← hmid_val]
      exact (qle_spec hu hmid_den).mp hle
    rw [if_pos hle, if_pos hleR]
    have hsub_den : 0 < (qsub b u).2 := qsub_den_pos hb hu
    have hhs := V.EnergyCertI.hsI_mem md hsub_den
    have hneg := IK.neg_mem hhs
    refine IK.mem_of_eq hneg ?_
    rw [val_qsub hb hu, LogSegment.primitive]
    ring
  · have hgtR : ¬ (IK.val u ≤ (IK.val a + IK.val b) / 2) := by
      rw [← hmid_val]
      exact mt (qle_spec hu hmid_den).mpr hle
    rw [if_neg hle, if_neg hgtR]
    have hsub1_den : 0 < (qsub u a).2 := qsub_den_pos hu ha
    have hsub2_den : 0 < (qhalf (qsub b a)).2 := qhalf_den_pos_g (qsub_den_pos hb ha)
    have hhs1 := V.EnergyCertI.hsI_mem md hsub1_den
    have hhs2 := V.EnergyCertI.hsI_mem md hsub2_den
    have hsmul := IK.smulInt_mem 2 hhs2
    have hsub := IK.sub_mem hhs1 hsmul
    refine IK.mem_of_eq hsub ?_
    rw [val_qsub hu ha, val_qhalf_local_g, val_qsub hb ha, LogSegment.primitive,
      LogSegment.primitive]
    push_cast
    ring

private theorem ubarI_mem_g (md : Mode) (rows : List CP) {a b : QF}
    (ha : 0 < a.2) (hb : 0 < b.2)
    (hrows : ∀ p ∈ rows, 0 < p.e.2 ∧ 0 < p.J.2) :
    IV.mem (ubarI md rows a b)
      (- (rows.map fun p => IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum) := by
  unfold ubarI
  apply IK.neg_mem
  apply IK.sumI_map_mem
  intro p hp
  rcases hrows p hp with ⟨he, hJ⟩
  exact IK.smulQ_mem hJ (psiI_mem_g md ha hb he)

/-! ## Section 4: Cross-kernel lower envelope `lamReal_g` (`dlowI`) -/

noncomputable def lamReal_g (q : ℕ) (a0 u : ℝ) : ℝ :=
  LogSegment.primitive ((q : ℝ) + a0 * u) / a0

private theorem integrableOn_Ioc_log_linear_g {q : ℕ} {a0 α β : ℝ}
    (hq : 0 < (q : ℝ)) (ha0 : 0 < a0) (h0α : 0 ≤ α) (_hαβ : α ≤ β) :
    IntegrableOn (fun u : ℝ => Real.log ((q : ℝ) + a0 * u)) (Ioc α β) volume := by
  have hcontArg : ContinuousOn (fun u : ℝ => (q : ℝ) + a0 * u) (Icc α β) :=
    continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  have hmapNe : Set.MapsTo (fun u : ℝ => (q : ℝ) + a0 * u) (Icc α β) ({0} : Set ℝ)ᶜ := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hu0 : 0 ≤ u := le_trans h0α hu.1
    nlinarith
  have hcont : ContinuousOn (fun u : ℝ => Real.log ((q : ℝ) + a0 * u)) (Icc α β) :=
    Real.continuousOn_log.comp hcontArg hmapNe
  exact hcont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self

private theorem integral_Ioc_log_linear_g {q : ℕ} {a0 α β : ℝ}
    (ha0 : 0 < a0) (hαβ : α ≤ β) :
    (∫ u in Ioc α β, Real.log ((q : ℝ) + a0 * u)) =
      lamReal_g q a0 β - lamReal_g q a0 α := by
  rw [← intervalIntegral.integral_of_le hαβ]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Real.log ((q : ℝ) + x)) (ne_of_gt ha0) (a := α) (b := β)
  simp only [smul_eq_mul] at hcomp
  rw [hcomp, LogSegment.integral_log_add]
  unfold lamReal_g
  have ha0' : a0 ≠ 0 := ne_of_gt ha0
  field_simp [ha0']

private theorem integrable_v13ChainMeasure_log_linear_g
    (cells : List V13ChainCell) {q : ℕ} {a0 : ℝ}
    (hq : 0 < (q : ℝ)) (ha0 : 0 < a0)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right) :
    Integrable (fun u : ℝ => Real.log ((q : ℝ) + a0 * u)) (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, 0 ≤ d.left ∧ d.left ≤ d.right :=
        fun d hd => hbounds d (by simp [hd])
      rcases hbounds c hc with ⟨h0l, hlr⟩
      have hcell : Integrable (fun u : ℝ => Real.log ((q : ℝ) + a0 * u))
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_log_linear_g hq ha0 h0l hlr).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure (ih hrest)

private theorem integral_v13ChainMeasure_log_linear_g
    (cells : List V13ChainCell) {q : ℕ} {a0 : ℝ}
    (hq : 0 < (q : ℝ)) (ha0 : 0 < a0)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right)
    (hdensity : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ u : ℝ, Real.log ((q : ℝ) + a0 * u) ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        (lamReal_g q a0 c.right - lamReal_g q a0 c.left)).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrestB : ∀ d ∈ cs, 0 ≤ d.left ∧ d.left ≤ d.right :=
        fun d hd => hbounds d (by simp [hd])
      have hrestD : ∀ d ∈ cs, 0 ≤ d.density :=
        fun d hd => hdensity d (by simp [hd])
      rcases hbounds c hc with ⟨h0l, hlr⟩
      have hcell' : Integrable (fun u : ℝ => Real.log ((q : ℝ) + a0 * u))
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_log_linear_g hq ha0 h0l hlr).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have htailInt := integrable_v13ChainMeasure_log_linear_g cs hq ha0 hrestB
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell' htailInt,
        integral_smul_measure, ENNReal.toReal_ofReal (hdensity c hc), smul_eq_mul,
        integral_Ioc_log_linear_g ha0 hlr, ih hrestB hrestD]
      simp

private theorem ae_nonneg_v13ChainMeasure_g
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

private theorem neg_integral_vCrossKernel_right_le_g
    (rows : List CP) {q : ℕ} {a0 t : ℝ}
    (hq : 0 < (q : ℝ)) (ha0 : 0 < a0) (hta : a0 ≤ t)
    (hbounds : ∀ c ∈ v13ChainCells rows, 0 ≤ c.left ∧ c.left ≤ c.right)
    (hdensity : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    - (∫ z : ℂ, V.vCrossKernel q (t : ℂ) z ∂v13DecodedChainMeasure rows) ≤
      (rows.map fun p => IK.val p.J * lamReal_g q a0 (IK.val p.e)).sum := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have htpos : 0 < t := lt_of_lt_of_le ha0 hta
  have hIntA := integrable_v13ChainMeasure_log_linear_g (v13ChainCells rows) hq ha0 hbounds
  have hIntT := integrable_v13ChainMeasure_log_linear_g (v13ChainCells rows) hq htpos hbounds
  have hmap : (∫ z : ℂ, V.vCrossKernel q (t : ℂ) z ∂v13DecodedChainMeasure rows) =
      ∫ u : ℝ, V.vCrossKernel q (t : ℂ) (u : ℂ) ∂v13ChainMeasure (v13ChainCells rows) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap]
  have hae := ae_nonneg_v13ChainMeasure_g (v13ChainCells rows) hbounds
  have hcongr : (∫ u : ℝ, V.vCrossKernel q (t : ℂ) (u : ℂ)
        ∂v13ChainMeasure (v13ChainCells rows)) =
      ∫ u : ℝ, Real.log ((q : ℝ) + t * u) ∂v13ChainMeasure (v13ChainCells rows) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    unfold V.vCrossKernel
    have hpos : 0 ≤ (q : ℝ) + t * u := by nlinarith
    have hcast : ((q : ℂ) + (t : ℂ) * (u : ℂ)) = (((q : ℝ) + t * u : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  rw [hcongr]
  have hmono : (∫ u : ℝ, Real.log ((q : ℝ) + a0 * u)
        ∂v13ChainMeasure (v13ChainCells rows)) ≤
      ∫ u : ℝ, Real.log ((q : ℝ) + t * u) ∂v13ChainMeasure (v13ChainCells rows) := by
    apply integral_mono_ae hIntA hIntT
    filter_upwards [hae] with u hu
    have hposA : 0 < (q : ℝ) + a0 * u := by nlinarith
    have hle : (q : ℝ) + a0 * u ≤ (q : ℝ) + t * u := by nlinarith
    exact Real.log_le_log hposA hle
  rw [integral_v13ChainMeasure_log_linear_g (v13ChainCells rows) hq ha0 hbounds hdensity,
    v13ChainCells_diff_sum_g (lamReal_g q a0) rows hsum] at hmono
  linarith

private theorem neg_integral_vCrossKernel_left_le_g
    (rows : List CP) {q : ℕ} {a0 t : ℝ}
    (hq : 0 < (q : ℝ)) (ha0 : 0 < a0) (hta : a0 ≤ t)
    (hbounds : ∀ c ∈ v13ChainCells rows, 0 ≤ c.left ∧ c.left ≤ c.right)
    (hdensity : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0) :
    - (∫ z : ℂ, V.vCrossKernel q z (t : ℂ) ∂v13DecodedChainMeasure rows) ≤
      (rows.map fun p => IK.val p.J * lamReal_g q a0 (IK.val p.e)).sum := by
  have hcomm : (∫ z : ℂ, V.vCrossKernel q z (t : ℂ) ∂v13DecodedChainMeasure rows) =
      ∫ z : ℂ, V.vCrossKernel q (t : ℂ) z ∂v13DecodedChainMeasure rows := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    unfold V.vCrossKernel
    dsimp only
    rw [mul_comm z (t : ℂ)]
  rw [hcomm]
  exact neg_integral_vCrossKernel_right_le_g rows hq ha0 hta hbounds hdensity hsum

private theorem lamI_mem_g (md : Mode) (q : ℕ) {a u : QF}
    (hq : 0 < q) (ha : 0 < a.2) (hu : 0 < u.2)
    (haval : 0 < IK.val a) (hu1 : 0 ≤ u.1) :
    IV.mem (lamI md q a u) (lamReal_g q (IK.val a) (IK.val u)) := by
  unfold lamI lamReal_g
  let s := qadd (Int.ofNat q, 1) (qmul a u)
  have hs_den : 0 < s.2 := qadd_den_pos zero_lt_one (qmul_den_pos_g ha hu)
  have huval : 0 ≤ IK.val u := by
    unfold IK.val
    exact div_nonneg (by exact_mod_cast hu1) (by exact_mod_cast hu.le)
  have hs_val : IK.val s = (q : ℝ) + IK.val a * IK.val u := by
    dsimp [s]
    rw [val_qadd zero_lt_one (qmul_den_pos_g ha hu), val_qmul]
    have hqval : IK.val ((q : ℤ), 1) = (q : ℝ) := by
      unfold IK.val
      simp
    rw [hqval]
  have hs_pos : 0 < IK.val s := by
    rw [hs_val]
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hs1 : 0 < s.1 := fst_pos_of_val_pos_g hs_den hs_pos
  have ha1 : a.1 ≠ 0 := (fst_pos_of_val_pos_g ha haval).ne'
  have hdiv_den : 0 < (qdiv s a).2 := qdiv_den_pos_g hs_den ha1
  have hlog := IK.logQ_mem md.ntl hs1 hs_den
  have hsub := IK.sub_mem hlog (IK.ofQ_mem (a := (1, 1)) (by decide))
  have hsmul := IK.smulQ_mem hdiv_den hsub
  refine IK.mem_of_eq hsmul ?_
  rw [val_qdiv hs_den ha ha1, hs_val]
  have hone : IK.val (1, 1) = 1 := by norm_num [IK.val]
  rw [hone, LogSegment.primitive, abs_of_pos (by rw [← hs_val]; exact hs_pos)]
  ring

private theorem neg_dlowI_mem_g (md : Mode) (q : ℕ) (rows : List CP) {a : QF}
    (hq : 0 < q) (ha : 0 < a.2) (haval : 0 < IK.val a)
    (hrows : ∀ p ∈ rows, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2) :
    IV.mem (IK.neg (dlowI md q rows a))
      ((rows.map fun p => IK.val p.J * lamReal_g q (IK.val a) (IK.val p.e)).sum) := by
  unfold dlowI
  have hsum : IV.mem (sumI (rows.map fun p => smulQ p.J (lamI md q a p.e)))
      ((rows.map fun p => IK.val p.J * lamReal_g q (IK.val a) (IK.val p.e)).sum) := by
    apply IK.sumI_map_mem
    intro p hp
    rcases hrows p hp with ⟨he1, he2, hJ2⟩
    exact IK.smulQ_mem hJ2 (lamI_mem_g md q hq ha he2 haval he1)
  exact IK.mem_of_eq (IK.neg_mem (IK.neg_mem hsum)) (neg_neg _)

/-! ## Section 5: Poisson cloud exact integral and midpoint quadratic enclosure -/

theorem integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_g
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (t : ℝ) :
    Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)
      (v13GlobalCirclePoissonMeasure p) := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := (t : ℂ) / (r : ℂ)
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have hmeas_f : AEStronglyMeasurable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)
      (v13GlobalCirclePoissonMeasure p) :=
    (by fun_prop : Measurable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)).aestronglyMeasurable
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
  have hfactor : (t : ℂ) - circleMap 0 r θ =
      -(r : ℂ) * (circleMap 0 1 θ - a) := by
    dsimp [a, r, v13GlobalPoissonRadius, circleMap]
    push_cast
    ring
  have hnorm : ‖(t : ℂ) - circleMap 0 r θ‖ =
      (3 / 5 : ℝ) * ‖circleMap 0 1 θ - a‖ := by
    rw [hfactor, norm_mul, norm_neg, hr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hne : ‖circleMap 0 1 θ - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ)
  rw [hnorm, Real.log_mul (by norm_num) hne]
  unfold v13GlobalPoissonAngleDensity
  dsimp [p', r]
  ring

theorem integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_g
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (t : ℝ) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      Real.log (3 / 5 : ℝ) +
        Real.circleAverage (fun ζ => poissonKernel 0 (p / (v13GlobalPoissonRadius : ℂ)) ζ *
          Real.log ‖ζ - (t : ℂ) / (v13GlobalPoissonRadius : ℂ)‖) 0 1 := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := (t : ℂ) / (r : ℂ)
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have hmeas_f : AEStronglyMeasurable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)
      (v13GlobalCirclePoissonMeasure p) :=
    (by fun_prop : Measurable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)).aestronglyMeasurable
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
        Real.log ‖(t : ℂ) - circleMap 0 r θ‖ ∂μ0) =
      ∫ θ : ℝ, (v13GlobalPoissonAngleDensity p θ * Real.log (3 / 5 : ℝ) +
        (2 * Real.pi)⁻¹ * (poissonKernel 0 p' (circleMap 0 1 θ) *
          Real.log ‖circleMap 0 1 θ - a‖)) ∂μ0 := by
    refine integral_congr_ae ?_
    filter_upwards [P0.ae_circleMap_ne a μ0] with θ hθ
    simp only [ENNReal.toReal_ofReal (v13GlobalPoissonAngleDensity_nonneg hp θ), smul_eq_mul]
    have hr : r = (3 / 5 : ℝ) := by rfl
    have hfactor : (t : ℂ) - circleMap 0 r θ =
        -(r : ℂ) * (circleMap 0 1 θ - a) := by
      dsimp [a, r, v13GlobalPoissonRadius, circleMap]
      push_cast
      ring
    have hnorm : ‖(t : ℂ) - circleMap 0 r θ‖ =
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

theorem integral_v13GlobalCirclePoissonMeasure_outside_g
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) {t : ℝ} (ht : (3 / 5 : ℝ) ≤ |t|) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log ((t - p.re) ^ 2 + p.im ^ 2) := by
  rw [integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_g hp t]
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := (t : ℂ) / (r : ℂ)
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have ha : 1 ≤ ‖a‖ := by
    dsimp [a, r, v13GlobalPoissonRadius]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
    exact (one_le_div (by norm_num : (0 : ℝ) < 3 / 5)).mpr ht
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
  have hprod : (3 / 5 : ℝ) * ‖p' - a‖ = ‖(t : ℂ) - p‖ := by
    have hfactor : (t : ℂ) - p = -((3 / 5 : ℝ) : ℂ) * (p' - a) := by
      dsimp [p', a, r, v13GlobalPoissonRadius]
      push_cast
      ring
    rw [hfactor, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hsq : ‖(t : ℂ) - p‖ ^ 2 = (t - p.re) ^ 2 + p.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpos : 0 < ‖(t : ℂ) - p‖ := by
    rw [← hprod]
    exact mul_pos (by norm_num) (norm_pos_iff.mpr hpa)
  rw [← Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hpa), hprod,
    ← hsq, Real.log_pow, Nat.cast_ofNat]
  ring

theorem integral_v13GlobalCirclePoissonMeasure_inside_g
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) {t : ℝ} (ht : |t| ≤ (3 / 5 : ℝ)) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure p) =
      (1 / 2 : ℝ) * Real.log ((9 / 25 - p.re * t) ^ 2 + (p.im * t) ^ 2) -
        Real.log (3 / 5 : ℝ) := by
  rw [integral_v13GlobalCirclePoissonMeasure_log_norm_sub_eq_circleAverage_g hp t]
  let r := v13GlobalPoissonRadius
  let p' := p / (r : ℂ)
  let a := (t : ℂ) / (r : ℂ)
  have hp' : ‖p'‖ < 1 := v13GlobalPoissonParameter_norm_lt hp
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a, r, v13GlobalPoissonRadius]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
    exact (div_le_one (by norm_num : (0 : ℝ) < 3 / 5)).mpr ht
  rw [P0.poisson_mean_log_norm_sub_closed ha hp']
  have h1pos : 0 < ‖1 - conj a * p'‖ := by
    have hlt : ‖conj a * p'‖ < 1 := by
      rw [norm_mul, norm_conj]
      nlinarith [norm_nonneg a, norm_nonneg p']
    have htri := norm_sub_norm_le (1 : ℂ) (conj a * p')
    simp only [norm_one] at htri
    linarith
  have hfactor : ((9 / 25 : ℝ) : ℂ) - p * (t : ℂ) =
      ((3 / 5 : ℝ) ^ 2 : ℂ) * (1 - conj a * p') := by
    dsimp [a, p', r, v13GlobalPoissonRadius]
    simp only [map_div₀, Complex.conj_ofReal]
    push_cast
    ring
  have hprod : (3 / 5 : ℝ) ^ 2 * ‖1 - conj a * p'‖ =
      ‖((9 / 25 : ℝ) : ℂ) - p * (t : ℂ)‖ := by
    rw [hfactor, norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  have hsq : ‖((9 / 25 : ℝ) : ℂ) - p * (t : ℂ)‖ ^ 2 =
      (9 / 25 - p.re * t) ^ 2 + (p.im * t) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hlog : Real.log ((3 / 5 : ℝ) ^ 2) + Real.log ‖1 - conj a * p'‖ =
      (1 / 2 : ℝ) * Real.log ((9 / 25 - p.re * t) ^ 2 + (p.im * t) ^ 2) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt h1pos), hprod, ← hsq,
      Real.log_pow, Nat.cast_ofNat]
    ring
  have hlogR2 : Real.log ((3 / 5 : ℝ) ^ 2) = 2 * Real.log (3 / 5 : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  linarith

theorem integrable_v13PoissonMeasure_log_norm_sub_g
    (rows : List PR) (t : ℝ)
    (hrows : ∀ c ∈ rows, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖) (v13PoissonMeasure rows) := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hrows d (by simp [hd])
      have hatom : Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖) (v13PoissonAtom c) :=
        (integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_g (hrows c hc) t).smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [hsplit]
      exact hatom.add_measure (ih hrest)

theorem integral_v13PoissonMeasure_log_norm_sub_eq_sum_g
    (rows : List PR) (t : ℝ)
    (hrows : ∀ c ∈ rows, 0 ≤ c.w.1 ∧ 0 < c.w.2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure rows) =
      (rows.map fun c => (c.mult : ℝ) * IK.val c.w *
        ∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)).sum := by
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
      have hatom : Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖) (v13PoissonAtom c) :=
        (integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_g hnorm t).smul_measure
          ENNReal.ofReal_ne_top
      have htail := integrable_v13PoissonMeasure_log_norm_sub_g cs t
        (fun d hd => (hrest d hd).2.2)
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [hsplit, integral_add_measure hatom htail, v13PoissonAtom,
        integral_smul_measure, ENNReal.toReal_ofReal hw_nonneg, smul_eq_mul,
        ih hrest]
      simp

theorem sum_map_poissonFull_eq_preRowsI_g
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

private theorem half_log_quadratic_upper_g
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

private theorem poiRealI_mem_and_bound_outside_g
    (c : PR) (hc : 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
      ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) ∧
      0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ∧
      (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) {a b : QF} (lr : IV)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : IK.val a < IK.val b)
    (hout : qle R a = true ∨ qle b (qneg R) = true) :
    ∃ Uc : ℝ, IV.mem (poiRealI fieldMode c a b lr) Uc ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b →
        (c.mult : ℝ) * IK.val c.w *
          ((1 / 2 : ℝ) * Real.log ((t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)) ≤ Uc := by
  rcases hc with ⟨hcx2, hcy2, hw2, hw1, _, _, hrad, _⟩
  let m := qhalf (qadd a b)
  let hw := qhalf (qsub b a)
  let wgt := qmul (Int.ofNat c.mult, 1) c.w
  let gm := qadd (qsq (qsub m c.cx)) (qsq c.cy)
  let gmin := qadd (qsq (qsub c.cx (clampQ a b c.cx))) (qsq c.cy)
  let tailQ := qadd (qmul (qabs (qdiv (qsub m c.cx) gm)) hw)
    (qdiv (qsq hw) (qmul (2, 1) gmin))
  have hm_den : 0 < m.2 := qhalf_den_pos_g (qadd_den_pos ha hb)
  have hhw_den : 0 < hw.2 := qhalf_den_pos_g (qsub_den_pos hb ha)
  have hwgt_den : 0 < wgt.2 := qmul_den_pos_g zero_lt_one hw2
  have hgm_den : 0 < gm.2 := qadd_den_pos (qsq_den_pos_g (qsub_den_pos hm_den hcx2)) (qsq_den_pos_g hcy2)
  have hclamp_den : 0 < (clampQ a b c.cx).2 := clampQ_den_pos_g ha hb hcx2
  have hgmin_den : 0 < gmin.2 :=
    qadd_den_pos (qsq_den_pos_g (qsub_den_pos hcx2 hclamp_den)) (qsq_den_pos_g hcy2)
  have hm_val : IK.val m = (IK.val a + IK.val b) / 2 := by
    dsimp [m]; rw [val_qhalf_local_g, val_qadd ha hb]
  have hhw_val : IK.val hw = (IK.val b - IK.val a) / 2 := by
    dsimp [hw]; rw [val_qhalf_local_g, val_qsub hb ha]
  have hwgt_val : IK.val wgt = (c.mult : ℝ) * IK.val c.w := by
    dsimp [wgt]; rw [val_qmul]
    have hmval : IK.val ((c.mult : ℤ), 1) = (c.mult : ℝ) := by
      unfold IK.val; simp
    rw [hmval]
  have hgm_val : IK.val gm = (IK.val m - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
    dsimp [gm]
    rw [val_qadd (qsq_den_pos_g (qsub_den_pos hm_den hcx2)) (qsq_den_pos_g hcy2),
      val_qsq_local_g, val_qsq_local_g, val_qsub hm_den hcx2]
  have hgmin_val : IK.val gmin =
      (IK.val (clampQ a b c.cx) - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
    dsimp [gmin]
    rw [val_qadd (qsq_den_pos_g (qsub_den_pos hcx2 hclamp_den)) (qsq_den_pos_g hcy2),
      val_qsq_local_g, val_qsq_local_g, val_qsub hcx2 hclamp_den]
    ring
  have hs_out : ∀ s : ℝ, IK.val a ≤ s → s ≤ IK.val b → (3 / 5 : ℝ) ^ 2 ≤ s ^ 2 := by
    intro s hsa hsb
    have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    have hnegR : IK.val (qneg R) = -(3 / 5 : ℝ) := by norm_num [R, qneg, IK.val]
    rcases hout with h1 | h2
    · have haR : (3 / 5 : ℝ) ≤ IK.val a := by
        rw [← hR]; exact (qle_spec (by decide) ha).mp h1
      nlinarith
    · have hbR : IK.val b ≤ -(3 / 5 : ℝ) := by
        rw [← hnegR]; exact (qle_spec hb (by decide)).mp h2
      nlinarith
  have hg_pos : ∀ s : ℝ, IK.val a ≤ s → s ≤ IK.val b →
      0 < (s - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
    intro s hsa hsb
    have hs2 := hs_out s hsa hsb
    by_contra hle
    push_neg at hle
    have h1 : s - IK.val c.cx = 0 := by nlinarith [sq_nonneg (s - IK.val c.cx), sq_nonneg (IK.val c.cy)]
    have h2 : IK.val c.cy = 0 := by nlinarith [sq_nonneg (s - IK.val c.cx), sq_nonneg (IK.val c.cy)]
    have hsx : s = IK.val c.cx := sub_eq_zero.mp h1
    nlinarith [hrad, hs2]
  rcases clampQ_bounds_and_sq_le_g ha hb hcx2 (le_of_lt hab) with ⟨hcl_lo, hcl_hi, hcl_sq⟩
  have hgmin_pos : 0 < IK.val gmin := by
    rw [hgmin_val]
    exact hg_pos (IK.val (clampQ a b c.cx)) hcl_lo hcl_hi
  have hgmin_le_gm : IK.val gmin ≤ IK.val gm := by
    rw [hgmin_val, hgm_val, hm_val]
    linarith
  have hgm_pos : 0 < IK.val gm := lt_of_lt_of_le hgmin_pos hgmin_le_gm
  have hgm1 : 0 < gm.1 := fst_pos_of_val_pos_g hgm_den hgm_pos
  have h2gmin_den : 0 < (qmul (2, 1) gmin).2 := qmul_den_pos_g (by decide) hgmin_den
  have h2gmin_val : IK.val (qmul (2, 1) gmin) = 2 * IK.val gmin := by
    rw [val_qmul]; have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
    rw [h2]
  have h2gmin_pos : 0 < IK.val (qmul (2, 1) gmin) := by rw [h2gmin_val]; linarith
  have h2gmin1 : (qmul (2, 1) gmin).1 ≠ 0 := (fst_pos_of_val_pos_g h2gmin_den h2gmin_pos).ne'
  have hdiv1_den : 0 < (qdiv (qsub m c.cx) gm).2 :=
    qdiv_den_pos_g (qsub_den_pos hm_den hcx2) hgm1.ne'
  have hdiv2_den : 0 < (qdiv (qsq hw) (qmul (2, 1) gmin)).2 :=
    qdiv_den_pos_g (qsq_den_pos_g hhw_den) h2gmin1
  have htail_den : 0 < tailQ.2 :=
    qadd_den_pos (qmul_den_pos_g (qabs_den_pos_g hdiv1_den) hhw_den) hdiv2_den
  have htail_val : IK.val tailQ =
      |(IK.val m - IK.val c.cx) / IK.val gm| * IK.val hw +
        (IK.val hw) ^ 2 / (2 * IK.val gmin) := by
    dsimp [tailQ]
    rw [val_qadd (qmul_den_pos_g (qabs_den_pos_g hdiv1_den) hhw_den) hdiv2_den,
      val_qmul, val_qabs_local_g hdiv1_den,
      val_qdiv (qsub_den_pos hm_den hcx2) hgm_den hgm1.ne', val_qsub hm_den hcx2,
      val_qdiv (qsq_den_pos_g hhw_den) h2gmin_den h2gmin1, val_qsq_local_g, h2gmin_val]
  refine ⟨IK.val wgt * ((1 / 2 : ℝ) * Real.log (IK.val gm) + IK.val tailQ), ?_, ?_⟩
  · have hcond : (qle R a || qle b (qneg R)) = true := by rcases hout with h | h <;> simp [h]
    unfold poiRealI
    rw [if_pos hcond]
    have hlog := IK.logQ_mem fieldMode.ntl hgm1 hgm_den
    have hsmul_half := IK.smulQ_mem (c := (1, 2)) (by decide) hlog
    have hhalf_val : IK.val (1, 2) = (1 / 2 : ℝ) := by norm_num [IK.val]
    have hsmul_half' := IK.mem_of_eq hsmul_half (by rw [hhalf_val])
    have hadd := IK.add_mem hsmul_half' (IK.ofQ_mem htail_den)
    exact IK.smulQ_mem hwgt_den hadd
  · intro t hta htb
    rw [hwgt_val]
    have hw_nonneg : 0 ≤ (c.mult : ℝ) * IK.val c.w := by
      apply mul_nonneg (Nat.cast_nonneg _)
      unfold IK.val
      exact div_nonneg (by exact_mod_cast hw1) (by exact_mod_cast hw2.le)
    apply mul_le_mul_of_nonneg_left _ hw_nonneg
    rw [htail_val]
    have hgt : 0 < (t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := hg_pos t hta htb
    have htm : |t - IK.val m| ≤ IK.val hw := by
      rw [hm_val, hhw_val, abs_le]
      constructor <;> linarith
    have hquad : ((t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2) - IK.val gm =
        2 * (IK.val m - IK.val c.cx) * (t - IK.val m) + 1 * (t - IK.val m) ^ 2 := by
      rw [hgm_val]; ring
    have hbound := half_log_quadratic_upper_g hgt hgm_pos hgmin_pos hgmin_le_gm
      (by norm_num : (0 : ℝ) ≤ 1) (by rw [hhw_val]; linarith) htm hquad
    simpa only [one_mul] using hbound

private theorem poiRealI_mem_and_bound_inside_g
    (c : PR) (hc : 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2 ∧ 0 ≤ c.w.1 ∧
      ¬ (c.cx.1 = 0 ∧ c.cy.1 = 0) ∧
      0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ∧
      (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2 ∧
      ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) {a b : QF} {lr : IV}
    (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (ha : 0 < a.2) (hb : 0 < b.2)
    (hloa : -(3 / 5 : ℝ) ≤ IK.val a) (hab : IK.val a < IK.val b)
    (hbhi : IK.val b ≤ (3 / 5 : ℝ)) :
    ∃ Uc : ℝ, IV.mem (poiRealI fieldMode c a b lr) Uc ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b →
        (c.mult : ℝ) * IK.val c.w *
          ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2) -
            Real.log (3 / 5 : ℝ)) ≤ Uc := by
  rcases hc with ⟨hcx2, hcy2, hw2, hw1, hnot0, hcc_pos_val, hrad, _⟩
  let m := qhalf (qadd a b)
  let hw := qhalf (qsub b a)
  let wgt := qmul (Int.ofNat c.mult, 1) c.w
  let cc := qadd (qsq c.cx) (qsq c.cy)
  let tstar := qdiv (qmul R2 c.cx) cc
  let cl := clampQ a b tstar
  let gm := giQ c m
  let gmin := giQ c cl
  let derNum := qadd (qmul (qmul (-2, 1) c.cx) (qsub R2 (qmul c.cx m)))
    (qmul (qmul (2, 1) (qsq c.cy)) m)
  let der := qdiv derNum (qmul (2, 1) gm)
  let tailQ := qadd (qmul (qabs der) hw)
    (qdiv (qmul cc (qsq hw)) (qmul (2, 1) gmin))
  have hm_den : 0 < m.2 := qhalf_den_pos_g (qadd_den_pos ha hb)
  have hhw_den : 0 < hw.2 := qhalf_den_pos_g (qsub_den_pos hb ha)
  have hwgt_den : 0 < wgt.2 := qmul_den_pos_g zero_lt_one hw2
  have hcc_den : 0 < cc.2 := qadd_den_pos (qsq_den_pos_g hcx2) (qsq_den_pos_g hcy2)
  have hcc_val : IK.val cc = (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
    dsimp [cc]
    rw [val_qadd (qsq_den_pos_g hcx2) (qsq_den_pos_g hcy2), val_qsq_local_g, val_qsq_local_g]
  have hcc_pos : 0 < IK.val cc := by rw [hcc_val]; exact hcc_pos_val
  have hcc1 : 0 < cc.1 := fst_pos_of_val_pos_g hcc_den hcc_pos
  have htstar_den : 0 < tstar.2 :=
    qdiv_den_pos_g (qmul_den_pos_g (by decide) hcx2) hcc1.ne'
  have hcl_den : 0 < cl.2 := clampQ_den_pos_g ha hb htstar_den
  have hgiQ_den : ∀ q : QF, 0 < q.2 → 0 < (giQ c q).2 := fun q hq =>
    qadd_den_pos (qsq_den_pos_g (qsub_den_pos (by decide) (qmul_den_pos_g hcx2 hq)))
      (qsq_den_pos_g (qmul_den_pos_g hcy2 hq))
  have hgiQ_val : ∀ q : QF, 0 < q.2 →
      IK.val (giQ c q) = (9 / 25 - IK.val c.cx * IK.val q) ^ 2 + (IK.val c.cy * IK.val q) ^ 2 := by
    intro q hq
    unfold giQ
    rw [val_qadd (qsq_den_pos_g (qsub_den_pos (by decide) (qmul_den_pos_g hcx2 hq)))
        (qsq_den_pos_g (qmul_den_pos_g hcy2 hq)),
      val_qsq_local_g, val_qsq_local_g, val_qsub (by decide) (qmul_den_pos_g hcx2 hq),
      val_qmul, val_qmul]
    have hR2 : IK.val R2 = (9 / 25 : ℝ) := by norm_num [R2, IK.val]
    rw [hR2]
  have hgm_den : 0 < gm.2 := hgiQ_den m hm_den
  have hgmin_den : 0 < gmin.2 := hgiQ_den cl hcl_den
  have hm_val : IK.val m = (IK.val a + IK.val b) / 2 := by
    dsimp [m]; rw [val_qhalf_local_g, val_qadd ha hb]
  have hhw_val : IK.val hw = (IK.val b - IK.val a) / 2 := by
    dsimp [hw]; rw [val_qhalf_local_g, val_qsub hb ha]
  have hwgt_val : IK.val wgt = (c.mult : ℝ) * IK.val c.w := by
    dsimp [wgt]; rw [val_qmul]
    have hmval : IK.val ((c.mult : ℤ), 1) = (c.mult : ℝ) := by
      unfold IK.val; simp
    rw [hmval]
  have htstar_val : IK.val tstar = (9 / 25 : ℝ) * IK.val c.cx / IK.val cc := by
    dsimp [tstar]
    rw [val_qdiv (qmul_den_pos_g (by decide) hcx2) hcc_den hcc1.ne', val_qmul]
    have hR2 : IK.val R2 = (9 / 25 : ℝ) := by norm_num [R2, IK.val]
    rw [hR2]
  have hgi_complete : ∀ s : ℝ,
      (9 / 25 - IK.val c.cx * s) ^ 2 + (IK.val c.cy * s) ^ 2 =
        IK.val cc * (s - IK.val tstar) ^ 2 +
          (9 / 25 : ℝ) ^ 2 * (IK.val c.cy) ^ 2 / IK.val cc := by
    intro s
    rw [htstar_val, hcc_val]
    have hcc_ne : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 ≠ 0 := ne_of_gt hcc_pos_val
    field_simp [hcc_ne]
    ring
  have hgi_pos : ∀ s : ℝ, -(3 / 5 : ℝ) ≤ s → s ≤ (3 / 5 : ℝ) →
      0 < (9 / 25 - IK.val c.cx * s) ^ 2 + (IK.val c.cy * s) ^ 2 := by
    intro s hs1 hs2
    have hcx_sq : (IK.val c.cx) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
      nlinarith [hrad, sq_nonneg (IK.val c.cy)]
    have hs_sq : s ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by nlinarith
    have hprod_sq : (IK.val c.cx * s) ^ 2 < (9 / 25 : ℝ) ^ 2 := by
      calc
        (IK.val c.cx * s) ^ 2 = (IK.val c.cx) ^ 2 * s ^ 2 := by ring
        _ ≤ (IK.val c.cx) ^ 2 * (3 / 5 : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hs_sq (sq_nonneg _)
        _ < (3 / 5 : ℝ) ^ 2 * (3 / 5 : ℝ) ^ 2 :=
            mul_lt_mul_of_pos_right hcx_sq (by norm_num)
        _ = (9 / 25 : ℝ) ^ 2 := by norm_num
    have hsub_pos : 0 < (9 / 25 : ℝ) - IK.val c.cx * s := by
      nlinarith [sq_nonneg ((9 / 25 : ℝ) + IK.val c.cx * s)]
    nlinarith [sq_pos_of_pos hsub_pos, sq_nonneg (IK.val c.cy * s)]
  rcases clampQ_bounds_and_sq_le_g ha hb htstar_den (le_of_lt hab) with ⟨hcl_lo, hcl_hi, hcl_sq⟩
  have hgmin_pos : 0 < IK.val gmin := by
    rw [hgiQ_val cl hcl_den]
    exact hgi_pos (IK.val cl) (le_trans hloa hcl_lo) (le_trans hcl_hi hbhi)
  have hgmin_le_gm : IK.val gmin ≤ IK.val gm := by
    rw [hgiQ_val cl hcl_den, hgiQ_val m hm_den,
      hgi_complete (IK.val cl), hgi_complete (IK.val m), hm_val]
    have hmul := mul_le_mul_of_nonneg_left hcl_sq (le_of_lt hcc_pos)
    linarith
  have hgm_pos : 0 < IK.val gm := lt_of_lt_of_le hgmin_pos hgmin_le_gm
  have hgm1 : 0 < gm.1 := fst_pos_of_val_pos_g hgm_den hgm_pos
  have h2gm_den : 0 < (qmul (2, 1) gm).2 := qmul_den_pos_g (by decide) hgm_den
  have h2gm_val : IK.val (qmul (2, 1) gm) = 2 * IK.val gm := by
    rw [val_qmul]; have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
    rw [h2]
  have h2gm_pos : 0 < IK.val (qmul (2, 1) gm) := by rw [h2gm_val]; linarith
  have h2gm1 : (qmul (2, 1) gm).1 ≠ 0 := (fst_pos_of_val_pos_g h2gm_den h2gm_pos).ne'
  have h2gmin_den : 0 < (qmul (2, 1) gmin).2 := qmul_den_pos_g (by decide) hgmin_den
  have h2gmin_val : IK.val (qmul (2, 1) gmin) = 2 * IK.val gmin := by
    rw [val_qmul]; have h2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
    rw [h2]
  have h2gmin_pos : 0 < IK.val (qmul (2, 1) gmin) := by rw [h2gmin_val]; linarith
  have h2gmin1 : (qmul (2, 1) gmin).1 ≠ 0 := (fst_pos_of_val_pos_g h2gmin_den h2gmin_pos).ne'
  have hderNum_den : 0 < derNum.2 :=
    qadd_den_pos (qmul_den_pos_g (qmul_den_pos_g (by decide) hcx2)
        (qsub_den_pos (by decide) (qmul_den_pos_g hcx2 hm_den)))
      (qmul_den_pos_g (qmul_den_pos_g (by decide) (qsq_den_pos_g hcy2)) hm_den)
  have hder_den : 0 < der.2 := qdiv_den_pos_g hderNum_den h2gm1
  have hdiv2_den : 0 < (qdiv (qmul cc (qsq hw)) (qmul (2, 1) gmin)).2 :=
    qdiv_den_pos_g (qmul_den_pos_g hcc_den (qsq_den_pos_g hhw_den)) h2gmin1
  have htail_den : 0 < tailQ.2 :=
    qadd_den_pos (qmul_den_pos_g (qabs_den_pos_g hder_den) hhw_den) hdiv2_den
  let A := -IK.val c.cx * (9 / 25 - IK.val c.cx * IK.val m) + (IK.val c.cy) ^ 2 * IK.val m
  have hder_val : IK.val der = A / IK.val gm := by
    dsimp [der, derNum, A]
    rw [val_qdiv hderNum_den h2gm_den h2gm1,
      val_qadd (qmul_den_pos_g (qmul_den_pos_g (by decide) hcx2)
          (qsub_den_pos (by decide) (qmul_den_pos_g hcx2 hm_den)))
        (qmul_den_pos_g (qmul_den_pos_g (by decide) (qsq_den_pos_g hcy2)) hm_den),
      val_qmul, val_qmul, val_qsub (by decide) (qmul_den_pos_g hcx2 hm_den), val_qmul,
      val_qmul, val_qmul, val_qsq_local_g, h2gm_val]
    have hR2 : IK.val R2 = (9 / 25 : ℝ) := by norm_num [R2, IK.val]
    have hm2 : IK.val (-2, 1) = -2 := by norm_num [IK.val]
    have hp2 : IK.val (2, 1) = 2 := by norm_num [IK.val]
    rw [hR2, hm2, hp2]
    field_simp [ne_of_gt hgm_pos]
  have htail_val : IK.val tailQ =
      |A / IK.val gm| * IK.val hw + IK.val cc * (IK.val hw) ^ 2 / (2 * IK.val gmin) := by
    dsimp [tailQ]
    rw [val_qadd (qmul_den_pos_g (qabs_den_pos_g hder_den) hhw_den) hdiv2_den,
      val_qmul, val_qabs_local_g hder_den, hder_val,
      val_qdiv (qmul_den_pos_g hcc_den (qsq_den_pos_g hhw_den)) h2gmin_den h2gmin1,
      val_qmul, val_qsq_local_g, h2gmin_val]
  refine ⟨IK.val wgt * (((1 / 2 : ℝ) * Real.log (IK.val gm) - Real.log (3 / 5 : ℝ)) +
      IK.val tailQ), ?_, ?_⟩
  · have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    have hnegR : IK.val (qneg R) = -(3 / 5 : ℝ) := by norm_num [R, qneg, IK.val]
    have hnot_out : (qle R a || qle b (qneg R)) = false := by
      rw [Bool.or_eq_false_iff]
      constructor
      · rw [Bool.eq_false_iff]
        intro h1
        have haR : (3 / 5 : ℝ) ≤ IK.val a := by
          rw [← hR]; exact (qle_spec (by decide) ha).mp h1
        linarith
      · rw [Bool.eq_false_iff]
        intro h2
        have hbR : IK.val b ≤ -(3 / 5 : ℝ) := by
          rw [← hnegR]; exact (qle_spec hb (by decide)).mp h2
        linarith
    have hin : (qle (qneg R) a && qle b R) = true := by
      rw [Bool.and_eq_true]
      constructor
      · exact (qle_spec (by decide) ha).mpr (by rw [hnegR]; exact hloa)
      · exact (qle_spec hb (by decide)).mpr (by rw [hR]; exact hbhi)
    unfold poiRealI
    rw [if_neg (by rw [hnot_out]; decide), if_pos hin, if_neg hnot0]
    have hlog := IK.logQ_mem fieldMode.ntl hgm1 hgm_den
    have hsmul_half := IK.smulQ_mem (c := (1, 2)) (by decide) hlog
    have hhalf_val : IK.val (1, 2) = (1 / 2 : ℝ) := by norm_num [IK.val]
    have hsmul_half' := IK.mem_of_eq hsmul_half (by rw [hhalf_val])
    have hsub := IK.sub_mem hsmul_half' hlr
    have hadd := IK.add_mem hsub (IK.ofQ_mem htail_den)
    exact IK.smulQ_mem hwgt_den hadd
  · intro t hta htb
    rw [hwgt_val]
    have hw_nonneg : 0 ≤ (c.mult : ℝ) * IK.val c.w := by
      apply mul_nonneg (Nat.cast_nonneg _)
      unfold IK.val
      exact div_nonneg (by exact_mod_cast hw1) (by exact_mod_cast hw2.le)
    apply mul_le_mul_of_nonneg_left _ hw_nonneg
    rw [htail_val]
    have hgt : 0 < (9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2 :=
      hgi_pos t (le_trans hloa hta) (le_trans htb hbhi)
    have htm : |t - IK.val m| ≤ IK.val hw := by
      rw [hm_val, hhw_val, abs_le]
      constructor <;> linarith
    have hquad : ((9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2) - IK.val gm =
        2 * A * (t - IK.val m) + IK.val cc * (t - IK.val m) ^ 2 := by
      rw [hgiQ_val m hm_den, hcc_val]
      dsimp [A]
      ring
    have hbound := half_log_quadratic_upper_g hgt hgm_pos hgmin_pos hgmin_le_gm
      (le_of_lt hcc_pos) (by rw [hhw_val]; linarith) htm hquad
    linarith

private theorem list_map_sum_le_g {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ c ∈ l, f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h c (by simp)) (ih fun d hd => h d (by simp [hd]))

private theorem sumI_map_exists_upper_g {α : Type*} (l : List α)
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
    refine list_map_sum_le_g l (g t) u (fun c hc => ?_)
    dsimp [u]
    rw [dif_pos hc]
    exact (Classical.choose_spec (h c hc)).2 t hta htb

private theorem poiRealSum_mem_and_bound_outside_g
    {q : ℕ} (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    {a b : QF} (lr : IV)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : IK.val a < IK.val b)
    (hout : qle R a = true ∨ qle b (qneg R) = true)
    (ht_out : ∀ t, IK.val a ≤ t → t ≤ IK.val b → (3 / 5 : ℝ) ≤ |t|) :
    ∃ U : ℝ, IV.mem (poiRealSum fieldMode Dr.data.pre a b lr) U ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b →
        (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure Dr.data.full) ≤ U := by
  unfold poiRealSum
  rcases sumI_map_exists_upper_g Dr.data.pre
    (fun c => poiRealI fieldMode c a b lr)
    (fun t c => (c.mult : ℝ) * IK.val c.w *
      ((1 / 2 : ℝ) * Real.log ((t - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)))
    (a0 := IK.val a) (b0 := IK.val b)
    (fun c hc => poiRealI_mem_and_bound_outside_g c (hDr.pre_rows_data c hc) lr ha hb hab hout)
    with ⟨U, hU_mem, hU_le⟩
  refine ⟨U, hU_mem, ?_⟩
  intro t hta htb
  rw [integral_v13PoissonMeasure_outside_eq_pre_sum Dr hDr (ht_out t hta htb)]
  exact hU_le t hta htb

private theorem poiRealSum_mem_and_bound_inside_g
    {q : ℕ} (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    {a b : QF} {lr : IV}
    (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (ha : 0 < a.2) (hb : 0 < b.2)
    (hloa : -(3 / 5 : ℝ) ≤ IK.val a) (hab : IK.val a < IK.val b)
    (hbhi : IK.val b ≤ (3 / 5 : ℝ)) :
    ∃ U : ℝ, IV.mem (poiRealSum fieldMode Dr.data.pre a b lr) U ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b →
        (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure Dr.data.full) ≤ U := by
  unfold poiRealSum
  rcases sumI_map_exists_upper_g Dr.data.pre
    (fun c => poiRealI fieldMode c a b lr)
    (fun t c => (c.mult : ℝ) * IK.val c.w *
      ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * t) ^ 2 + (IK.val c.cy * t) ^ 2) -
        Real.log (3 / 5 : ℝ)))
    (a0 := IK.val a) (b0 := IK.val b)
    (fun c hc => poiRealI_mem_and_bound_inside_g c (hDr.pre_rows_data c hc) hlr ha hb hloa hab hbhi)
    with ⟨U, hU_mem, hU_le⟩
  refine ⟨U, hU_mem, ?_⟩
  intro t hta htb
  have ht_in : |t| ≤ (3 / 5 : ℝ) := by
    rw [abs_le]
    exact ⟨le_trans hloa hta, le_trans htb hbhi⟩
  rw [integral_v13PoissonMeasure_inside_eq_pre_sum Dr hDr ht_in]
  exact hU_le t hta htb



theorem v13_μz_integral_log_norm_sub_real
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr)) (t : ℝ) :
    (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂(v13RefMeasure Dr N).μz) =
      (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.zp) +
        (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13PoissonMeasure Dr.data.full) := by
  change (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖
    ∂(v13DecodedChainMeasure Dr.data.zp + v13PoissonMeasure Dr.data.full)) = _
  have hIntZ : Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)
      (v13DecodedChainMeasure Dr.data.zp) :=
    integrable_v13DecodedChainMeasure_log_norm_sub_g Dr.data.zp t
      (fun c hc => (hDr.z_cells c hc).1)
  have hIntP : Integrable (fun z : ℂ => Real.log ‖(t : ℂ) - z‖)
      (v13PoissonMeasure Dr.data.full) :=
    integrable_v13PoissonMeasure_log_norm_sub_g Dr.data.full t
      (fun c hc => (hDr.full_rows_data c hc).2.2.2.2.2.2.2)
  exact integral_add_measure hIntZ hIntP

set_option maxHeartbeats 10000000
/-- Piece `.x` cell soundness on `[1/250, 1]` for decoded rows `Dr`. -/
theorem v13_field_x_cell_on_of_lr
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (lr : IV) :
    CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (V.EnergyCertI.fieldUB Dr.data q lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure Dr N) (t : ℂ)) := by
  intro a b ha hb hloa hab hbhi
  have hq0 : 0 < q := by have h2 := hq.1; omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlo_val : IK.val (pieceDomain q .x).1 = (1 / 250 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have ha_pos : 0 < IK.val a := by linarith
  have hb_pos : 0 < IK.val b := lt_trans ha_pos hab
  have hb1 : 0 < b.1 := fst_pos_of_val_pos_g hb hb_pos
  let Ux := - (Dr.data.xp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Uv := (Dr.data.vp.map fun p =>
    IK.val p.J * lamReal_g q (IK.val a) (IK.val p.e)).sum
  let Ulog := (3 / 4 : ℝ) * Real.log (IK.val b)
  refine ⟨(2 * Ux + Uv) + Ulog, ?_, ?_⟩
  · change IV.mem (fxUB fieldMode Dr.data q a b) ((2 * Ux + Uv) + Ulog)
    unfold fxUB
    have hUx : IV.mem (ubarI fieldMode Dr.data.xp a b) Ux :=
      ubarI_mem_g fieldMode Dr.data.xp ha hb
        (fun p hp => ⟨(hDr.x_rows p hp).2.1, (hDr.x_rows p hp).2.2⟩)
    have h2Ux : IV.mem (smulInt 2 (ubarI fieldMode Dr.data.xp a b)) (2 * Ux) := by
      simpa using IK.smulInt_mem 2 hUx
    have hUv : IV.mem (IK.neg (dlowI fieldMode q Dr.data.vp a)) Uv :=
      neg_dlowI_mem_g fieldMode q Dr.data.vp hq0 ha ha_pos hDr.v_rows
    have hlog : IV.mem (smulQ (3, 4) (logQ fieldMode.ntl b)) Ulog := by
      have h := IK.smulQ_mem (c := (3, 4)) (by decide) (IK.logQ_mem fieldMode.ntl hb1 hb)
      have h34 : IK.val (3, 4) = (3 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.mem_of_eq h (by rw [h34])
    exact IK.add_mem (IK.add_mem h2Ux hUv) hlog
  · intro t hta htb
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos hta
    unfold V.signedVFullFieldX V.signedVFieldX
    dsimp only
    rw [show (v13RefMeasure Dr N).q = q by rfl]
    rw [show (v13RefMeasure Dr N).μx = v13DecodedChainMeasure Dr.data.xp by rfl]
    rw [show (v13RefMeasure Dr N).μv = v13DecodedChainMeasure Dr.data.vp by rfl]
    have hx_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.xp) ≤ Ux :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.xp hta htb
        (fun c hc => (hDr.x_cells c hc).2.1)
        (fun c hc => (hDr.x_cells c hc).2.2)
        hDr.x_jump
    have hv_le : - (∫ z : ℂ, V.vCrossKernel q (t : ℂ) z ∂v13DecodedChainMeasure Dr.data.vp) ≤ Uv :=
      neg_integral_vCrossKernel_right_le_g Dr.data.vp hqR ha_pos hta
        (fun c hc => ⟨(hDr.v_cells c hc).1, (hDr.v_cells c hc).2.1⟩)
        (fun c hc => (hDr.v_cells c hc).2.2)
        hDr.v_jump
    have hlog_le : (3 / 4 : ℝ) * Real.log ‖(t : ℂ)‖ ≤ Ulog := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log ht_pos htb) (by norm_num)
    linarith
theorem v13_field_vlo_cell_on_of_lr
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (V.EnergyCertI.fieldUB Dr.data q lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure Dr N) (t : ℂ)) := by
  intro a b ha hb hloa hab hbhi
  have hq0 : 0 < q := by have h2 := hq.1; omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlo_val : IK.val (pieceDomain q .vlo).1 = (1 / 250 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have hhi_val : IK.val (pieceDomain q .vlo).2 = (3 / 5 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have ha_pos : 0 < IK.val a := by linarith
  have hb_pos : 0 < IK.val b := lt_trans ha_pos hab
  have hb1 : 0 < b.1 := fst_pos_of_val_pos_g hb hb_pos
  have hloa' : -(3 / 5 : ℝ) ≤ IK.val a := by linarith
  have hbhi' : IK.val b ≤ (3 / 5 : ℝ) := by linarith
  rcases poiRealSum_mem_and_bound_inside_g Dr hDr hlr ha hb hloa' hab hbhi' with ⟨Up, hUp_mem, hUp_le⟩
  let Uv := - (Dr.data.vp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Uz := - (Dr.data.zp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Ux := (Dr.data.xp.map fun p =>
    IK.val p.J * lamReal_g q (IK.val a) (IK.val p.e)).sum
  let Ulog := (1 / 4 : ℝ) * Real.log (IK.val b)
  refine ⟨(((2 * Uv + Uz) + Up) + Ux) + Ulog, ?_, ?_⟩
  · change IV.mem (fvUB fieldMode Dr.data q a b lr) ((((2 * Uv + Uz) + Up) + Ux) + Ulog)
    unfold fvUB
    have hUv : IV.mem (ubarI fieldMode Dr.data.vp a b) Uv :=
      ubarI_mem_g fieldMode Dr.data.vp ha hb
        (fun p hp => ⟨(hDr.v_rows p hp).2.1, (hDr.v_rows p hp).2.2⟩)
    have h2Uv : IV.mem (smulInt 2 (ubarI fieldMode Dr.data.vp a b)) (2 * Uv) := by
      simpa using IK.smulInt_mem 2 hUv
    have hUz : IV.mem (ubarI fieldMode Dr.data.zp a b) Uz :=
      ubarI_mem_g fieldMode Dr.data.zp ha hb hDr.z_rows
    have hUx : IV.mem (IK.neg (dlowI fieldMode q Dr.data.xp a)) Ux :=
      neg_dlowI_mem_g fieldMode q Dr.data.xp hq0 ha ha_pos hDr.x_rows
    have hlog : IV.mem (smulQ (1, 4) (logQ fieldMode.ntl b)) Ulog := by
      have h := IK.smulQ_mem (c := (1, 4)) (by decide) (IK.logQ_mem fieldMode.ntl hb1 hb)
      have h14 : IK.val (1, 4) = (1 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.mem_of_eq h (by rw [h14])
    exact IK.add_mem (IK.add_mem (IK.add_mem (IK.add_mem h2Uv hUz) hUp_mem) hUx) hlog
  · intro t hta htb
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos hta
    unfold V.signedVFullFieldV V.signedVFieldV
    dsimp only
    rw [show (v13RefMeasure Dr N).q = q by rfl]
    rw [show (v13RefMeasure Dr N).μv = v13DecodedChainMeasure Dr.data.vp by rfl]
    rw [show (v13RefMeasure Dr N).μx = v13DecodedChainMeasure Dr.data.xp by rfl]
    rw [v13_μz_integral_log_norm_sub_real Dr hDr N t]
    have hv_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.vp) ≤ Uv :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.vp hta htb
        (fun c hc => (hDr.v_cells c hc).2.1)
        (fun c hc => (hDr.v_cells c hc).2.2)
        hDr.v_jump
    have hz_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.zp) ≤ Uz :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.zp hta htb
        (fun c hc => (hDr.z_cells c hc).1)
        (fun c hc => (hDr.z_cells c hc).2)
        hDr.z_jump
    have hp_le := hUp_le t hta htb
    have hx_le : - (∫ z : ℂ, V.vCrossKernel q z (t : ℂ) ∂v13DecodedChainMeasure Dr.data.xp) ≤ Ux :=
      neg_integral_vCrossKernel_left_le_g Dr.data.xp hqR ha_pos hta
        (fun c hc => ⟨(hDr.x_cells c hc).1, (hDr.x_cells c hc).2.1⟩)
        (fun c hc => (hDr.x_cells c hc).2.2)
        hDr.x_jump
    have hlog_le : (1 / 4 : ℝ) * Real.log ‖(t : ℂ)‖ ≤ Ulog := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log ht_pos htb) (by norm_num)
    linarith

/-- Piece `.vhi` cell soundness on `[3/5, 1]` for decoded rows `Dr`. -/
theorem v13_field_vhi_cell_on_of_lr
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (lr : IV) :
    CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (V.EnergyCertI.fieldUB Dr.data q lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure Dr N) (t : ℂ)) := by
  intro a b ha hb hloa hab hbhi
  have hq0 : 0 < q := by have h2 := hq.1; omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlo_val : IK.val (pieceDomain q .vhi).1 = (3 / 5 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have ha_ge : (3 / 5 : ℝ) ≤ IK.val a := by linarith
  have ha_pos : 0 < IK.val a := by linarith
  have hb_pos : 0 < IK.val b := lt_trans ha_pos hab
  have hb1 : 0 < b.1 := fst_pos_of_val_pos_g hb hb_pos
  have hout : qle R a = true ∨ qle b (qneg R) = true := by
    left
    have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    exact (qle_spec (by decide) ha).mpr (by rw [hR]; exact ha_ge)
  have ht_out : ∀ t, IK.val a ≤ t → t ≤ IK.val b → (3 / 5 : ℝ) ≤ |t| := by
    intro t hta _
    rw [abs_of_pos (lt_of_lt_of_le ha_pos hta)]
    linarith
  rcases poiRealSum_mem_and_bound_outside_g Dr hDr lr ha hb hab hout ht_out with ⟨Up, hUp_mem, hUp_le⟩
  let Uv := - (Dr.data.vp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Uz := - (Dr.data.zp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Ux := (Dr.data.xp.map fun p =>
    IK.val p.J * lamReal_g q (IK.val a) (IK.val p.e)).sum
  let Ulog := (1 / 4 : ℝ) * Real.log (IK.val b)
  refine ⟨(((2 * Uv + Uz) + Up) + Ux) + Ulog, ?_, ?_⟩
  · change IV.mem (fvUB fieldMode Dr.data q a b lr) ((((2 * Uv + Uz) + Up) + Ux) + Ulog)
    unfold fvUB
    have hUv : IV.mem (ubarI fieldMode Dr.data.vp a b) Uv :=
      ubarI_mem_g fieldMode Dr.data.vp ha hb
        (fun p hp => ⟨(hDr.v_rows p hp).2.1, (hDr.v_rows p hp).2.2⟩)
    have h2Uv : IV.mem (smulInt 2 (ubarI fieldMode Dr.data.vp a b)) (2 * Uv) := by
      simpa using IK.smulInt_mem 2 hUv
    have hUz : IV.mem (ubarI fieldMode Dr.data.zp a b) Uz :=
      ubarI_mem_g fieldMode Dr.data.zp ha hb hDr.z_rows
    have hUx : IV.mem (IK.neg (dlowI fieldMode q Dr.data.xp a)) Ux :=
      neg_dlowI_mem_g fieldMode q Dr.data.xp hq0 ha ha_pos hDr.x_rows
    have hlog : IV.mem (smulQ (1, 4) (logQ fieldMode.ntl b)) Ulog := by
      have h := IK.smulQ_mem (c := (1, 4)) (by decide) (IK.logQ_mem fieldMode.ntl hb1 hb)
      have h14 : IK.val (1, 4) = (1 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.mem_of_eq h (by rw [h14])
    exact IK.add_mem (IK.add_mem (IK.add_mem (IK.add_mem h2Uv hUz) hUp_mem) hUx) hlog
  · intro t hta htb
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos hta
    unfold V.signedVFullFieldV V.signedVFieldV
    dsimp only
    rw [show (v13RefMeasure Dr N).q = q by rfl]
    rw [show (v13RefMeasure Dr N).μv = v13DecodedChainMeasure Dr.data.vp by rfl]
    rw [show (v13RefMeasure Dr N).μx = v13DecodedChainMeasure Dr.data.xp by rfl]
    rw [v13_μz_integral_log_norm_sub_real Dr hDr N t]
    have hv_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.vp) ≤ Uv :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.vp hta htb
        (fun c hc => (hDr.v_cells c hc).2.1)
        (fun c hc => (hDr.v_cells c hc).2.2)
        hDr.v_jump
    have hz_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.zp) ≤ Uz :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.zp hta htb
        (fun c hc => (hDr.z_cells c hc).1)
        (fun c hc => (hDr.z_cells c hc).2)
        hDr.z_jump
    have hp_le := hUp_le t hta htb
    have hx_le : - (∫ z : ℂ, V.vCrossKernel q z (t : ℂ) ∂v13DecodedChainMeasure Dr.data.xp) ≤ Ux :=
      neg_integral_vCrossKernel_left_le_g Dr.data.xp hqR ha_pos hta
        (fun c hc => ⟨(hDr.x_cells c hc).1, (hDr.x_cells c hc).2.1⟩)
        (fun c hc => (hDr.x_cells c hc).2.2)
        hDr.x_jump
    have hlog_le : (1 / 4 : ℝ) * Real.log ‖(t : ℂ)‖ ≤ Ulog := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log ht_pos htb) (by norm_num)
    linarith

/-- Piece `.zneg` cell soundness on `[-2, -3/5]` for decoded rows `Dr`. -/
theorem v13_field_zneg_cell_on_of_lr
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (lr : IV) :
    CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (V.EnergyCertI.fieldUB Dr.data q lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure Dr N) (t : ℂ)) := by
  intro a b ha hb hloa hab hbhi
  have hq0 : 0 < q := by have h2 := hq.1; omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hhi_val : IK.val (pieceDomain q .zneg).2 = -(3 / 5 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have hb_le : IK.val b ≤ -(3 / 5 : ℝ) := by linarith
  have hnegb_pos : 0 < IK.val (qneg b) := by rw [val_qneg]; linarith
  have hnegb1 : 0 < (qneg b).1 := fst_pos_of_val_pos_g (qneg_den_pos_g hb) hnegb_pos
  have hout : qle R a = true ∨ qle b (qneg R) = true := by
    right
    have hnegR : IK.val (qneg R) = -(3 / 5 : ℝ) := by norm_num [R, qneg, IK.val]
    exact (qle_spec hb (by decide)).mpr (by rw [hnegR]; exact hb_le)
  have ht_out : ∀ t, IK.val a ≤ t → t ≤ IK.val b → (3 / 5 : ℝ) ≤ |t| := by
    intro t _ htb
    have ht_neg : t < 0 := by linarith
    rw [abs_of_neg ht_neg]
    linarith
  rcases poiRealSum_mem_and_bound_outside_g Dr hDr lr ha hb hab hout ht_out with ⟨Up, hUp_mem, hUp_le⟩
  let Uz := - (Dr.data.zp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Uv := - (Dr.data.vp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Ulog := (-5 / 4 : ℝ) * Real.log (-IK.val b)
  refine ⟨(2 * (Uz + Up) + Uv) + Ulog, ?_, ?_⟩
  · change IV.mem (fzNegUB fieldMode Dr.data a b lr) ((2 * (Uz + Up) + Uv) + Ulog)
    unfold fzNegUB
    have hUz : IV.mem (ubarI fieldMode Dr.data.zp a b) Uz :=
      ubarI_mem_g fieldMode Dr.data.zp ha hb hDr.z_rows
    have hUzp : IV.mem (IK.add (ubarI fieldMode Dr.data.zp a b)
        (poiRealSum fieldMode Dr.data.pre a b lr)) (Uz + Up) :=
      IK.add_mem hUz hUp_mem
    have h2Uzp : IV.mem (smulInt 2 (IK.add (ubarI fieldMode Dr.data.zp a b)
        (poiRealSum fieldMode Dr.data.pre a b lr))) (2 * (Uz + Up)) := by
      simpa using IK.smulInt_mem 2 hUzp
    have hUv : IV.mem (ubarI fieldMode Dr.data.vp a b) Uv :=
      ubarI_mem_g fieldMode Dr.data.vp ha hb
        (fun p hp => ⟨(hDr.v_rows p hp).2.1, (hDr.v_rows p hp).2.2⟩)
    have hlog : IV.mem (smulQ (-5, 4) (logQ fieldMode.ntl (qneg b))) Ulog := by
      have h := IK.smulQ_mem (c := (-5, 4)) (by decide)
        (IK.logQ_mem fieldMode.ntl hnegb1 (qneg_den_pos_g hb))
      have hm54 : IK.val (-5, 4) = (-5 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.mem_of_eq h (by rw [hm54, val_qneg])
    exact IK.add_mem (IK.add_mem h2Uzp hUv) hlog
  · intro t hta htb
    have ht_neg : t < 0 := by linarith
    unfold V.signedVFullFieldZ V.signedVFieldZ
    dsimp only
    rw [show (v13RefMeasure Dr N).μv = v13DecodedChainMeasure Dr.data.vp by rfl]
    rw [v13_μz_integral_log_norm_sub_real Dr hDr N t]
    have hz_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.zp) ≤ Uz :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.zp hta htb
        (fun c hc => (hDr.z_cells c hc).1)
        (fun c hc => (hDr.z_cells c hc).2)
        hDr.z_jump
    have hp_le := hUp_le t hta htb
    have hv_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.vp) ≤ Uv :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.vp hta htb
        (fun c hc => (hDr.v_cells c hc).2.1)
        (fun c hc => (hDr.v_cells c hc).2.2)
        hDr.v_jump
    have hlog_ge : Real.log (-IK.val b) ≤ Real.log ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht_neg]
      exact Real.log_le_log (by linarith) (by linarith)
    dsimp [Ulog]
    linarith

/-- Piece `.zpos` cell soundness on `[3/5, 1]` for decoded rows `Dr`. -/
theorem v13_field_zpos_cell_on_of_lr
    {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (lr : IV) :
    CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (V.EnergyCertI.fieldUB Dr.data q lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure Dr N) (t : ℂ)) := by
  intro a b ha hb hloa hab hbhi
  have hq0 : 0 < q := by have h2 := hq.1; omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlo_val : IK.val (pieceDomain q .zpos).1 = (3 / 5 : ℝ) := by
    norm_num [pieceDomain, IK.val]
  have ha_ge : (3 / 5 : ℝ) ≤ IK.val a := by linarith
  have ha_pos : 0 < IK.val a := by linarith
  have ha1 : 0 < a.1 := fst_pos_of_val_pos_g ha ha_pos
  have hout : qle R a = true ∨ qle b (qneg R) = true := by
    left
    have hR : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
    exact (qle_spec (by decide) ha).mpr (by rw [hR]; exact ha_ge)
  have ht_out : ∀ t, IK.val a ≤ t → t ≤ IK.val b → (3 / 5 : ℝ) ≤ |t| := by
    intro t hta _
    rw [abs_of_pos (lt_of_lt_of_le ha_pos hta)]
    linarith
  rcases poiRealSum_mem_and_bound_outside_g Dr hDr lr ha hb hab hout ht_out with ⟨Up, hUp_mem, hUp_le⟩
  let Uz := - (Dr.data.zp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Uv := - (Dr.data.vp.map fun p =>
    IK.val p.J * psiReal_g (IK.val a) (IK.val b) (IK.val p.e)).sum
  let Ulog := (-5 / 4 : ℝ) * Real.log (IK.val a)
  refine ⟨(2 * (Uz + Up) + Uv) + Ulog, ?_, ?_⟩
  · change IV.mem (fzPosUB fieldMode Dr.data a b lr) ((2 * (Uz + Up) + Uv) + Ulog)
    unfold fzPosUB
    have hUz : IV.mem (ubarI fieldMode Dr.data.zp a b) Uz :=
      ubarI_mem_g fieldMode Dr.data.zp ha hb hDr.z_rows
    have hUzp : IV.mem (IK.add (ubarI fieldMode Dr.data.zp a b)
        (poiRealSum fieldMode Dr.data.pre a b lr)) (Uz + Up) :=
      IK.add_mem hUz hUp_mem
    have h2Uzp : IV.mem (smulInt 2 (IK.add (ubarI fieldMode Dr.data.zp a b)
        (poiRealSum fieldMode Dr.data.pre a b lr))) (2 * (Uz + Up)) := by
      simpa using IK.smulInt_mem 2 hUzp
    have hUv : IV.mem (ubarI fieldMode Dr.data.vp a b) Uv :=
      ubarI_mem_g fieldMode Dr.data.vp ha hb
        (fun p hp => ⟨(hDr.v_rows p hp).2.1, (hDr.v_rows p hp).2.2⟩)
    have hlog : IV.mem (smulQ (-5, 4) (logQ fieldMode.ntl a)) Ulog := by
      have h := IK.smulQ_mem (c := (-5, 4)) (by decide) (IK.logQ_mem fieldMode.ntl ha1 ha)
      have hm54 : IK.val (-5, 4) = (-5 / 4 : ℝ) := by norm_num [IK.val]
      exact IK.mem_of_eq h (by rw [hm54])
    exact IK.add_mem (IK.add_mem h2Uzp hUv) hlog
  · intro t hta htb
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos hta
    unfold V.signedVFullFieldZ V.signedVFieldZ
    dsimp only
    rw [show (v13RefMeasure Dr N).μv = v13DecodedChainMeasure Dr.data.vp by rfl]
    rw [v13_μz_integral_log_norm_sub_real Dr hDr N t]
    have hz_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.zp) ≤ Uz :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.zp hta htb
        (fun c hc => (hDr.z_cells c hc).1)
        (fun c hc => (hDr.z_cells c hc).2)
        hDr.z_jump
    have hp_le := hUp_le t hta htb
    have hv_le : (∫ z : ℂ, Real.log ‖(t : ℂ) - z‖ ∂v13DecodedChainMeasure Dr.data.vp) ≤ Uv :=
      integral_v13DecodedChainMeasure_le_kMax_g Dr.data.vp hta htb
        (fun c hc => (hDr.v_cells c hc).2.1)
        (fun c hc => (hDr.v_cells c hc).2.2)
        hDr.v_jump
    have hlog_ge : Real.log (IK.val a) ≤ Real.log ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact Real.log_le_log ha_pos hta
    dsimp [Ulog]
    linarith

end H6CellGeneric
