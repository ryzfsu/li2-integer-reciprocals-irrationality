/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

import Li2Lean.B3.V13FieldCellGeneric
import Mathlib.Data.List.Chain
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.V13ArcCell
import Li2Lean.B3.V13EndpointDisk
import Li2Lean.B3.H6FieldChainGlue
import Li2Lean.B3.H6EnergyShard
import Li2Lean.B3.V13ChainLogEndpoint
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.B3.ReferenceMeasureSupportCircle
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.V13TotalIdentity
import Li2Lean.B3.F6Alpha
import Li2Lean.B3.Q2ReferenceLogInput
import Li2Lean.B3.Q2ReferencePackageFacts
import Li2Lean.P0.TubeExteriorBoundary
import Li2Lean.V.EnergyCertI.ISoundEval
import Li2Lean.V.EnergyCertI.ISoundGlueOn

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Part B: generic bridges -/

/-! ### B.0 Log-interval soundness (q-free; `vLogRF` = field chains, `vLogRE` = shards) -/

theorem h6_vLogRF_sound : IV.mem vLogRF (Real.log (3 / 5 : ℝ)) := by
  have hlog := IK.logQ_mem 3 (a := (3, 5)) (by norm_num) (by norm_num)
  rw [vLogRF_eq] at hlog
  simpa [IK.val] using hlog

theorem h6_vLogRE_sound : IV.mem vLogRE (Real.log (3 / 5 : ℝ)) :=
  q2_reference_log_interval_sound

/-! ### B.1 The five ledger witnesses for an arbitrary decoded source -/

/-- The five same-measure `CellSoundnessOn` ledgers consumed by
`v13ReferencePackageInput_of_pinned`. -/
structure V13FiveCells {q : ℕ} {hq : SignedVBaseRange q} (Dr : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw Dr)) (lr : IV) : Prop where
  x : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
    (V.EnergyCertI.fieldUB Dr.data q lr .x)
    (fun t => V.signedVFullFieldX (v13RefMeasure Dr N) (t : ℂ))
  vlo : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
    (V.EnergyCertI.fieldUB Dr.data q lr .vlo)
    (fun t => V.signedVFullFieldV (v13RefMeasure Dr N) (t : ℂ))
  vhi : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
    (V.EnergyCertI.fieldUB Dr.data q lr .vhi)
    (fun t => V.signedVFullFieldV (v13RefMeasure Dr N) (t : ℂ))
  zneg : CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
    (V.EnergyCertI.fieldUB Dr.data q lr .zneg)
    (fun t => V.signedVFullFieldZ (v13RefMeasure Dr N) (t : ℂ))
  zpos : CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
    (V.EnergyCertI.fieldUB Dr.data q lr .zpos)
    (fun t => V.signedVFullFieldZ (v13RefMeasure Dr N) (t : ℂ))

theorem v13_five_cells {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    V13FiveCells Dr N lr :=
  ⟨H6CellGeneric.v13_field_x_cell_on_of_lr Dr hDr N lr,
    H6CellGeneric.v13_field_vlo_cell_on_of_lr Dr hDr N hlr,
    H6CellGeneric.v13_field_vhi_cell_on_of_lr Dr hDr N lr,
    H6CellGeneric.v13_field_zneg_cell_on_of_lr Dr hDr N lr,
    H6CellGeneric.v13_field_zpos_cell_on_of_lr Dr hDr N lr⟩

/-! ### B.2 Finite chains ⟶ `C.x_field`, `C.v_field`

The Boolean checks enter only through `field_lt_of_chain_on` (inside
`H6FieldChainGlue`); the cell witness is the actual full field of the same
measure, at the chain's own log interval `vLogRF`. -/

theorem v13_x_field_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB Dr.data q vLogRF .x) (kxQ q) s = true)
    (hchain : chainOK (1, 250) (1, 1) blocks = true)
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure Dr N) w ≤ (vEx q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure Dr N) (t : ℂ) < (vKx q : ℝ) :=
  v13_field_x_global_of_chain hq
    (H6CellGeneric.v13_field_x_cell_on_of_lr Dr hDr N vLogRF) hwf hcells hchain hend

theorem v13_v_field_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blo bhi : List (List QF)}
    (hwlo : ∀ s ∈ blo, blockWF s = true)
    (hclo : ∀ s ∈ blo, cellsOK (fieldUB Dr.data q vLogRF .vlo) (kvQ q) s = true)
    (hchlo : chainOK (1, 250) (3, 5) blo = true)
    (hwhi : ∀ s ∈ bhi, blockWF s = true)
    (hchi : ∀ s ∈ bhi, cellsOK (fieldUB Dr.data q vLogRF .vhi) (kvQ q) s = true)
    (hchhi : chainOK (3, 5) (1, 1) bhi = true)
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure Dr N) w ≤ (vEv q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure Dr N) (t : ℂ) < (vKv q : ℝ) :=
  v13_field_v_global_of_chain hq
    (H6CellGeneric.v13_field_vlo_cell_on_of_lr Dr hDr N h6_vLogRF_sound)
    (H6CellGeneric.v13_field_vhi_cell_on_of_lr Dr hDr N vLogRF)
    hwlo hclo hchlo hwhi hchi hchhi hend

/-! ### B.3 Finite chains + arcs ⟶ `C.z_field` -/

theorem v13_zneg_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB Dr.data q vLogRF .zneg) (kzQ q) s = true)
    (hchain : chainOK (-(q : ℤ), 1) (-3, 5) blocks = true) :
    ∀ t : ℝ, -(q : ℝ) ≤ t → t ≤ -(3 / 5 : ℝ) →
      V.signedVFullFieldZ (v13RefMeasure Dr N) (t : ℂ) < (vKz q : ℝ) := by
  intro t h1 h2
  have hlo : IK.val ((-(q : ℤ), 1) : QF) = -(q : ℝ) := by simp [IK.val]
  have hhi : -(3 / 5 : ℝ) = IK.val ((-3, 5) : QF) := by norm_num [IK.val]
  exact v13_field_zneg_chain hq (H6CellGeneric.v13_field_zneg_cell_on_of_lr Dr hDr N vLogRF)
    hwf hcells hchain t (le_trans (le_of_eq hlo) h1) (le_trans h2 (le_of_eq hhi))

theorem v13_zpos_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB Dr.data q vLogRF .zpos) (kzQ q) s = true)
    (hchain : chainOK (3, 5) (1, 1) blocks = true) :
    ∀ t : ℝ, (3 / 5 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldZ (v13RefMeasure Dr N) (t : ℂ) < (vKz q : ℝ) := by
  intro t h1 h2
  have hlo : IK.val ((3, 5) : QF) = (3 / 5 : ℝ) := by norm_num [IK.val]
  have hhi : (1 : ℝ) = IK.val ((1, 1) : QF) := by norm_num [IK.val]
  exact v13_field_zpos_chain hq (H6CellGeneric.v13_field_zpos_cell_on_of_lr Dr hDr N vLogRF)
    hwf hcells hchain t (le_trans (le_of_eq hlo) h1) (le_trans h2 (le_of_eq hhi))

theorem v13_arc1_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB Dr.data q vLogRF .arc1) (kzQ q) s = true)
    (hchain : chainOK (0, 1) (1, 1) blocks = true) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 1 s) < (vKz q : ℝ) := by
  have hcell := v13_field_arc_cell_on Dr hDr N 1 (Or.inl rfl) h6_vLogRF_sound
  rw [if_pos (rfl : (1 : ℕ) = 1)] at hcell
  have h := field_lt_of_chain_on
    (f := fun s : ℝ => V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 1 s))
    (ub := fieldUB Dr.data q vLogRF .arc1) (K := kzQ q)
    (lo := (0, 1)) (hi := (1, 1)) (kzQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro s hs
  have h0 : IK.val ((0, 1) : QF) = (0 : ℝ) := by norm_num [IK.val]
  have h1 : (1 : ℝ) = IK.val ((1, 1) : QF) := by norm_num [IK.val]
  have hs' := h s (le_trans (le_of_eq h0) hs.1) (le_trans hs.2 (le_of_eq h1))
  rwa [val_kzQ_eq_vKz hq] at hs'

theorem v13_arc2_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB Dr.data q vLogRF .arc2) (kzQ q) s = true)
    (hchain : chainOK (0, 1) (1, 1) blocks = true) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 2 s) < (vKz q : ℝ) := by
  have hcell := v13_field_arc_cell_on Dr hDr N 2 (Or.inr rfl) h6_vLogRF_sound
  rw [if_neg (by decide : (2 : ℕ) ≠ 1)] at hcell
  have h := field_lt_of_chain_on
    (f := fun s : ℝ => V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 2 s))
    (ub := fieldUB Dr.data q vLogRF .arc2) (K := kzQ q)
    (lo := (0, 1)) (hi := (1, 1)) (kzQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro s hs
  have h0 : IK.val ((0, 1) : QF) = (0 : ℝ) := by norm_num [IK.val]
  have h1 : (1 : ℝ) = IK.val ((1, 1) : QF) := by norm_num [IK.val]
  have hs' := h s (le_trans (le_of_eq h0) hs.1) (le_trans hs.2 (le_of_eq h1))
  rwa [val_kzQ_eq_vKz hq] at hs'

/-- Upper semicircle from the two rational quarter parametrisations. -/
theorem v13_upperArc_bound {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw Dr)) {K : ℝ}
    (h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 1 s) < K)
    (h2 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (v13ArcPoint 2 s) < K) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (V.vUpperArc t) < K := by
  intro t ht
  obtain ⟨quarter, hqt, s, hs, heq⟩ := v13_upperArc_cover t ht
  rw [heq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqt
  rcases hqt with rfl | rfl
  · exact h1 s hs
  · exact h2 s hs

/-- Lower semicircle by conjugation invariance of the reference z field. -/
theorem v13_lowerArc_bound {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw Dr)) {K : ℝ}
    (hup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (V.vUpperArc t) < K) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ (v13RefMeasure Dr N) (V.vLowerArc t) < K := by
  intro t ht
  rw [vLowerArc_eq_conj_vUpperArc, signedVFullFieldZ_v13RefMeasure_conj]
  exact hup (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem v13_z_field_of_blocks {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    {bn bp b1 b2 : List (List QF)}
    (hwn : ∀ s ∈ bn, blockWF s = true)
    (hcn : ∀ s ∈ bn, cellsOK (fieldUB Dr.data q vLogRF .zneg) (kzQ q) s = true)
    (hchn : chainOK (-(q : ℤ), 1) (-3, 5) bn = true)
    (hwp : ∀ s ∈ bp, blockWF s = true)
    (hcp : ∀ s ∈ bp, cellsOK (fieldUB Dr.data q vLogRF .zpos) (kzQ q) s = true)
    (hchp : chainOK (3, 5) (1, 1) bp = true)
    (hw1 : ∀ s ∈ b1, blockWF s = true)
    (hc1 : ∀ s ∈ b1, cellsOK (fieldUB Dr.data q vLogRF .arc1) (kzQ q) s = true)
    (hch1 : chainOK (0, 1) (1, 1) b1 = true)
    (hw2 : ∀ s ∈ b2, blockWF s = true)
    (hc2 : ∀ s ∈ b2, cellsOK (fieldUB Dr.data q vLogRF .arc2) (kzQ q) s = true)
    (hch2 : chainOK (0, 1) (1, 1) b2 = true) :
    ∀ w ∈ V.vContourTrace q,
      V.signedVFullFieldZ (v13RefMeasure Dr N) w < (vKz q : ℝ) := by
  have hup := v13_upperArc_bound Dr N
    (v13_arc1_of_blocks Dr hDr N hw1 hc1 hch1) (v13_arc2_of_blocks Dr hDr N hw2 hc2 hch2)
  exact v13_field_z_global hq (v13_zneg_of_blocks Dr hDr N hwn hcn hchn)
    (v13_zpos_of_blocks Dr hDr N hwp hcp hchp) hup (v13_lowerArc_bound Dr N hup)

/-! ### B.4 Generic endpoint certificates (`V13XEndpointCertificate`, `V13VEndpointCertificate`)

Port of `Q4EndpointDisk` (x) and `Q2VEndpointDisk` (v) with the q-specific row
facts replaced by `V13FieldRowFacts` + `V13DecodedRowBounds`.  The evaluator
enclosures `exUB`/`evUB` are matched term by term:
`exUB = 2·jPos xp − (5/4)·log(q−δ) + (3/4)·log δ`,
`evUB = 2·jPos vp + (jNeg zp + pm·log(3/5+δ)) − log(q−δ) + (1/4)·log δ`. -/

/-- `−Σ J_p · primitive(e_p + δ)`: the shifted one-body bound of a chain on `[0,1]`. -/
noncomputable def v13ChainShiftPos (rows : List CP) : ℝ :=
  -(rows.map fun p => IK.val p.J * LogSegment.primitive (IK.val p.e + 1 / 250)).sum

/-- `Σ J_p · primitive(δ − e_p)`: the reflected bound of the z chain on `[-q,-3/5]`. -/
noncomputable def v13ChainShiftNeg (rows : List CP) : ℝ :=
  (rows.map fun p => IK.val p.J * LogSegment.primitive ((1 / 250 : ℝ) - IK.val p.e)).sum

/-- Consecutive cells ordered ⟹ the breakpoint rows are pairwise ordered. -/
theorem v13ChainCellsAux_chain' :
    ∀ (h : ℝ) (rows : List CP), (∀ c ∈ v13ChainCellsAux h rows, c.left ≤ c.right) →
      rows.IsChain (fun p q => IK.val p.e ≤ IK.val q.e)
  | _, [], _ => List.isChain_nil
  | _, [_], _ => List.isChain_singleton _
  | h, c :: d :: rest, H => by
      refine List.IsChain.cons (v13ChainCellsAux_chain' (h + IK.val c.J) (d :: rest) ?_) ?_
      · intro x hx
        exact H x (by simp [v13ChainCellsAux, hx])
      · intro y hy
        simp at hy
        subst y
        exact H ({left := IK.val c.e, right := IK.val d.e, density := h + IK.val c.J} : V13ChainCell)
          (by simp [v13ChainCellsAux])

theorem v13_rows_pairwise_of_cells (rows : List CP)
    (h : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right) :
    rows.Pairwise (fun p q => IK.val p.e ≤ IK.val q.e) := by
  haveI : IsTrans CP (fun p q => IK.val p.e ≤ IK.val q.e) :=
    ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  exact List.isChain_iff_pairwise.mp (v13ChainCellsAux_chain' 0 rows h)

/-- Closed form of `∫ log(x+δ)` against a nonnegative chain on `[0, ∞)`. -/
theorem v13_chain_shift_integral (rows : List CP)
    (hcells : ∀ c ∈ v13ChainCells rows, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density)
    (hjump : (rows.map fun p => IK.val p.J).sum = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure (v13ChainCells rows)) =
      - (rows.map fun p => IK.val p.J * LogSegment.primitive (IK.val p.e + δ)).sum := by
  rw [integral_v13ChainMeasure_log_shift (v13ChainCells rows) δ hδ
    (fun c hc => ⟨(hcells c hc).1, (hcells c hc).2.1⟩) (fun c hc => (hcells c hc).2.2)]
  change ((v13ChainCellsAux 0 rows).map fun c => c.density *
      (LogSegment.primitive (c.right + δ) -
        LogSegment.primitive (c.left + δ))).sum = _
  rw [v13ChainCellsAux_log_primitive_sum]
  have hconst : (rows.map fun p => IK.val p.J *
      LogSegment.primitive (v13ChainRowsLast rows + δ)).sum = 0 := by
    calc
      _ = (rows.map fun p => IK.val p.J).sum *
          LogSegment.primitive (v13ChainRowsLast rows + δ) := by
            simp [List.sum_map_mul_right]
      _ = 0 := by rw [hjump]; simp
  simp only [zero_mul]
  have hsplit := list_sum_mul_sub_const rows
    (LogSegment.primitive (v13ChainRowsLast rows + δ))
    (fun p => LogSegment.primitive (IK.val p.e + δ)) (fun p => IK.val p.J)
  rw [hsplit, hconst]
  ring

/-- One-body endpoint bound for a nonnegative chain supported in `[0,1]`. -/
theorem v13_chain_endpoint_bound_pos (rows : List CP)
    (hcells : ∀ c ∈ v13ChainCells rows, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density)
    (hsupp : ∀ c ∈ v13ChainCells rows, 0 ≤ c.left ∧ c.right ≤ 1)
    (hjump : (rows.map fun p => IK.val p.J).sum = 0)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 250) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure rows) ≤ v13ChainShiftPos rows := by
  let δ : ℝ := 1 / 250
  have hδ : 0 < δ := by norm_num [δ]
  have hInt := integrable_v13DecodedChainMeasure_log_norm_sub_uncond rows w
  have hae_nonneg : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells rows), 0 ≤ x := by
    have hs : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells rows), x ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      exact v13ChainMeasure_outside_Icc _ _ _ hsupp
    filter_upwards [hs] with x hx
    exact hx.1
  have hae_ne : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells rows), w ≠ Complex.ofReal x := by
    by_cases him : w.im = 0
    · have hwreal : w = Complex.ofReal w.re := by
        apply Complex.ext <;> simp [him]
      rw [hwreal, ae_iff]
      have hset : {x : ℝ | ¬ Complex.ofReal w.re ≠ Complex.ofReal x} = {w.re} := by
        ext x
        simp
      rw [hset]
      exact v13ChainMeasure_singleton (v13ChainCells rows) w.re
    · filter_upwards [] with x
      intro heq
      have him' := congrArg Complex.im heq
      exact him (by simpa using him')
  have hshift := integral_chainMeasureComplex_log_norm_sub_le_shift
    (v13ChainCells rows) δ w hδ (by simpa [δ] using hw)
    (fun c hc => ⟨(hcells c hc).1, (hcells c hc).2.1⟩)
    hae_nonneg hae_ne (by simpa [v13DecodedChainMeasure] using hInt)
  calc
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure rows)
        ≤ ∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure (v13ChainCells rows) := by
          simpa [v13DecodedChainMeasure] using hshift
    _ = v13ChainShiftPos rows := by
          rw [v13_chain_shift_integral rows hcells hjump δ hδ]
          simp [v13ChainShiftPos, δ]

/-- One-body endpoint bound for the z chain on `[-q, -3/5]` (reflected shift). -/
theorem v13_chain_endpoint_bound_neg {q : ℕ} (Dr : V13DecodedRows q)
    (hDr : V13FieldRowFacts Dr) (w : ℂ) (hw : ‖w‖ ≤ 1 / 250) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure Dr.data.zp) ≤
      v13ChainShiftNeg Dr.data.zp := by
  let δ : ℝ := 1 / 250
  have hδ : 0 < δ := by norm_num [δ]
  have hsrc := v13DecodedRows_z_source_bounds Dr
  have hInt : Integrable (fun z : ℂ => Real.log ‖w - z‖)
      (v13DecodedChainMeasure Dr.data.zp) :=
    integrable_v13DecodedChainMeasure_log_norm_sub_uncond Dr.data.zp w
  have hsupp_ae : ∀ᵐ x ∂v13ChainMeasure (v13ChainCells Dr.data.zp),
      x ∈ Icc (-(q : ℝ)) (-3 / 5 : ℝ) := by
    rw [ae_iff]
    apply v13ChainMeasure_outside_Icc
    intro c hc
    have h := hsrc c hc
    exact ⟨h.1, by linarith [h.2]⟩
  have hshiftInt : Integrable (fun x : ℝ => Real.log (δ - x))
      (v13ChainMeasure (v13ChainCells Dr.data.zp)) := by
    apply integrable_v13ChainMeasure_of_continuousOn_cells
    intro c hc
    have hcell := hsrc c hc
    have hcontArg : ContinuousOn (fun x : ℝ => δ - x) (Icc c.left c.right) :=
      continuousOn_const.sub continuousOn_id
    have hmapNe : Set.MapsTo (fun x : ℝ => δ - x) (Icc c.left c.right) ({0} : Set ℝ)ᶜ := by
      intro x hx
      have hxupper : x ≤ (-3 / 5 : ℝ) := le_trans hx.2 (by linarith [hcell.2])
      exact ne_of_gt (show δ - x > 0 by linarith)
    exact Real.continuousOn_log.comp hcontArg hmapNe
  let emb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmapInt : Integrable (fun x : ℝ => Real.log ‖w - Complex.ofReal x‖)
      (v13ChainMeasure (v13ChainCells Dr.data.zp)) := by
    have hmap : Integrable (fun z : ℂ => Real.log ‖w - z‖)
        (Measure.map Complex.ofReal (v13ChainMeasure (v13ChainCells Dr.data.zp))) := by
      simpa [v13DecodedChainMeasure, v13ChainMeasureComplex] using hInt
    change Integrable ((fun z : ℂ => Real.log ‖w - z‖) ∘ Complex.ofReal)
      (v13ChainMeasure (v13ChainCells Dr.data.zp))
    exact (emb.integrable_map_iff (g := fun z : ℂ => Real.log ‖w - z‖)).mp hmap
  change (∫ z : ℂ, Real.log ‖w - z‖ ∂
      Measure.map Complex.ofReal (v13ChainMeasure (v13ChainCells Dr.data.zp))) ≤ _
  rw [emb.integral_map]
  calc
    (∫ x : ℝ, Real.log ‖w - Complex.ofReal x‖ ∂v13ChainMeasure (v13ChainCells Dr.data.zp))
        ≤ ∫ x : ℝ, Real.log (δ - x) ∂v13ChainMeasure (v13ChainCells Dr.data.zp) := by
      apply integral_mono_ae hmapInt hshiftInt
      filter_upwards [hsupp_ae] with x hx
      have hxneg : x ≤ 0 := le_trans hx.2 (by norm_num)
      have hnormpos : 0 < ‖w - Complex.ofReal x‖ := by
        have hne : w ≠ Complex.ofReal x := by
          intro heq
          have hn := congrArg norm heq
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hxneg] at hn
          linarith [hx.2]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hnorm : ‖w - Complex.ofReal x‖ ≤ δ - x := by
        calc
          ‖w - Complex.ofReal x‖ ≤ ‖w‖ + ‖Complex.ofReal x‖ := norm_sub_le _ _
          _ = ‖w‖ + |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ = ‖w‖ - x := by rw [abs_of_nonpos hxneg]; ring
          _ ≤ δ - x := by
            have hwδ : ‖w‖ ≤ δ := by simpa [δ] using hw
            linarith
      exact Real.log_le_log hnormpos hnorm
    _ = v13ChainShiftNeg Dr.data.zp := by
      have h := integral_v13Chain_log_sub (δ := δ) Dr.data.zp hDr.z_jump
        (v13_rows_pairwise_of_cells Dr.data.zp (fun c hc => (hDr.z_cells c hc).1))
        (fun c hc => (hDr.z_cells c hc).2)
      rw [h]
      rfl

/-- Poisson part of the z measure on the endpoint disk: `|z| = 3/5` a.e. -/
theorem v13_poisson_endpoint_bound {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 250) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13PoissonMeasure Dr.data.full) ≤
      (v13PoissonMeasure Dr.data.full).real Set.univ * Real.log (3 / 5 + 1 / 250) := by
  let μ := v13PoissonMeasure Dr.data.full
  have hInt : Integrable (fun z : ℂ => Real.log ‖w - z‖) μ :=
    integrable_v13PoissonMeasure_log_norm_sub_complex Dr.data.full w
      (fun c hc => (hDr.full_rows_data c hc).2.2.2.2.2.2.2)
  have hfinite : μ Set.univ ≠ ⊤ := by
    have h := N.finite_z
    change (v13DecodedChainMeasure Dr.data.zp + v13PoissonMeasure Dr.data.full) Set.univ ≠ ⊤
      at h
    rw [Measure.add_apply] at h
    exact (ENNReal.add_ne_top.mp h).2
  letI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hfinite⟩
  have hconst : Integrable (fun _ : ℂ => Real.log (3 / 5 + 1 / 250 : ℝ)) μ :=
    integrable_const _
  have hz_ae : ∀ᵐ z ∂μ, ‖z‖ = (3 / 5 : ℝ) := by
    rw [ae_iff]
    have h := v13GlobalPoissonMeasure_outside_sphere Dr.data.full
    rw [show v13GlobalPoissonRadius = (3 / 5 : ℝ) by rfl] at h
    have hset : {z : ℂ | ¬ ‖z‖ = (3 / 5 : ℝ)} = (Metric.sphere 0 (3 / 5 : ℝ))ᶜ := by
      ext z
      simp [Metric.mem_sphere, dist_zero_right]
    rw [hset]
    exact h
  have hle : ∀ᵐ z ∂μ, Real.log ‖w - z‖ ≤ Real.log (3 / 5 + 1 / 250 : ℝ) := by
    filter_upwards [hz_ae] with z hz
    have hne : w ≠ z := by
      intro heq
      have hn := congrArg norm heq
      rw [hz] at hn
      nlinarith [hw]
    have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hnorm : ‖w - z‖ ≤ (3 / 5 + 1 / 250 : ℝ) := by
      calc
        ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 1 / 250 + 3 / 5 := add_le_add hw (le_of_eq hz)
        _ = 3 / 5 + 1 / 250 := by ring
    exact Real.log_le_log hpos hnorm
  calc
    _ ≤ ∫ _ : ℂ, Real.log (3 / 5 + 1 / 250 : ℝ) ∂μ := integral_mono_ae hInt hconst hle
    _ = μ.real Set.univ * Real.log (3 / 5 + 1 / 250) := by
      rw [integral_const, smul_eq_mul]

/-- Cross-kernel lower bound against a finite measure on `[0,1] ⊂ ℂ`, both orientations. -/
theorem v13_cross_lower {q : ℕ} (hq2 : 2 ≤ q) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hsupp : μ (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0) (w : ℂ) (hw : ‖w‖ ≤ 1 / 250) :
    μ.real Set.univ * Real.log ((q : ℝ) - 1 / 250) ≤
        ∫ t : ℂ, V.vCrossKernel q w t ∂μ ∧
      μ.real Set.univ * Real.log ((q : ℝ) - 1 / 250) ≤
        ∫ t : ℂ, V.vCrossKernel q t w ∂μ := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hcomm : (fun t : ℂ => V.vCrossKernel q t w) = fun t => V.vCrossKernel q w t := by
    funext t
    simp [V.vCrossKernel, mul_comm]
  have hae : ∀ᵐ t ∂μ, t ∈ Complex.ofReal '' Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1,
      (q : ℝ) - 1 / 250 ≤ ‖(q : ℂ) + w * Complex.ofReal x‖ ∧
        ‖(q : ℂ) + w * Complex.ofReal x‖ ≤ (q : ℝ) + 1 := by
    intro x hx
    have hwt : ‖w * Complex.ofReal x‖ ≤ 1 / 250 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      nlinarith [norm_nonneg w, hx.2]
    have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp
    constructor
    · have htri := norm_sub_le ((q : ℂ) + w * Complex.ofReal x) (w * Complex.ofReal x)
      rw [add_sub_cancel_right, hqn] at htri
      linarith
    · have htri := norm_add_le (q : ℂ) (w * Complex.ofReal x)
      rw [hqn] at htri
      linarith
  have hmeas : Measurable (fun t : ℂ => V.vCrossKernel q w t) := by
    unfold V.vCrossKernel
    fun_prop
  have hInt : Integrable (fun t : ℂ => V.vCrossKernel q w t) μ := by
    refine Integrable.mono' (integrable_const (Real.log ((q : ℝ) + 1)))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with t ht
    rcases ht with ⟨x, hx, rfl⟩
    obtain ⟨hlo, hhi⟩ := hpt x hx
    have hone : 1 ≤ ‖(q : ℂ) + w * Complex.ofReal x‖ := by linarith
    have hl0 : 0 ≤ Real.log ‖(q : ℂ) + w * Complex.ofReal x‖ := Real.log_nonneg hone
    unfold V.vCrossKernel
    rw [Real.norm_eq_abs, abs_of_nonneg hl0]
    exact Real.log_le_log (by linarith) hhi
  have hconst : Integrable (fun _ : ℂ => Real.log ((q : ℝ) - 1 / 250)) μ := integrable_const _
  have hlow : ∀ᵐ t ∂μ, Real.log ((q : ℝ) - 1 / 250) ≤ V.vCrossKernel q w t := by
    filter_upwards [hae] with t ht
    rcases ht with ⟨x, hx, rfl⟩
    unfold V.vCrossKernel
    exact Real.log_le_log (by linarith) (hpt x hx).1
  have h1 := integral_mono_ae hconst hInt hlow
  rw [integral_const, smul_eq_mul] at h1
  refine ⟨h1, ?_⟩
  rw [hcomm]
  exact h1

private theorem logQ_q_sub_delta_mem {q : ℕ} (hq2 : 2 ≤ q) :
    IV.mem (logQ fieldMode.ntl (qsub (Int.ofNat q, 1) DELTA)) (Real.log ((q : ℝ) - 1 / 250)) := by
  have hnum : 0 < (qsub (Int.ofNat q, 1) DELTA).1 := by
    simp only [qsub, qneg, qadd, DELTA]
    push_cast
    have hqi : (2 : ℤ) ≤ Int.ofNat q := Int.ofNat_le.mpr hq2
    omega
  have hval : IK.val (qsub (Int.ofNat q, 1) DELTA) = (q : ℝ) - 1 / 250 := by
    simp only [IK.val, qsub, qneg, qadd, DELTA]
    push_cast
    norm_num
    ring
  have hlog : Real.log (IK.val (qsub (Int.ofNat q, 1) DELTA)) =
      Real.log ((q : ℝ) - 1 / 250) := congrArg Real.log hval
  exact IK.mem_of_eq (logQ_mem fieldMode.ntl hnum (by simp [qsub, qneg, qadd, DELTA])) hlog

private theorem logQ_delta_mem :
    IV.mem (logQ fieldMode.ntl DELTA) (Real.log (1 / 250 : ℝ)) :=
  IK.mem_of_eq (logQ_mem fieldMode.ntl (by norm_num [DELTA]) (by norm_num [DELTA]))
    (by norm_num [IK.val, DELTA])

theorem v13_jPos_mem (rows : List CP)
    (hrows : ∀ p ∈ rows, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2) :
    IV.mem (jPos fieldMode rows) (v13ChainShiftPos rows) := by
  unfold jPos v13ChainShiftPos
  apply IK.neg_mem
  apply IK.sumI_map_mem
  intro p hp
  have hrow := hrows p hp
  have heden : 0 < p.e.2 := hrow.2.1
  have hjden : 0 < p.J.2 := hrow.2.2
  have hdden : 0 < DELTA.2 := by norm_num [DELTA]
  have hsden : 0 < (qadd p.e DELTA).2 := by
    simp only [qadd]
    exact Nat.mul_pos heden hdden
  have hsI := V.EnergyCertI.hsI_mem (md := fieldMode) (s := qadd p.e DELTA) hsden
  have hsmul := IK.smulQ_mem hjden hsI
  have hv := IK.val_qadd heden hdden
  have hdelta : IK.val DELTA = (1 / 250 : ℝ) := by norm_num [DELTA, IK.val]
  have hpos : 0 < IK.val p.e + (1 / 250 : ℝ) := by
    have hepos : 0 ≤ IK.val p.e := by
      unfold IK.val
      exact div_nonneg (by exact_mod_cast hrow.1) (by exact_mod_cast heden.le)
    linarith
  have heq : IK.val p.J *
      (IK.val (qadd p.e DELTA) * Real.log |IK.val (qadd p.e DELTA)| -
        IK.val (qadd p.e DELTA)) =
      IK.val p.J * LogSegment.primitive (IK.val p.e + (1 / 250 : ℝ)) := by
    rw [hv, hdelta, LogSegment.primitive, abs_of_pos hpos]
    ring
  exact IK.mem_of_eq hsmul heq

theorem v13_jNeg_mem (rows : List CP) (hrows : ∀ p ∈ rows, 0 < p.e.2 ∧ 0 < p.J.2) :
    IV.mem (jNeg fieldMode rows) (v13ChainShiftNeg rows) := by
  unfold jNeg v13ChainShiftNeg
  apply IK.sumI_map_mem
  intro p hp
  have heden : 0 < p.e.2 := (hrows p hp).1
  have hjden : 0 < p.J.2 := (hrows p hp).2
  have hqeden : 0 < (qneg p.e).2 := by simpa [qneg] using heden
  have hdden : 0 < DELTA.2 := by norm_num [DELTA]
  have hsden : 0 < (qadd (qneg p.e) DELTA).2 := by
    simp only [qadd]
    exact Nat.mul_pos hqeden hdden
  have hsI := V.EnergyCertI.hsI_mem (md := fieldMode) (s := qadd (qneg p.e) DELTA) hsden
  have hsmul := IK.smulQ_mem hjden hsI
  have hv := IK.val_qadd hqeden hdden
  have hnegval : IK.val (qneg p.e) = - IK.val p.e := val_qneg (a := p.e)
  have hdelta : IK.val DELTA = (1 / 250 : ℝ) := by norm_num [DELTA, IK.val]
  have heq : IK.val p.J *
      (IK.val (qadd (qneg p.e) DELTA) * Real.log |IK.val (qadd (qneg p.e) DELTA)| -
        IK.val (qadd (qneg p.e) DELTA)) =
      IK.val p.J * LogSegment.primitive ((1 / 250 : ℝ) - IK.val p.e) := by
    rw [hv, hnegval, hdelta]
    rw [show -IK.val p.e + (1 / 250 : ℝ) = (1 / 250 : ℝ) - IK.val p.e by ring]
    simp only [LogSegment.primitive_eq, Real.log_abs]
  exact IK.mem_of_eq hsmul heq

/-- Generic x endpoint certificate (`V13EndpointDisk.V13XEndpointCertificate`). -/
noncomputable def v13_x_endpoint_certificate {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr)) :
    V13XEndpointCertificate Dr N where
  J := v13ChainShiftPos Dr.data.xp
  x_log_bound w _ hw := by
    change (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure Dr.data.xp) ≤ _
    exact v13_chain_endpoint_bound_pos Dr.data.xp hDr.x_cells hrows.x_full hDr.x_jump w hw
  cross_lower w _ hw := by
    have hs := (v13RefMeasure_supports_of_bounds Dr N (vXLow q) (vVLow q)
      hrows.x_low hrows.x_full hrows.v_low hrows.v_full hrows.z_source).2.2.2.2.1
    letI : IsFiniteMeasure (v13RefMeasure Dr N).μv :=
      ⟨lt_top_iff_ne_top.mpr (v13RefMeasure Dr N).finite_v⟩
    have hm : (v13RefMeasure Dr N).μv.real Set.univ = (5 / 4 : ℝ) := by
      simpa [Measure.real_def] using congrArg ENNReal.toReal (v13RefMeasure Dr N).mass_v
    have h := (v13_cross_lower hq.1 (v13RefMeasure Dr N).μv hs w hw).1
    rwa [hm] at h
  interval_mem := by
    unfold exUB
    have h1 := IK.smulInt_mem 2 (v13_jPos_mem Dr.data.xp hDr.x_rows)
    have h2 : IV.mem (smulQ (-5, 4) (logQ fieldMode.ntl (qsub (Int.ofNat q, 1) DELTA)))
        ((-5 / 4 : ℝ) * Real.log ((q : ℝ) - 1 / 250)) :=
      IK.mem_of_eq (smulQ_mem (by norm_num : 0 < (4 : ℕ)) (logQ_q_sub_delta_mem hq.1))
        (by norm_num [IK.val])
    have h3 : IV.mem (smulQ (3, 4) (logQ fieldMode.ntl DELTA))
        ((3 / 4 : ℝ) * Real.log (1 / 250)) :=
      IK.mem_of_eq (smulQ_mem (by norm_num : 0 < (4 : ℕ)) logQ_delta_mem)
        (by norm_num [IK.val])
    exact IK.mem_of_eq (IK.add_mem (IK.add_mem h1 h2) h3) (by push_cast; ring)

/-- Generic v endpoint certificate (`V13EndpointDisk.V13VEndpointCertificate`).
Per-q inputs: `pm` denominator and the identification of the Poisson mass with `pm`. -/
noncomputable def v13_v_endpoint_certificate {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (hpmden : 0 < Dr.data.pm.2)
    (hpm : (v13PoissonMeasure Dr.data.full).real Set.univ = IK.val Dr.data.pm) :
    V13VEndpointCertificate Dr N where
  V := v13ChainShiftPos Dr.data.vp
  Z := v13ChainShiftNeg Dr.data.zp + IK.val Dr.data.pm * Real.log (3 / 5 + 1 / 250)
  v_log_bound w _ hw := by
    change (∫ z : ℂ, Real.log ‖w - z‖ ∂v13DecodedChainMeasure Dr.data.vp) ≤ _
    exact v13_chain_endpoint_bound_pos Dr.data.vp hDr.v_cells hrows.v_full hDr.v_jump w hw
  z_log_bound w _ hw := by
    change (∫ z : ℂ, Real.log ‖w - z‖ ∂
      (v13DecodedChainMeasure Dr.data.zp + v13PoissonMeasure Dr.data.full)) ≤ _
    rw [integral_add_measure (integrable_v13DecodedChainMeasure_log_norm_sub_uncond _ w)
      (integrable_v13PoissonMeasure_log_norm_sub_complex Dr.data.full w
        (fun c hc => (hDr.full_rows_data c hc).2.2.2.2.2.2.2))]
    have hP := v13_poisson_endpoint_bound Dr hDr N w hw
    rw [hpm] at hP
    exact add_le_add (v13_chain_endpoint_bound_neg Dr hDr w hw) hP
  cross_lower w _ hw := by
    have hs := (v13RefMeasure_supports_of_bounds Dr N (vXLow q) (vVLow q)
      hrows.x_low hrows.x_full hrows.v_low hrows.v_full hrows.z_source).2.2.2.1
    letI : IsFiniteMeasure (v13RefMeasure Dr N).μx :=
      ⟨lt_top_iff_ne_top.mpr (v13RefMeasure Dr N).finite_x⟩
    have hm : (v13RefMeasure Dr N).μx.real Set.univ = (1 : ℝ) := by
      simpa [Measure.real_def] using congrArg ENNReal.toReal (v13RefMeasure Dr N).mass_x
    have h := (v13_cross_lower hq.1 (v13RefMeasure Dr N).μx hs w hw).2
    rw [hm, one_mul] at h
    exact h
  interval_mem := by
    unfold evUB
    have h1 := IK.smulInt_mem 2 (v13_jPos_mem Dr.data.vp hDr.v_rows)
    have hz := v13_jNeg_mem Dr.data.zp hDr.z_rows
    have hlogR : IV.mem (logQ fieldMode.ntl (qadd R DELTA)) (Real.log (3 / 5 + 1 / 250)) :=
      IK.mem_of_eq (logQ_mem fieldMode.ntl (by norm_num [qadd, R, DELTA])
        (by norm_num [qadd, R, DELTA])) (by norm_num [IK.val, qadd, R, DELTA])
    have hp := smulQ_mem hpmden hlogR
    have h4 := IK.neg_mem (logQ_q_sub_delta_mem hq.1)
    have h5 : IV.mem (smulQ (1, 4) (logQ fieldMode.ntl DELTA))
        ((1 / 4 : ℝ) * Real.log (1 / 250)) :=
      IK.mem_of_eq (smulQ_mem (by norm_num : 0 < (4 : ℕ)) logQ_delta_mem)
        (by norm_num [IK.val])
    exact IK.mem_of_eq (IK.add_mem (IK.add_mem (IK.add_mem h1 (IK.add_mem hz hp)) h4) h5)
      (by push_cast; ring)

/-- Generic Poisson mass of decoded rows (helper for q3, where no
`q3ReferenceRaw_poisson_mass` exists in the release). -/
theorem v13PoissonMeasure_univ_eq_sum (rows : List PR)
    (hrows : ∀ r ∈ rows, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonMeasure rows Set.univ =
      (rows.map (fun r => ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w))).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.map_cons, List.sum_cons]
      change (v13PoissonAtom r + v13PoissonMeasure rs) Set.univ = _
      rw [Measure.add_apply, v13PoissonAtom, Measure.smul_apply,
        v13GlobalCirclePoissonMeasure_univ (hrows r (by simp)),
        ih (fun r hr => hrows r (by simp [hr]))]
      simp [smul_eq_mul]

/-! ### B.5 Energy shard ledger -/

theorem V13EnergyRowFacts.of_field {q : ℕ} {Dr : V13DecodedRows q}
    (hDr : V13FieldRowFacts Dr) (hmx : 0 < Dr.data.mx.2) (hmv : 0 < Dr.data.mv.2) :
    V13EnergyRowFacts Dr where
  xp_pos p hp := ⟨(hDr.x_rows p hp).2.2, (hDr.x_rows p hp).2.1⟩
  vp_pos p hp := ⟨(hDr.v_rows p hp).2.1, (hDr.v_rows p hp).2.2⟩
  zp_pos p hp := hDr.z_rows p hp
  pre_pos c hc := ⟨(hDr.pre_rows_data c hc).1, (hDr.pre_rows_data c hc).2.1,
    (hDr.pre_rows_data c hc).2.2.1⟩
  full_pos c hc := ⟨(hDr.full_rows_data c hc).1, (hDr.full_rows_data c hc).2.1,
    (hDr.full_rows_data c hc).2.2.1⟩
  mx_pos := hmx
  mv_pos := hmv

/-- Pairwise Poisson moduli are positive: `|c_i|,|c_j| < 3/5` gives
`|Re(c_i conj c_j)| < 9/25`, so `(9/25 − Re)^2 > 0`.  Finite alternative per q:
`∀ ci ∈ qD.full, ∀ cj ∈ qD.full, 0 < (modsq ci cj).1 ∧ 0 < (modsq ci cj).2 := by decide +kernel`. -/
theorem v13_modsq_pos {q : ℕ} {Dr : V13DecodedRows q} (hDr : V13FieldRowFacts Dr) :
    ∀ ci ∈ Dr.data.full, ∀ cj ∈ Dr.data.full,
      0 < (modsq ci cj).1 ∧ 0 < (modsq ci cj).2 := by
  intro ci hci cj hcj
  obtain ⟨hx, hy, -, -, -, -, hi, -⟩ := hDr.full_rows_data ci hci
  obtain ⟨hx', hy', -, -, -, -, hj, -⟩ := hDr.full_rows_data cj hcj
  have hR2 : 0 < R2.2 := by norm_num [R2]
  have hA : 0 < (qsub R2 (qadd (qmul ci.cx cj.cx) (qmul ci.cy cj.cy))).2 :=
    qsub_den_pos hR2 (qadd_den_pos (Nat.mul_pos hx hx') (Nat.mul_pos hy hy'))
  have hB : 0 < (qsub (qmul ci.cx cj.cy) (qmul ci.cy cj.cx)).2 :=
    qsub_den_pos (Nat.mul_pos hx hy') (Nat.mul_pos hy hx')
  have hden : 0 < (modsq ci cj).2 := by
    unfold modsq
    exact qadd_den_pos (Nat.mul_pos hA hA) (Nat.mul_pos hB hB)
  refine ⟨?_, hden⟩
  set a := IK.val ci.cx
  set b := IK.val ci.cy
  set c := IK.val cj.cx
  set d := IK.val cj.cy
  have hval : IK.val (modsq ci cj) =
      (9 / 25 - (a * c + b * d)) ^ 2 + (a * d - b * c) ^ 2 := by
    unfold modsq
    rw [val_qadd (Nat.mul_pos hA hA) (Nat.mul_pos hB hB), val_qsq_local, val_qsq_local,
      val_qsub hR2 (qadd_den_pos (Nat.mul_pos hx hx') (Nat.mul_pos hy hy')),
      val_qadd (Nat.mul_pos hx hx') (Nat.mul_pos hy hy'),
      val_qsub (Nat.mul_pos hx hy') (Nat.mul_pos hy hx'),
      val_qmul, val_qmul, val_qmul, val_qmul]
    norm_num [R2, IK.val, a, b, c, d]
  have hlag : (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    ring
  have hprod : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) < (9 / 25 : ℝ) ^ 2 := by
    have h1 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    have h2 : 0 ≤ c ^ 2 + d ^ 2 := by positivity
    calc (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≤ (a ^ 2 + b ^ 2) * (3 / 5) ^ 2 :=
          mul_le_mul_of_nonneg_left hj.le h1
      _ < (3 / 5) ^ 2 * (3 / 5) ^ 2 := by nlinarith
      _ = (9 / 25 : ℝ) ^ 2 := by norm_num
  have hdot : a * c + b * d < 9 / 25 := by nlinarith [sq_nonneg (a * d - b * c)]
  have hpos : 0 < IK.val (modsq ci cj) := by
    rw [hval]
    have : 0 < 9 / 25 - (a * c + b * d) := by linarith
    positivity
  exact fst_pos_of_val_pos hden hpos

/-- The single analytic input of the shard ledger (S6-dq): the degree-50 moment
expansion of `D_q` with the alternating (Leibniz) remainder.  True for every decoded
source (positive chains on `[0,1]`, `q ≥ 2`), not a finite check; included in the release. -/
def V13DqSeries {q : ℕ} {hq : SignedVBaseRange q} (Dr : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw Dr)) : Prop :=
  ∃ rho : ℝ, IV.mem (DEncBridge.tailInterval q Dr.data) rho ∧
    V.vCrossInteraction q (v13RefMeasure Dr N).μx (v13RefMeasure Dr N).μv =
      DEncBridge.dSeriesValue q Dr.data + rho

/- OPEN (S6-dq), statement to prove once for all q:
theorem v13_dq_series {q : ℕ} {hq : SignedVBaseRange q} (Dr : V13DecodedRows q)
    (hDr : V13FieldRowFacts Dr) (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (hmx : IK.val Dr.data.mx = 1) (hmv : IK.val Dr.data.mv = 5 / 4) :
    V13DqSeries Dr N
Route: log|q+uv| = log q + Σ_{k≥1} (-1)^{k+1} (uv/q)^k / k on [0,1]^2, Fubini over the two
finite positive chain measures, ∫ u^k dμ = momentValue rows k (summation by parts, ΣJ = 0),
alternating remainder after k = 50 bounded by m_51(x) m_51(v)/(51 q^51) ≤ mx·mv/(51 q^51). -/

theorem v13_energy_shard_fact {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (hmx : 0 < Dr.data.mx.2) (hmv : 0 < Dr.data.mv.2)
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (plan : List (EKind × ℕ × ℕ × Int))
    (hcheck : ∀ e ∈ plan, energyShardOK Dr.data q lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true)
    (hdqplan : ∀ e ∈ plan, e.1 = EKind.dq → e.2.1 = 0 ∧ e.2.2.1 = 1)
    (hseries : V13DqSeries Dr N) :
    EnergyShardSoundnessFact Dr.data q lr plan (vEnergyTerm q Dr.data) := by
  have hE : V13EnergyRowFacts Dr := V13EnergyRowFacts.of_field hDr hmx hmv
  have hmod := v13_modsq_pos hDr
  have hq0 : 0 < q := by have h2 := hq.1; omega
  intro e he
  refine ⟨hcheck e he, ?_⟩
  by_cases hk : e.1 = EKind.dq
  · obtain ⟨h0, h1⟩ := hdqplan e he hk
    obtain ⟨rho, htail, hact⟩ := hseries
    have h := v13_dq_energyShard_mem (lr := lr) Dr N hq0 hmx hmv hE.xp_pos
      (fun p hp => ⟨(hE.vp_pos p hp).2, (hE.vp_pos p hp).1⟩) hact rfl htail
    rw [hk, h0, h1]
    exact h
  · exact v13_energyShard_mem_non_dq Dr hE hlr e.1 e.2.1 e.2.2.1 hk
      (fun ci hci cj hcj =>
        hmod ci (List.mem_of_mem_drop hci) cj (List.mem_of_mem_drop hcj))

/-! ### B.6 Assembly helper: a complete `V13NumericCertificates` from this file's fields
plus the inputs owned by the ball/sigma/total helper (balls, sigma, `V13DqSeries`). -/

noncomputable def h6_numeric_certificates {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (hDr : V13FieldRowFacts Dr)
    (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (Ax Av Az : ℝ) (hAx : 0 ≤ Ax) (hAv : 0 ≤ Av) (hAz : 0 ≤ Az)
    (hxb : VBallBound (v13RefMeasure Dr N).μx Ax)
    (hvb : VBallBound (v13RefMeasure Dr N).μv Av)
    (hzb : VBallBound (v13RefMeasure Dr N).μz Az)
    (hsigma : vSigma q = sigmaBudget Ax Av Az)
    (hlower : ((vQlow q : ℚ) : ℝ) < V.signedVQuadratic (v13RefMeasure Dr N))
    (hxf : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure Dr N) (t : ℂ) < (vKx q : ℝ))
    (hvf : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure Dr N) (t : ℂ) < (vKv q : ℝ))
    (hzf : ∀ w ∈ V.vContourTrace q,
      V.signedVFullFieldZ (v13RefMeasure Dr N) w < (vKz q : ℝ))
    (halpha : vAlpha q ≤ (vQlow q : ℝ) - 3 / 2 * Real.log q -
      (vKx q : ℝ) - 5 / 4 * (vKv q : ℝ) - (vKz q : ℝ))
    (hxe : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure Dr N) w ≤ (vEx q : ℝ))
    (hve : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure Dr N) w ≤ (vEv q : ℝ)) :
    V13NumericCertificates q hq Dr where
  rows := hrows
  normalization := N
  Ax := Ax
  Av := Av
  Az := Az
  Ax_nonneg := hAx
  Av_nonneg := hAv
  Az_nonneg := hAz
  x_ball := hxb
  v_ball := hvb
  z_ball := hzb
  sigma_eq := hsigma
  energy_lower := hlower
  x_field := hxf
  v_field := hvf
  z_field := hzf
  alpha_le := halpha
  x_endpoint_disk := hxe
  v_endpoint_disk := hve
  dual_admissible := signedVReferenceIntegrable_of_ballBound Dr hrows N hAx hAv hAz hxb hvb hzb

/-- Energy lower bound from the shard ledger and the ball-derived total identity
(generic form of `q4_energy_lower_of_shard_and_total`). -/
theorem h6_energy_lower {q : ℕ} {hq : SignedVBaseRange q}
    (Dr : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw Dr)) {lr : IV}
    (plan : List (EKind × ℕ × ℕ × Int))
    (henergy : EnergyShardSoundnessFact Dr.data q lr plan (vEnergyTerm q Dr.data))
    (htotal : EnergyTotalSoundnessFact (v13RefMeasure Dr N) Dr.data plan (vEnergyTerm q Dr.data))
    (htiles : energyPlanTiles Dr.data plan = true)
    (hclaims : claimsGt plan (qlowQ q) = true)
    (hqden : 0 < (qlowQ q).2)
    (hqlow : IK.val (qlowQ q) = (vQlow q : ℝ)) :
    ((vQlow q : ℚ) : ℝ) < V.signedVQuadratic (v13RefMeasure Dr N) := by
  have h := energy_lower_of_plan Dr.data q lr plan (qlowQ q) hqden (vEnergyTerm q Dr.data)
    (V.signedVQuadratic (v13RefMeasure Dr N)) htotal htiles hclaims
    (fun e he => (henergy e he).1) (fun e he => (henergy e he).2)
  rw [hqlow] at h
  exact h


end
end Li2Lean.B3
