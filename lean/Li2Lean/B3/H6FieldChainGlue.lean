/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

H6-S2 field-chain glue.

The finite cellsOK/chainOK certificates are connected here to the actual
signedVFullField* functions. The endpoint disk is used only on
(0,1/250]; no ball estimate is used as a substitute for a field or sigma
bound. The two circular pieces of vContourTrace remain explicit inputs:
their arc parameterizations and orientation are different from the real
segments and cannot be inferred from a segment chain.
-/

import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.V.EnergyCertI.ISoundGlueOn
import Li2Lean.V.VPath

namespace Li2Lean

noncomputable section

namespace B3

open Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Printed constants and integer-kit constants agree on the base range. -/

private theorem base_range_cases {q : ℕ} (hq : SignedVBaseRange q) :
    q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by
  unfold SignedVBaseRange at hq
  omega

theorem val_kxQ_eq_vKx {q : ℕ} (hq : SignedVBaseRange q) :
    IK.val (kxQ q) = (vKx q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kxQ, vKx, IK.val]

theorem val_kvQ_eq_vKv {q : ℕ} (hq : SignedVBaseRange q) :
    IK.val (kvQ q) = (vKv q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kvQ, vKv, IK.val]

theorem val_kzQ_eq_vKz {q : ℕ} (hq : SignedVBaseRange q) :
    IK.val (kzQ q) = (vKz q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kzQ, vKz, IK.val]

theorem val_exQ_eq_vEx {q : ℕ} (hq : SignedVBaseRange q) :
    IK.val (exQ q) = (vEx q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exQ, vEx, IK.val]

theorem val_evQ_eq_vEv {q : ℕ} (hq : SignedVBaseRange q) :
    IK.val (evQ q) = (vEv q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [evQ, vEv, IK.val]

theorem kxQ_den_pos {q : ℕ} (hq : SignedVBaseRange q) : 0 < (kxQ q).2 := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kxQ]

theorem kvQ_den_pos {q : ℕ} (hq : SignedVBaseRange q) : 0 < (kvQ q).2 := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kvQ]

theorem kzQ_den_pos {q : ℕ} (hq : SignedVBaseRange q) : 0 < (kzQ q).2 := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [kzQ]

theorem vEx_lt_vKx {q : ℕ} (hq : SignedVBaseRange q) :
    (vEx q : ℝ) < (vKx q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [vEx, vKx]

theorem vEv_lt_vKv {q : ℕ} (hq : SignedVBaseRange q) :
    (vEv q : ℝ) < (vKv q : ℝ) := by
  rcases base_range_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [vEv, vKv]

/-! ## Interior chains

Each theorem below is a thin typed adapter around
EnergyCertI.field_lt_of_chain_on. In particular, the cell witness is
still the actual full field for the same measure ν; the Boolean checks only
certify the interval arithmetic.
-/

theorem v13_field_x_chain {q : ℕ} (hq : SignedVBaseRange q)
    {D : IData} {lr : IV} {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (fieldUB D q lr .x)
      (fun t => V.signedVFullFieldX ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .x) (kxQ q) s = true)
    (hchain : chainOK (1, 250) (1, 1) blocks = true) :
    ∀ t, IK.val (1, 250) ≤ t → t ≤ IK.val (1, 1) →
      V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ) := by
  have h := field_lt_of_chain_on
    (f := fun t : ℝ => V.signedVFullFieldX ν (t : ℂ))
    (ub := fieldUB D q lr .x) (K := kxQ q)
    (lo := (1, 250)) (hi := (1, 1)) (kxQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro t htlo hthi
  have ht := h t htlo hthi
  rwa [val_kxQ_eq_vKx hq] at ht

theorem v13_field_vlo_chain {q : ℕ} (hq : SignedVBaseRange q)
    {D : IData} {lr : IV} {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (fieldUB D q lr .vlo)
      (fun t => V.signedVFullFieldV ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .vlo) (kvQ q) s = true)
    (hchain : chainOK (1, 250) (3, 5) blocks = true) :
    ∀ t, IK.val (1, 250) ≤ t → t ≤ IK.val (3, 5) →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
  have h := field_lt_of_chain_on
    (f := fun t : ℝ => V.signedVFullFieldV ν (t : ℂ))
    (ub := fieldUB D q lr .vlo) (K := kvQ q)
    (lo := (1, 250)) (hi := (3, 5)) (kvQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro t htlo hthi
  have ht := h t htlo hthi
  rwa [val_kvQ_eq_vKv hq] at ht

theorem v13_field_vhi_chain {q : ℕ} (hq : SignedVBaseRange q)
    {D : IData} {lr : IV} {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (fieldUB D q lr .vhi)
      (fun t => V.signedVFullFieldV ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .vhi) (kvQ q) s = true)
    (hchain : chainOK (3, 5) (1, 1) blocks = true) :
    ∀ t, IK.val (3, 5) ≤ t → t ≤ IK.val (1, 1) →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
  have h := field_lt_of_chain_on
    (f := fun t : ℝ => V.signedVFullFieldV ν (t : ℂ))
    (ub := fieldUB D q lr .vhi) (K := kvQ q)
    (lo := (3, 5)) (hi := (1, 1)) (kvQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro t htlo hthi
  have ht := h t htlo hthi
  rwa [val_kvQ_eq_vKv hq] at ht

theorem v13_field_zneg_chain {q : ℕ} (hq : SignedVBaseRange q)
    {D : IData} {lr : IV} {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (fieldUB D q lr .zneg)
      (fun t => V.signedVFullFieldZ ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .zneg) (kzQ q) s = true)
    (hchain : chainOK (-(q : ℤ), 1) (-3, 5) blocks = true) :
    ∀ t, IK.val (-(q : ℤ), 1) ≤ t → t ≤ IK.val (-3, 5) →
      V.signedVFullFieldZ ν (t : ℂ) < (vKz q : ℝ) := by
  have h := field_lt_of_chain_on
    (f := fun t : ℝ => V.signedVFullFieldZ ν (t : ℂ))
    (ub := fieldUB D q lr .zneg) (K := kzQ q)
    (lo := (-(q : ℤ), 1)) (hi := (-3, 5)) (kzQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro t htlo hthi
  have ht := h t htlo hthi
  rwa [val_kzQ_eq_vKz hq] at ht

theorem v13_field_zpos_chain {q : ℕ} (hq : SignedVBaseRange q)
    {D : IData} {lr : IV} {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (fieldUB D q lr .zpos)
      (fun t => V.signedVFullFieldZ ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .zpos) (kzQ q) s = true)
    (hchain : chainOK (3, 5) (1, 1) blocks = true) :
    ∀ t, IK.val (3, 5) ≤ t → t ≤ IK.val (1, 1) →
      V.signedVFullFieldZ ν (t : ℂ) < (vKz q : ℝ) := by
  have h := field_lt_of_chain_on
    (f := fun t : ℝ => V.signedVFullFieldZ ν (t : ℂ))
    (ub := fieldUB D q lr .zpos) (K := kzQ q)
    (lo := (3, 5)) (hi := (1, 1)) (kzQ_den_pos hq)
    (fun a b ha hb hloa hbhi hab => hcell a b ha hb hloa hab hbhi)
    (by norm_num) (by norm_num) hwf hcells hchain
  intro t htlo hthi
  have ht := h t htlo hthi
  rwa [val_kzQ_eq_vKz hq] at ht

/-! ## Endpoint bridges for the real fields

The endpoint hypotheses are stated on complex w, exactly as in
VReferenceFacts. The conversion below uses only ‖(t : ℂ)‖ = |t| and
t > 0; it does not use a mass, ball, or sigma bound.
-/

theorem v13_field_x_global
    {q : ℕ} (hq : SignedVBaseRange q) {ν : V.SignedVMeasures}
    (hchain : ∀ t : ℝ, (1 / 250 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX ν w ≤ (vEx q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ) := by
  refine field_lt_Ioc (f := fun t : ℝ => V.signedVFullFieldX ν (t : ℂ))
    (δ := (1 / 250 : ℝ)) (E := (vEx q : ℝ)) (Kr := (vKx q : ℝ))
    (vEx_lt_vKx hq) ?_ hchain
  intro t ht0 htδ
  have hnorm_pos : 0 < ‖(t : ℂ)‖ := by
    simpa [abs_of_pos ht0]
  have hnorm_le : ‖(t : ℂ)‖ ≤ 1 / 250 := by
    simpa [abs_of_pos ht0] using htδ
  simpa using hend (t : ℂ) hnorm_pos hnorm_le

theorem v13_field_v_global
    {q : ℕ} (hq : SignedVBaseRange q) {ν : V.SignedVMeasures}
    (hlo : ∀ t : ℝ, (1 / 250 : ℝ) ≤ t → t ≤ 3 / 5 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ))
    (hhi : ∀ t : ℝ, (3 / 5 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV ν w ≤ (vEv q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
  refine field_lt_Ioc (f := fun t : ℝ => V.signedVFullFieldV ν (t : ℂ))
    (δ := (1 / 250 : ℝ)) (E := (vEv q : ℝ)) (Kr := (vKv q : ℝ))
    (vEv_lt_vKv hq) ?_ ?_
  · intro t ht0 htδ
    have hnorm_pos : 0 < ‖(t : ℂ)‖ := by
      simpa [abs_of_pos ht0]
    have hnorm_le : ‖(t : ℂ)‖ ≤ 1 / 250 := by
      simpa [abs_of_pos ht0] using htδ
    simpa using hend (t : ℂ) hnorm_pos hnorm_le
  · intro t htδ ht1
    by_cases hmid : t ≤ (3 / 5 : ℝ)
    · exact hlo t htδ hmid
    · exact hhi t (le_of_lt (lt_of_not_ge hmid)) ht1

/-! ## The z trace: real segments plus explicit, correctly oriented arcs

vUpperArc runs from angle 0 to pi, while vLowerArc runs from pi to
2*pi (see V/VPath.lean). Both arc bounds are therefore required on the
same parameter interval Icc 0 1; no reversal or segment estimate is
silently applied to an arc.
-/

theorem v13_field_z_global
    {q : ℕ} (hq : SignedVBaseRange q) {ν : V.SignedVMeasures}
    (hneg : ∀ t : ℝ, -(q : ℝ) ≤ t → t ≤ -(3 / 5 : ℝ) →
      V.signedVFullFieldZ ν (t : ℂ) < (vKz q : ℝ))
    (hpos : ∀ t : ℝ, (3 / 5 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldZ ν (t : ℂ) < (vKz q : ℝ))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ ν (V.vUpperArc t) < (vKz q : ℝ))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      V.signedVFullFieldZ ν (V.vLowerArc t) < (vKz q : ℝ)) :
    ∀ w ∈ V.vContourTrace q,
      V.signedVFullFieldZ ν w < (vKz q : ℝ) := by
  intro w hw
  simp only [V.vContourTrace, Set.mem_union, Set.mem_image] at hw
  rcases hw with ⟨t, ht, rfl⟩ | hw
  · let x : ℝ := -(q : ℝ) + ((q : ℝ) - V.vContourRadius) * t
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq.1
    have hr : 0 ≤ (q : ℝ) - V.vContourRadius := by
      norm_num [V.vContourRadius]
      linarith
    have hxlo : -(q : ℝ) ≤ x := by
      dsimp [x]
      nlinarith [ht.1]
    have hxhi : x ≤ -(3 / 5 : ℝ) := by
      dsimp [x, V.vContourRadius]
      nlinarith [ht.2]
    simpa [V.vNegativeSegment, x] using hneg x hxlo hxhi
  · rcases hw with ⟨t, ht, rfl⟩ | hw
    · let x : ℝ := V.vContourRadius + (1 - V.vContourRadius) * t
      have hxlo : (3 / 5 : ℝ) ≤ x := by
        dsimp [x, V.vContourRadius]
        nlinarith [ht.1]
      have hxhi : x ≤ 1 := by
        dsimp [x, V.vContourRadius]
        nlinarith [ht.2]
      simpa [V.vPositiveSegment, x] using hpos x hxlo hxhi
    · rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact hupper t ht
      · exact hlower t ht

/-! Convenience composition for a finite x chain. -/

theorem v13_field_x_global_of_chain
    {q : ℕ} (hq : SignedVBaseRange q) {D : IData} {lr : IV}
    {ν : V.SignedVMeasures}
    (hcell : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (fieldUB D q lr .x)
      (fun t => V.signedVFullFieldX ν (t : ℂ)))
    {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK (fieldUB D q lr .x) (kxQ q) s = true)
    (hchain : chainOK (1, 250) (1, 1) blocks = true)
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX ν w ≤ (vEx q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ) := by
  have hchain' : ∀ t : ℝ, (1 / 250 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ) := by
    intro t htlo hthi
    have ht := v13_field_x_chain hq hcell hwf hcells hchain t
      (by simpa [IK.val] using htlo) (by simpa [IK.val] using hthi)
    exact ht
  apply v13_field_x_global hq (ν := ν)
    hchain'
  exact hend

theorem v13_field_v_global_of_chain
    {q : ℕ} (hq : SignedVBaseRange q) {D : IData} {lr : IV}
    {ν : V.SignedVMeasures}
    (hlo_cell : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (fieldUB D q lr .vlo)
      (fun t => V.signedVFullFieldV ν (t : ℂ)))
    (hhi_cell : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (fieldUB D q lr .vhi)
      (fun t => V.signedVFullFieldV ν (t : ℂ)))
    {blocks_lo blocks_hi : List (List QF)}
    (hwf_lo : ∀ s ∈ blocks_lo, blockWF s = true)
    (hcells_lo : ∀ s ∈ blocks_lo,
      cellsOK (fieldUB D q lr .vlo) (kvQ q) s = true)
    (hchain_lo : chainOK (1, 250) (3, 5) blocks_lo = true)
    (hwf_hi : ∀ s ∈ blocks_hi, blockWF s = true)
    (hcells_hi : ∀ s ∈ blocks_hi,
      cellsOK (fieldUB D q lr .vhi) (kvQ q) s = true)
    (hchain_hi : chainOK (3, 5) (1, 1) blocks_hi = true)
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV ν w ≤ (vEv q : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
  have hlo' : ∀ t : ℝ, (1 / 250 : ℝ) ≤ t → t ≤ 3 / 5 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
    intro t htlo hthi
    exact v13_field_vlo_chain hq hlo_cell hwf_lo hcells_lo hchain_lo t
      (by simpa [IK.val] using htlo) (by simpa [IK.val] using hthi)
  have hhi' : ∀ t : ℝ, (3 / 5 : ℝ) ≤ t → t ≤ 1 →
      V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ) := by
    intro t htlo hthi
    exact v13_field_vhi_chain hq hhi_cell hwf_hi hcells_hi hchain_hi t
      (by simpa [IK.val] using htlo) (by simpa [IK.val] using hthi)
  apply v13_field_v_global hq (ν := ν)
  · exact hlo'
  · exact hhi'
  · exact hend

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13_field_x_chain
#print axioms Li2Lean.B3.v13_field_v_global_of_chain
#print axioms Li2Lean.B3.v13_field_z_global
