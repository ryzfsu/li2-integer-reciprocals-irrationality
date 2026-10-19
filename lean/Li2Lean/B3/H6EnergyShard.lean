/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Shared H6 E-d shard enclosure layer.

The finite energyShardOK Boolean checks are kept separate from semantic
enclosures. Chain and Poisson rows use elementary interval lemmas from
EnergyE2Rows and ISoundPhi. The dq row is exposed only through the explicit
measure identity, finite degree-50 decomposition, and alternating tail from
DEdBridge.
-/

import Li2Lean.B3.EnergyE2Rows
import Li2Lean.B3.DEdBridge
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.ISoundPhi

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

structure V13EnergyRowFacts {q : ℕ} (R : V13DecodedRows q) : Prop where
  xp_pos : ∀ p ∈ R.data.xp, 0 < p.J.2 ∧ 0 < p.e.2
  vp_pos : ∀ p ∈ R.data.vp, 0 < p.e.2 ∧ 0 < p.J.2
  zp_pos : ∀ p ∈ R.data.zp, 0 < p.e.2 ∧ 0 < p.J.2
  pre_pos : ∀ c ∈ R.data.pre, 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2
  full_pos : ∀ c ∈ R.data.full, 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2
  mx_pos : 0 < R.data.mx.2
  mv_pos : 0 < R.data.mv.2

private theorem gI_mem_vEnergyG (md : Mode) {s : QF} (hs : 0 < s.2) :
    IV.mem (gI md s) (vEnergyG (val s)) := by
  have h := gI_mem md s hs
  by_cases hz : val s = 0
  · simpa [vEnergyG, hz] using h
  · simpa [vEnergyG, hz] using h

theorem selfRow_mem_s6 (md : Mode) (pts : List CP) (k : ℕ)
    (hpts : ∀ p ∈ pts, 0 < p.J.2 ∧ 0 < p.e.2) :
    IV.mem (selfRow md pts k) (vEnergySelfRow pts k) := by
  generalize hdrop : pts.drop k = rows
  cases rows with
  | nil =>
      simpa [selfRow, vEnergySelfRow, hdrop] using (zero_mem : IV.mem zero 0)
  | cons p rest =>
      have hpdrop : p ∈ pts.drop k := by simp [hdrop]
      have hp : p ∈ pts := List.mem_of_mem_drop hpdrop
      have hsum :
          IV.mem (sumI (rest.map fun l =>
              smulQ (qmul (-2, 1) (qmul p.J l.J))
                (gI md (qsub l.e p.e))))
            (rest.map fun l =>
              (-2 : ℝ) * val p.J * val l.J *
                vEnergyG (val l.e - val p.e)).sum := by
        apply sumI_map_mem
        intro l hl
        have hldrop : l ∈ pts.drop k := by
          rw [hdrop]
          simp [hl]
        have hlpts : l ∈ pts := List.mem_of_mem_drop hldrop
        have hpJ := (hpts p hp).1
        have hpE := (hpts p hp).2
        have hlJ := (hpts l hlpts).1
        have hlE := (hpts l hlpts).2
        have hcoeff : 0 < (qmul (-2, 1) (qmul p.J l.J)).2 := by
          simp only [qmul]
          exact Nat.mul_pos (by norm_num) (Nat.mul_pos hpJ hlJ)
        have hsub : val (qsub l.e p.e) = val l.e - val p.e :=
          val_qsub hlE hpE
        have hg := gI_mem_vEnergyG md (s := qsub l.e p.e)
          (qsub_den_pos hlE hpE)
        have hterm := smulQ_mem hcoeff hg
        apply mem_of_eq hterm
        rw [val_qmul, val_qmul, hsub]
        have hc : val ((-2, 1) : QF) = (-2 : ℝ) := by norm_num [val]
        rw [hc]
        ring
      simp only [selfRow, vEnergySelfRow, hdrop]
      simpa [mul_assoc] using hsum

theorem crossRow_mem_s6 (md : Mode) (pts1 pts2 : List CP) (k : ℕ)
    (hpts1 : ∀ p ∈ pts1, 0 < p.J.2 ∧ 0 < p.e.2)
    (hpts2 : ∀ p ∈ pts2, 0 < p.J.2 ∧ 0 < p.e.2) :
    IV.mem (crossRow md pts1 pts2 k) (vEnergyCrossRow pts1 pts2 k) := by
  generalize hdrop : pts1.drop k = rows
  cases rows with
  | nil =>
      simpa [crossRow, vEnergyCrossRow, hdrop] using (zero_mem : IV.mem zero 0)
  | cons p rest =>
      have hpdrop : p ∈ pts1.drop k := by simp [hdrop]
      have hp : p ∈ pts1 := List.mem_of_mem_drop hpdrop
      have hsum :
          IV.mem (sumI (pts2.map fun l =>
              smulQ (qneg (qmul p.J l.J))
                (gI md (qsub p.e l.e))))
            (pts2.map fun l =>
              (-1 : ℝ) * val p.J * val l.J *
                vEnergyG (val p.e - val l.e)).sum := by
        apply sumI_map_mem
        intro l hl
        have hlJ := (hpts2 l hl).1
        have hlE := (hpts2 l hl).2
        have hpJ := (hpts1 p hp).1
        have hpE := (hpts1 p hp).2
        have hcoeff : 0 < (qneg (qmul p.J l.J)).2 := by
          simp only [qneg, qmul]
          exact Nat.mul_pos hpJ hlJ
        have hsub : val (qsub p.e l.e) = val p.e - val l.e :=
          val_qsub hpE hlE
        have hg := gI_mem_vEnergyG md (s := qsub p.e l.e)
          (qsub_den_pos hpE hlE)
        have hterm := smulQ_mem hcoeff hg
        apply mem_of_eq hterm
        rw [val_qneg, val_qmul, hsub]
        ring
      simp only [crossRow, vEnergyCrossRow, hdrop]
      simpa [mul_assoc] using hsum

theorem ppTerm_mem_real_s6 (md : Mode) (ci cj : PR) (lr : IV)
    (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (hnum : 0 < (modsq ci cj).1) (hden : 0 < (modsq ci cj).2) :
    IV.mem (ppTerm md ci cj lr) (vEnergyPpTerm ci cj) := by
  apply mem_of_eq (ppTerm_mem md ci cj lr hlr hnum hden)
  simp only [vEnergyPpTerm, vEnergyPpModSq]
  ring

private theorem forall₂_map_of_pointwise_s6 {α β γ : Type*} (R : β → γ → Prop)
    (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ l, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a tl ih =>
      rw [List.map_cons, List.map_cons]
      exact List.Forall₂.cons (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))

theorem ppRow_mem_s6 (md : Mode) (full : List PR) (i : ℕ) (lr : IV)
    (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (hw : ∀ c ∈ full.drop i, 0 < c.w.2)
    (hmod : ∀ ci ∈ full.drop i, ∀ cj ∈ full.drop i,
      0 < (modsq ci cj).1 ∧ 0 < (modsq ci cj).2) :
    IV.mem (ppRow md full i lr) (vEnergyPpRow full i) := by
  cases hdrop : full.drop i with
  | nil =>
      simp only [ppRow, vEnergyPpRow, hdrop]
      exact zero_mem
  | cons ci rest =>
      simp only [ppRow, vEnergyPpRow, hdrop]
      have hci : ci ∈ full.drop i := by rw [hdrop]; simp
      have hciw := hw ci hci
      have hdiagMod := hmod ci hci ci hci
      have hdiag := ppTerm_mem_real_s6 md ci ci lr hlr hdiagMod.1 hdiagMod.2
      have hdiagCoeff : 0 < (qmul ci.w ci.w).2 := by
        simp only [qmul]
        exact Nat.mul_pos hciw hciw
      have hdiag' := smulQ_mem hdiagCoeff hdiag
      have hfirst : IV.mem (smulQ (qmul ci.w ci.w) (ppTerm md ci ci lr))
          ((val ci.w) ^ 2 * vEnergyPpTerm ci ci) := by
        apply mem_of_eq hdiag'
        rw [val_qmul]
        ring
      have hpoint : ∀ cj ∈ rest,
          IV.mem (smulQ (qmul (2, 1) (qmul ci.w cj.w))
            (ppTerm md ci cj lr))
            (2 * val ci.w * val cj.w * vEnergyPpTerm ci cj) := by
        intro cj hcj
        have hcj' : cj ∈ full.drop i := by rw [hdrop]; simp [hcj]
        have hmod' := hmod ci hci cj hcj'
        have hterm := ppTerm_mem_real_s6 md ci cj lr hlr hmod'.1 hmod'.2
        have hcoeff : 0 < (qmul (2, 1) (qmul ci.w cj.w)).2 := by
          simp only [qmul]
          exact Nat.mul_pos (by norm_num) (Nat.mul_pos hciw (hw cj hcj'))
        have hscaled := smulQ_mem hcoeff hterm
        have hcoeffVal :
            val (qmul (2, 1) (qmul ci.w cj.w)) =
              2 * val ci.w * val cj.w := by
          calc
            val (qmul (2, 1) (qmul ci.w cj.w)) =
                val (2, 1) * val (qmul ci.w cj.w) := val_qmul _ _
            _ = val (2, 1) * (val ci.w * val cj.w) := by rw [val_qmul]
            _ = 2 * val ci.w * val cj.w := by
              rw [show val (2, 1) = (2 : ℝ) by norm_num [val]]
              ring
        apply mem_of_eq hscaled
        rw [hcoeffVal]
      have htail : List.Forall₂ IV.mem
          (rest.map fun cj => smulQ (qmul (2, 1) (qmul ci.w cj.w))
            (ppTerm md ci cj lr))
          (rest.map fun cj => 2 * val ci.w * val cj.w * vEnergyPpTerm ci cj) :=
        forall₂_map_of_pointwise_s6 IV.mem rest
          (fun cj => smulQ (qmul (2, 1) (qmul ci.w cj.w))
            (ppTerm md ci cj lr))
          (fun cj => 2 * val ci.w * val cj.w * vEnergyPpTerm ci cj) hpoint
      have hrow := sumI_mem (List.Forall₂.cons hfirst htail)
      simpa [List.sum_cons] using hrow

private def rowAt_s6 {α β : Type*} [Zero β] (l : List α) (f : α → β) (i : ℕ) : β :=
  match l.drop i with
  | [] => 0
  | a :: _ => f a

private theorem sum_drop_take_map_eq_range'_rowAt_s6
    {α β : Type*} [AddMonoid β] (l : List α) (f : α → β) (i n : ℕ) :
    (((l.drop i).take n).map f).sum =
      ((List.range' i n).map (rowAt_s6 l f)).sum := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      cases h : l.drop i with
      | nil =>
          have hlen : l.length ≤ i := (List.drop_eq_nil_iff.mp h)
          have hi0 : rowAt_s6 l f i = 0 := by simp [rowAt_s6, h]
          have hlater : ∀ j : ℕ, rowAt_s6 l f (i + 1 + j) = 0 := by
            intro j
            have hlen' : l.length ≤ i + 1 + j := by omega
            simp [rowAt_s6, List.drop_eq_nil_of_le hlen']
          rw [List.range'_succ]
          simp only [List.map_cons, List.sum_cons, h, List.take,
            List.map_nil, List.sum_nil, zero_add]
          rw [hi0]
          have htailzero :
              (List.map (rowAt_s6 l f) (List.range' (i + 1) n)).sum = 0 := by
            apply List.sum_eq_zero
            intro x hx
            rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
            rcases (List.mem_range'.mp hj) with ⟨j, hj, rfl⟩
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlater j
          simp [htailzero]
      | cons a rest =>
          have hnext : l.drop (i + 1) = rest := by
            have hh := congrArg (fun xs : List α => xs.drop 1) h
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hh
          rw [List.range'_succ]
          simp only [List.map_cons, List.sum_cons]
          have hi0 : rowAt_s6 l f i = f a := by simp [rowAt_s6, h]
          rw [hi0]
          have hi := ih (i + 1)
          rw [hnext] at hi
          simpa [h, List.take_succ_cons] using congrArg (fun x => f a + x) hi

private def intPoiAt_s6 (D : IData) (i : ℕ) : ℝ :=
  match D.pre.drop i with
  | [] => 0
  | c :: _ => vEnergyIntPoiRow D c

private theorem intPoiAt_s6_eq (q : ℕ) (D : IData) (i : ℕ) :
    intPoiAt_s6 D i = vEnergyTerm q D EKind.intPoi i := by
  rfl

private theorem intPoi_sum_eq_s6 (q : ℕ) (D : IData) (i0 i1 : ℕ) :
    (((D.pre.drop i0).take (i1 - i0)).map (vEnergyIntPoiRow D)).sum =
      ∑ i ∈ Finset.Ico i0 i1, vEnergyTerm q D EKind.intPoi i := by
  calc
    (((D.pre.drop i0).take (i1 - i0)).map (vEnergyIntPoiRow D)).sum =
        ((List.range' i0 (i1 - i0)).map (intPoiAt_s6 D)).sum := by
      have h := sum_drop_take_map_eq_range'_rowAt_s6 D.pre
        (vEnergyIntPoiRow D) i0 (i1 - i0)
      have hroweq : rowAt_s6 D.pre (vEnergyIntPoiRow D) = intPoiAt_s6 D := by
        funext i
        cases hdrop : D.pre.drop i <;> simp [rowAt_s6, intPoiAt_s6, hdrop]
      simpa only [hroweq] using h
    _ = ∑ i ∈ Finset.Ico i0 i1, intPoiAt_s6 D i :=
      listRange'_sum_eq_Ico (intPoiAt_s6 D) i0 i1
    _ = ∑ i ∈ Finset.Ico i0 i1, vEnergyTerm q D EKind.intPoi i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact intPoiAt_s6_eq q D i

theorem v13_energyShard_mem_of_row_mem
    {D : IData} {q : ℕ} {lr : IV} {k : EKind} {i0 i1 : ℕ}
    {row : ℕ → IV} {term : ℕ → ℝ}
    (hrow : ∀ i ∈ List.range' i0 (i1 - i0),
      IV.mem (row i) (term i))
    (heval : energyShard D q lr k i0 i1 =
      sumI ((List.range' i0 (i1 - i0)).map row)) :
    IV.mem (energyShard D q lr k i0 i1)
      (∑ i ∈ Finset.Ico i0 i1, term i) := by
  rw [heval, ← listRange'_sum_eq_Ico]
  exact sumI_map_mem hrow

/-! All non-dq kinds are assembled from the same-source row facts. The
Poisson modulus positivity is deliberately an explicit analytic input: a
positive row weight alone does not imply that a pairwise modulus is nonzero. -/

theorem v13_energyShard_mem_non_dq
    {q : ℕ} (R : V13DecodedRows q) (hE : V13EnergyRowFacts R)
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (k : EKind) (i0 i1 : ℕ) (hk : k ≠ EKind.dq)
    (hmod : ∀ ci ∈ R.data.full.drop i0, ∀ cj ∈ R.data.full.drop i0,
      0 < (modsq ci cj).1 ∧ 0 < (modsq ci cj).2) :
    IV.mem (energyShard R.data q lr k i0 i1)
      (∑ i ∈ Finset.Ico i0 i1, vEnergyTerm q R.data k i) := by
  cases k with
  | selfX =>
      have hrow : ∀ i ∈ List.range' i0 (i1 - i0),
          IV.mem (selfRow energyMode R.data.xp i)
            (vEnergySelfRow R.data.xp i) := by
        intro i hi
        exact selfRow_mem_s6 energyMode R.data.xp i hE.xp_pos
      have heval : energyShard R.data q lr EKind.selfX i0 i1 =
          sumI ((List.range' i0 (i1 - i0)).map
            (selfRow energyMode R.data.xp)) := by
        rfl
      simpa [vEnergyTerm] using
        (v13_energyShard_mem_of_row_mem hrow heval)
  | selfV =>
      have hrow : ∀ i ∈ List.range' i0 (i1 - i0),
          IV.mem (selfRow energyMode R.data.vp i)
            (vEnergySelfRow R.data.vp i) := by
        intro i hi
        have hp : ∀ p ∈ R.data.vp, 0 < p.J.2 ∧ 0 < p.e.2 := by
          intro p hp
          exact ⟨(hE.vp_pos p hp).2, (hE.vp_pos p hp).1⟩
        exact selfRow_mem_s6 energyMode R.data.vp i hp
      have heval : energyShard R.data q lr EKind.selfV i0 i1 =
          sumI ((List.range' i0 (i1 - i0)).map
            (selfRow energyMode R.data.vp)) := by
        rfl
      simpa [vEnergyTerm] using
        (v13_energyShard_mem_of_row_mem hrow heval)
  | selfZ =>
      have hrow : ∀ i ∈ List.range' i0 (i1 - i0),
          IV.mem (selfRow energyMode R.data.zp i)
            (vEnergySelfRow R.data.zp i) := by
        intro i hi
        have hz : ∀ p ∈ R.data.zp, 0 < p.J.2 ∧ 0 < p.e.2 := by
          intro p hp
          exact ⟨(hE.zp_pos p hp).2, (hE.zp_pos p hp).1⟩
        exact selfRow_mem_s6 energyMode R.data.zp i hz
      have heval : energyShard R.data q lr EKind.selfZ i0 i1 =
          sumI ((List.range' i0 (i1 - i0)).map
            (selfRow energyMode R.data.zp)) := by
        rfl
      simpa [vEnergyTerm] using
        (v13_energyShard_mem_of_row_mem hrow heval)
  | crossVZ =>
      have hv : ∀ p ∈ R.data.vp, 0 < p.J.2 ∧ 0 < p.e.2 := by
        intro p hp
        exact ⟨(hE.vp_pos p hp).2, (hE.vp_pos p hp).1⟩
      have hrow : ∀ i ∈ List.range' i0 (i1 - i0),
          IV.mem (crossRow energyMode R.data.vp R.data.zp i)
            (vEnergyCrossRow R.data.vp R.data.zp i) := by
        intro i hi
        have hz : ∀ p ∈ R.data.zp, 0 < p.J.2 ∧ 0 < p.e.2 := by
          intro p hp
          exact ⟨(hE.zp_pos p hp).2, (hE.zp_pos p hp).1⟩
        exact crossRow_mem_s6 energyMode R.data.vp R.data.zp i hv hz
      have heval : energyShard R.data q lr EKind.crossVZ i0 i1 =
          sumI ((List.range' i0 (i1 - i0)).map
            (crossRow energyMode R.data.vp R.data.zp)) := by
        rfl
      simpa [vEnergyTerm] using
        (v13_energyShard_mem_of_row_mem hrow heval)
  | intPoi =>
      have hv : ∀ p ∈ R.data.vp, 0 < p.e.2 ∧ 0 < p.J.2 := hE.vp_pos
      have hrows : IV.mem
          (sumI (((R.data.pre.drop i0).take (i1 - i0)).map
            (intPoiRow energyMode R.data.zp R.data.vp · lr)))
          (((R.data.pre.drop i0).take (i1 - i0)).map
            (vEnergyIntPoiRow R.data)).sum := by
        apply sumI_map_mem
        intro c hc
        have hc' : c ∈ R.data.pre :=
          List.mem_of_mem_drop (List.mem_of_mem_take hc)
        exact intPoiRow_mem hE.zp_pos hv (hE.pre_pos c hc') (by exact hlr)
      have hsum := intPoi_sum_eq_s6 q R.data i0 i1
      simpa [energyShard] using (mem_of_eq hrows hsum)
  | pp =>
      have hrow : ∀ i ∈ List.range' i0 (i1 - i0),
          IV.mem (ppRow energyMode R.data.full i lr)
            (vEnergyPpRow R.data.full i) := by
        intro i hi
        have hi0 : i0 ≤ i := by
          rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
          omega
        have hdrop : R.data.full.drop i =
            (R.data.full.drop i0).drop (i - i0) := by
          rw [List.drop_drop]
          congr 1
          omega
        exact ppRow_mem_s6 energyMode R.data.full i lr hlr
          (fun c hc => (hE.full_pos c (List.mem_of_mem_drop hc)).2.2)
          (by
            intro ci hci cj hcj
            have hci' := hci
            have hcj' := hcj
            rw [hdrop] at hci' hcj'
            exact hmod ci (List.mem_of_mem_drop hci') cj
              (List.mem_of_mem_drop hcj'))
      have heval : energyShard R.data q lr EKind.pp i0 i1 =
          sumI ((List.range' i0 (i1 - i0)).map
            (ppRow energyMode R.data.full · lr)) := by
        rfl
      simpa [vEnergyTerm] using
        (v13_energyShard_mem_of_row_mem hrow heval)
  | dq => exact (hk rfl).elim

theorem v13_dq_energyShard_mem
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    {lr : IV} {Dq rho : ℝ}
    (hqpos : 0 < q)
    (hmx : 0 < R.data.mx.2) (hmv : 0 < R.data.mv.2)
    (hx : ∀ p ∈ R.data.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ R.data.vp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hactual :
      V.vCrossInteraction q (v13RefMeasure R N).μx
        (v13RefMeasure R N).μv = Dq)
    (hDq : Dq = DEncBridge.dSeriesValue q R.data + rho)
    (htail : IV.mem (DEncBridge.tailInterval q R.data) rho) :
    IV.mem (energyShard R.data q lr EKind.dq 0 1)
      (∑ i ∈ Finset.Ico 0 1, vEnergyTerm q R.data EKind.dq i) := by
  have h := DEncBridge.v13_dq_shard_mem_ref
    (q := q) (hq := hq) R N lr hqpos hmx hmv hx hv hactual hDq htail
  simpa [vEnergyTerm] using h

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13_energyShard_mem_of_row_mem
#print axioms Li2Lean.B3.v13_dq_energyShard_mem
