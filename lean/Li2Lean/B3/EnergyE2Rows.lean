/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.EnergySoundnessMeasureFacts

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Primitive evaluator enclosures -/

theorem val_qhalf_e2 (s : QF) (hs : 0 < s.2) :
    val (qhalf s) = val s / 2 := by
  unfold val qhalf
  have hd : (s.2 : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

theorem val_qsq_e2 (s : QF) : val (qsq s) = (val s)^2 := by
  unfold qsq
  rw [IK.val_qmul]
  ring

theorem val_qadd_qsq_e2 (s Y : QF) (hs : 0 < s.2) (hY : 0 < Y.2) :
    val (qadd (qsq s) (qsq Y)) = (val s)^2 + (val Y)^2 := by
  have hs2 : 0 < (qsq s).2 := by simpa [qsq, qmul] using Nat.mul_pos hs hs
  have hY2 : 0 < (qsq Y).2 := by simpa [qsq, qmul] using Nat.mul_pos hY hY
  rw [IK.val_qadd hs2 hY2, val_qsq_e2, val_qsq_e2]

theorem val_ne_zero_e2 {a : QF} (ha : 0 < a.2) (han : a.1 ≠ 0) : val a ≠ 0 := by
  unfold val
  have hn : (a.1 : ℝ) ≠ 0 := by exact_mod_cast han
  exact (div_ne_zero hn (by exact_mod_cast ha.ne'))

theorem qabs_val_e2 (s : QF) (hs : 0 < s.2) :
    val (qabs s) = |val s| := by
  change ((s.1.natAbs : ℕ) : ℝ) / (s.2 : ℝ) = |(s.1 : ℝ) / (s.2 : ℝ)|
  have hs2 : 0 < (s.2 : ℝ) := by exact_mod_cast hs
  rw [IK.natAbs_cast, abs_div, abs_of_pos hs2]

theorem qhalf_qsq_val_e2 (s : QF) (hs : 0 < s.2) :
    val (qhalf (qsq s)) = (val s)^2 / 2 := by
  unfold val qhalf qsq qmul
  have hd : (s.2 : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Int.cast_mul, Int.cast_ofNat]
  push_cast
  field_simp

noncomputable def aReal (s Y : QF) : ℝ :=
  if Y.1 = 0 then val s * Real.log |val s| - val s else
    val s / 2 * Real.log ((val s)^2 + (val Y)^2) - val s +
      val Y * Real.arctan (val s / val Y)

theorem hsI_mem (md : Mode) (s : QF) (hs : 0 < s.2) :
    IV.mem (hsI md s) (val s * Real.log |val s| - val s) := by
  unfold hsI
  by_cases hzero : s.1 = 0
  · rw [if_pos hzero]
    have hval : val s = 0 := by simp [val, hzero]
    simpa [hval] using IK.zero_mem
  · rw [if_neg hzero]
    have habs : 0 < (qabs s).1 := by
      change (0 : ℤ) < (s.1.natAbs : ℤ)
      exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr hzero)
    have hqabsden : 0 < (qabs s).2 := by simpa [qabs] using hs
    have hlog := IK.logQ_mem md.ntl habs hqabsden
    have hsmul := IK.smulQ_mem hs hlog
    have hrat := IK.ofQ_mem (a := qneg s) hs
    apply IK.mem_of_eq (IK.add_mem hsmul hrat)
    rw [qabs_val_e2 s hs, IK.val_qneg]
    ring

theorem aI_mem (md : Mode) (s Y : QF) (hs : 0 < s.2) (hY : 0 < Y.2) :
    IV.mem (aI md s Y) (aReal s Y) := by
  unfold aI aReal
  by_cases hY0 : Y.1 = 0
  · simp only [if_pos hY0]
    exact hsI_mem md s hs
  · simp only [if_neg hY0]
    have hs2 : 0 < (qsq s).2 := by simpa [qsq, qmul] using Nat.mul_pos hs hs
    have hY2 : 0 < (qsq Y).2 := by simpa [qsq, qmul] using Nat.mul_pos hY hY
    have hradden : 0 < (qadd (qsq s) (qsq Y)).2 := Nat.mul_pos hs2 hY2
    have hradval := val_qadd_qsq_e2 s Y hs hY
    have hYval : val Y ≠ 0 := val_ne_zero_e2 hY hY0
    have hradpos : 0 < (val s)^2 + (val Y)^2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hYval)
    have hradnum : 0 < (qadd (qsq s) (qsq Y)).1 := by
      have hd : (0 : ℝ) < ((qadd (qsq s) (qsq Y)).2 : ℝ) := by
        exact_mod_cast hradden
      have hdiv : 0 < val (qadd (qsq s) (qsq Y)) := by
        rw [hradval]
        exact hradpos
      change 0 < ((qadd (qsq s) (qsq Y)).1 : ℝ) /
          ((qadd (qsq s) (qsq Y)).2 : ℝ) at hdiv
      have hn := (lt_div_iff₀ hd).mp hdiv
      exact_mod_cast (by simpa using hn)
    have hlog := IK.logQ_mem md.ntl hradnum hradden
    have hcoef : 0 < (qhalf s).2 := by simp [qhalf]; omega
    have hfirst := IK.smulQ_mem hcoef hlog
    have hneg := IK.ofQ_mem (a := qneg s) hs
    have hdivden : 0 < (qdiv s Y).2 := by
      simp only [qdiv]
      exact Nat.mul_pos hs (Int.natAbs_pos.mpr hY0)
    have hatan := IK.atanQ_mem md.nta hdivden
    have hsecond := IK.smulQ_mem hY hatan
    apply IK.mem_of_eq (IK.add_mem (IK.add_mem hfirst hneg) hsecond)
    rw [val_qhalf_e2 s hs, hradval, IK.val_qneg,
      IK.val_qdiv hs hY hY0]
    ring

theorem gI_mem (md : Mode) (s : QF) (hs : 0 < s.2) :
    IV.mem (gI md s) ((val s)^2 / 2 * Real.log |val s| - 3 * (val s)^2 / 4) := by
  unfold gI
  by_cases hzero : s.1 = 0
  · rw [if_pos hzero]
    have hval : val s = 0 := by simp [val, hzero]
    simpa [hval] using IK.zero_mem
  · have habs : 0 < (qabs s).1 := by
      change (0 : ℤ) < (s.1.natAbs : ℤ)
      exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr hzero)
    have hqabsden : 0 < (qabs s).2 := by simpa [qabs] using hs
    have hlog := IK.logQ_mem md.ntl habs hqabsden
    have hcoef : 0 < (qhalf (qsq s)).2 := by
      simp only [qhalf, qsq, qmul]
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos hs hs)
    have hsmul := IK.smulQ_mem hcoef hlog
    have hratden : 0 < (qneg (qmul (3, 4) (qsq s))).2 := by
      simp only [qneg, qmul, qsq]
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos hs hs)
    have hrat := IK.ofQ_mem (a := qneg (qmul (3, 4) (qsq s))) hratden
    have hadd := IK.add_mem hsmul hrat
    rw [if_neg hzero]
    apply IK.mem_of_eq hadd
    rw [qhalf_qsq_val_e2 s hs, qabs_val_e2 s hs, IK.val_qneg]
    rw [IK.val_qmul (a := (3, 4)) (b := qsq s)]
    have hsq : val (qsq s) = val s * val s := by
      simpa [qsq] using (IK.val_qmul (a := s) (b := s))
    rw [hsq]
    have h34 : val (3, 4) = (3 : ℝ) / 4 := by norm_num [val]
    rw [h34]
    ring

theorem phiOut_mem (md : Mode) (c : PR) (u : QF)
    (hu : 0 < u.2) (hcx : 0 < c.cx.2) (hcy : 0 < c.cy.2) :
    IV.mem (phiOut md c u) (aReal (qsub u c.cx) c.cy) := by
  unfold phiOut
  exact aI_mem md (qsub u c.cx) c.cy (qsub_den_pos hu hcx) hcy

theorem ppTerm_mem (md : Mode) (ci cj : PR) (lr : IV)
    (hlr : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (hnum : 0 < (modsq ci cj).1) (hden : 0 < (modsq ci cj).2) :
    IV.mem (ppTerm md ci cj lr)
      (Real.log (val (modsq ci cj)) / 2 - Real.log (3 / 5 : ℝ)) := by
  unfold ppTerm
  have hlog := IK.logQ_mem md.ntl hnum hden
  have hc : 0 < ((1, 2) : QF).2 := by norm_num
  have hs := IK.smulQ_mem hc hlog
  apply IK.mem_of_eq (IK.sub_mem hs hlr)
  have hhalf : val ((1, 2) : QF) = (1 : ℝ) / 2 := by norm_num [val]
  rw [hhalf]
  ring

/-! A row-range sum has the same order as the corresponding `Finset.Ico` sum.
The evaluator uses `List.range'` so that every row is structurally available to
the interval proof; the ledger uses `Finset.Ico` for its analytic statement.
This lemma is the only indexing conversion needed by E2. -/
theorem listRange'_sum_eq_Ico (f : ℕ → ℝ) (i0 i1 : ℕ) :
    ((List.range' i0 (i1 - i0)).map f).sum =
      ∑ i ∈ Finset.Ico i0 i1, f i := by
  rw [Finset.sum_Ico_eq_sum_range]
  induction (i1 - i0) with
  | zero => simp
  | succ n ih =>
      rw [List.range'_concat]
      simp [ih, Finset.sum_range_succ_comm, Nat.add_assoc]
      rw [add_comm]

/-! The E2 combinatorial bridge.  `hrow` is supplied by the primitive
enclosures (`gI_mem`, `phiOut_mem`, `phiV_mem`, `ppTerm_mem`, and `dEnc_mem`).
The equality `heval` is intentionally explicit: it prevents a row proof from
being reused with a differently indexed evaluator. -/
def energyShardWitness_of_row_mem
    {D : IData} {q : ℕ} {lr : IV}
    {k : EKind} {i0 i1 : ℕ} {claim : Int}
    {row : ℕ → IV} {term : ℕ → ℝ}
    (hcheck : energyShardOK D q lr k i0 i1 claim = true)
    (hrow : ∀ i ∈ List.range' i0 (i1 - i0),
      IV.mem (row i) (term i))
    (heval : energyShard D q lr k i0 i1 =
      sumI ((List.range' i0 (i1 - i0)).map row)) :
    EnergyShardWitness D q lr (k, (i0, (i1, claim)))
      (fun _ i => term i) := by
  refine ⟨hcheck, ?_⟩
  change IV.mem (energyShard D q lr k i0 i1) (∑ i ∈ Finset.Ico i0 i1, term i)
  rw [heval]
  rw [← listRange'_sum_eq_Ico]
  exact sumI_map_mem hrow

/-! A version for a term family indexed by the kind.  This is the form used
when assembling all seven EKind cases into one plan. -/
def energyShardWitness_of_kind_row_mem
    {D : IData} {q : ℕ} {lr : IV}
    {k : EKind} {i0 i1 : ℕ} {claim : Int}
    {row : EKind → ℕ → IV} {term : EKind → ℕ → ℝ}
    (hcheck : energyShardOK D q lr k i0 i1 claim = true)
    (hrow : ∀ i ∈ List.range' i0 (i1 - i0),
      IV.mem (row k i) (term k i))
    (heval : energyShard D q lr k i0 i1 =
      sumI ((List.range' i0 (i1 - i0)).map (row k))) :
    EnergyShardWitness D q lr (k, (i0, (i1, claim))) term := by
  refine ⟨hcheck, ?_⟩
  change IV.mem (energyShard D q lr k i0 i1) (∑ i ∈ Finset.Ico i0 i1, term k i)
  rw [heval]
  rw [← listRange'_sum_eq_Ico]
  exact sumI_map_mem (fun i hi => hrow i hi)

end B3

end

end Li2Lean
