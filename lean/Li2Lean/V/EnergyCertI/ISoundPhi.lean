/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.ISoundTrans

namespace Li2Lean.V.EnergyCertI

open IK
open Li2Lean.B3

/-! Soundness of the Poisson potentials in the integer energy evaluator.

The hypotheses below are only denominator and row well-formedness facts.  The
real expressions are the concrete `vEnergyA`/`vEnergyPhi*` definitions from
`V13ReferenceEnergyTerm`; no free evaluator or free term function is used.
-/

private theorem val_qabs {a : IK.QF} (ha : 0 < a.2) :
    val (qabs a) = |val a| := by
  have hden : (0 : ℝ) < a.2 := by exact_mod_cast ha
  have hnum : (Int.ofNat a.1.natAbs : ℝ) = |(a.1 : ℝ)| := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) (Int.natCast_natAbs a.1)
    simpa [Int.cast_abs] using h
  unfold val qabs
  rw [abs_div, abs_of_pos hden, hnum]

private theorem qsq_den_pos {a : IK.QF} (ha : 0 < a.2) : 0 < (qsq a).2 := by
  simp only [qsq, qmul]
  exact Nat.mul_pos ha ha

private theorem qadd_sq_den_pos {a b : IK.QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (qadd (qsq a) (qsq b)).2 := by
  exact Nat.mul_pos (qsq_den_pos ha) (qsq_den_pos hb)

private theorem qadd_sq_num_pos {a b : IK.QF} (ha : 0 < a.2) (hb : 0 < b.2)
    (hne : a.1 ≠ 0 ∨ b.1 ≠ 0) : 0 < (qadd (qsq a) (qsq b)).1 := by
  unfold qadd qsq qmul
  have hda : (0 : ℤ) < Int.ofNat (a.2 * a.2) := by
    simpa only [Int.ofNat_eq_coe] using (Int.natCast_pos.mpr (Nat.mul_pos ha ha))
  have hdb : (0 : ℤ) < Int.ofNat (b.2 * b.2) := by
    simpa only [Int.ofNat_eq_coe] using (Int.natCast_pos.mpr (Nat.mul_pos hb hb))
  change 0 < (a.1 * a.1) * Int.ofNat (b.2 * b.2) +
    (b.1 * b.1) * Int.ofNat (a.2 * a.2)
  rcases hne with hne | hne
  · have hs : 0 < a.1 * a.1 := mul_self_pos.mpr hne
    have ht : 0 ≤ b.1 * b.1 := mul_self_nonneg _
    exact add_pos_of_pos_of_nonneg (mul_pos hs hdb) (mul_nonneg ht hda.le)
  · have hs : 0 ≤ a.1 * a.1 := mul_self_nonneg _
    have ht : 0 < b.1 * b.1 := mul_self_pos.mpr hne
    exact add_pos_of_nonneg_of_pos (mul_nonneg hs hdb.le) (mul_pos ht hda)

private theorem qdiv_den_pos {a b : IK.QF} (ha : 0 < a.2) (hb : 0 < b.2)
    (hb0 : b.1 ≠ 0) : 0 < (qdiv a b).2 := by
  unfold qdiv
  exact Nat.mul_pos ha (Int.natAbs_pos.mpr hb0)

private theorem val_qhalf {a : IK.QF} (ha : 0 < a.2) :
    val (qhalf a) = val a / 2 := by
  unfold val qhalf
  simp only [Int.ofNat_eq_coe, Nat.cast_mul]
  norm_num
  have h : (a.2 : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [h]

private theorem val_qhalf_qsq {a : IK.QF} (ha : 0 < a.2) :
    val (qhalf (qsq a)) = (val a) ^ 2 / 2 := by
  rw [val_qhalf (qsq_den_pos ha)]
  change val (qmul a a) / 2 = _
  rw [val_qmul]
  ring

private theorem val_qadd_sq {a b : IK.QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    val (qadd (qsq a) (qsq b)) = (val a) ^ 2 + (val b) ^ 2 := by
  rw [val_qadd (qsq_den_pos ha) (qsq_den_pos hb)]
  change val (qmul a a) + val (qmul b b) = _
  rw [val_qmul, val_qmul]
  ring

private theorem val_R2 : val R2 = (9 / 25 : ℝ) := by
  norm_num [R2, val]

private theorem hsI_mem (md : Mode) {s : IK.QF} (hs : 0 < s.2) :
    IK.IV.mem (hsI md s) (vEnergyA (val s) 0) := by
  by_cases hzero : s.1 = 0
  · simpa [hsI, vEnergyA, val, hzero] using (IK.zero_mem)
  · have hnat : 0 < s.1.natAbs := Int.natAbs_pos.mpr hzero
    have hnum : 0 < (qabs s).1 := by
      change (0 : ℤ) < Int.ofNat s.1.natAbs
      exact Int.natCast_pos.mpr hnat
    have hqabs : 0 < (qabs s).2 := by simpa [qabs] using hs
    have hlog := IK.logQ_mem md.ntl hnum hqabs
    rw [val_qabs hs] at hlog
    have hterm₁ := IK.smulQ_mem hs hlog
    have hterm₂ : IK.IV.mem (ofQ (qneg s)) (val (qneg s)) :=
      IK.ofQ_mem (by simpa [qneg] using hs)
    have hadd := IK.add_mem hterm₁ hterm₂
    rw [hsI, if_neg hzero]
    have htarget :
        val s * Real.log |val s| + val (qneg s) = vEnergyA (val s) 0 := by
      rw [vEnergyA]
      have hsval0 : val s ≠ 0 := by
        exact div_ne_zero (by exact_mod_cast hzero) (by exact_mod_cast hs.ne')
      simp [hsval0, val_qneg]
      ring
    rw [← htarget]
    exact hadd

theorem aI_mem_phi (md : Mode) {s Y : IK.QF} (hs : 0 < s.2) (hy : 0 < Y.2) :
    IK.IV.mem (aI md s Y) (vEnergyA (val s) (val Y)) := by
  by_cases hy0 : Y.1 = 0
  · have hYval : val Y = 0 := by simp [val, hy0]
    rw [aI, if_pos hy0]
    simpa [hYval] using hsI_mem md hs
  · have hnum : 0 < (qadd (qsq s) (qsq Y)).1 :=
      qadd_sq_num_pos hs hy (Or.inr hy0)
    have hden : 0 < (qadd (qsq s) (qsq Y)).2 := qadd_sq_den_pos hs hy
    have hlog := IK.logQ_mem md.ntl hnum hden
    have hhalf : 0 < (qhalf s).2 := by
      simp only [qhalf]
      exact Nat.mul_pos (by norm_num) hs
    have hterm₁ := IK.smulQ_mem hhalf hlog
    have hterm₂ : IK.IV.mem (ofQ (qneg s)) (val (qneg s)) :=
      IK.ofQ_mem (by simpa [qneg] using hs)
    have hqdiv : 0 < (qdiv s Y).2 := qdiv_den_pos hs hy hy0
    have hatan := IK.atanQ_mem md.nta hqdiv
    have hterm₃ := IK.smulQ_mem hy hatan
    have hadd := IK.add_mem (IK.add_mem hterm₁ hterm₂) hterm₃
    rw [aI, if_neg hy0]
    have hsq : val (qadd (qsq s) (qsq Y)) = (val s) ^ 2 + (val Y) ^ 2 :=
      val_qadd_sq hs hy
    have hdiv : val (qdiv s Y) = val s / val Y := val_qdiv hs hy hy0
    have htarget :
        val (qhalf s) * Real.log (val (qadd (qsq s) (qsq Y))) +
            val (qneg s) + val Y * Real.arctan (val (qdiv s Y)) =
          vEnergyA (val s) (val Y) := by
      rw [vEnergyA, hsq, hdiv, val_qhalf hs, val_qneg]
      have hyval0 : val Y ≠ 0 := by
        exact div_ne_zero (by exact_mod_cast hy0) (by exact_mod_cast hy.ne')
      simp [hyval0]
      ring
    rw [← htarget]
    exact hadd

theorem phiOut_mem (md : Mode) {c : PR} {u : IK.QF}
    (hu : 0 < u.2) (hcx : 0 < c.cx.2) (hcy : 0 < c.cy.2) :
    IK.IV.mem (phiOut md c u) (vEnergyPhiOut c u) := by
  have hsub : 0 < (qsub u c.cx).2 := qsub_den_pos hu hcx
  have h := aI_mem_phi md hsub hcy
  simpa [phiOut, vEnergyPhiOut, val_qsub hu hcx] using h

theorem phiIn_mem (md : Mode) {c : PR} {u : IK.QF} {lr : IK.IV}
    (hu : 0 < u.2) (hcx : 0 < c.cx.2) (hcy : 0 < c.cy.2)
    (hlr : IK.IV.mem lr (Real.log (3 / 5 : ℝ))) :
    IK.IV.mem (phiIn md c u lr) (vEnergyPhiIn c u) := by
  by_cases hzero : c.cx.1 = 0 ∧ c.cy.1 = 0
  · have hcx0 : val c.cx = 0 := by simp [val, hzero.1]
    have hcy0 : val c.cy = 0 := by simp [val, hzero.2]
    rw [phiIn, if_pos hzero]
    simpa [vEnergyPhiIn, hzero, hcx0, hcy0] using IK.smulQ_mem hu hlr
  · have hne : c.cx.1 ≠ 0 ∨ c.cy.1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hzero h
    have hnum : 0 < (qadd (qsq c.cx) (qsq c.cy)).1 :=
      qadd_sq_num_pos hcx hcy hne
    have hden : 0 < (qadd (qsq c.cx) (qsq c.cy)).2 :=
      qadd_sq_den_pos hcx hcy
    have hlog := IK.logQ_mem md.ntl hnum hden
    have hhalf : 0 < (((1, 2) : IK.QF)).2 := by norm_num
    have hlog' := IK.smulQ_mem hhalf hlog
    have hsub := IK.sub_mem hlog' hlr
    have hu' := IK.smulQ_mem hu hsub
    let d : IK.QF := qadd (qsq c.cx) (qsq c.cy)
    have hax : 0 < (qdiv (qmul R2 c.cx) d).2 :=
      qdiv_den_pos (Nat.mul_pos (by norm_num [R2]) hcx) hden (ne_of_gt hnum)
    have hay : 0 < (qdiv (qmul R2 c.cy) d).2 :=
      qdiv_den_pos (Nat.mul_pos (by norm_num [R2]) hcy) hden (ne_of_gt hnum)
    have haxsub : 0 < (qsub u (qdiv (qmul R2 c.cx) d)).2 :=
      qsub_den_pos hu hax
    have ha := aI_mem_phi md haxsub hay
    have hbody := IK.add_mem hu' ha
    rw [phiIn, if_neg hzero]
    have hden' : 0 < d.2 := by simpa [d] using hden
    have hdval : val d = (val c.cx) ^ 2 + (val c.cy) ^ 2 := by
      simpa [d] using (val_qadd_sq hcx hcy)
    have hdivx : val (qdiv (qmul R2 c.cx) d) =
        (9 / 25 : ℝ) * val c.cx / val d := by
      rw [val_qdiv (Nat.mul_pos (by norm_num [R2]) hcx) hden' (ne_of_gt hnum)]
      rw [val_qmul, val_R2]
    have hdivy : val (qdiv (qmul R2 c.cy) d) =
        (9 / 25 : ℝ) * val c.cy / val d := by
      rw [val_qdiv (Nat.mul_pos (by norm_num [R2]) hcy) hden' (ne_of_gt hnum)]
      rw [val_qmul, val_R2]
    have htarget :
        val u * (Real.log (val (qadd (qsq c.cx) (qsq c.cy))) / 2 -
            Real.log (3 / 5 : ℝ)) +
          vEnergyA (val (qsub u (qdiv (qmul R2 c.cx) d)))
            (val (qdiv (qmul R2 c.cy) d)) = vEnergyPhiIn c u := by
      have hvalzero : ¬ (val c.cx = 0 ∧ val c.cy = 0) := by
        intro h
        apply hzero
        constructor
        · have hx : (c.cx.1 : ℝ) = 0 :=
            (div_eq_zero_iff.mp h.1).resolve_right (by exact_mod_cast hcx.ne')
          exact_mod_cast hx
        · have hy : (c.cy.1 : ℝ) = 0 :=
            (div_eq_zero_iff.mp h.2).resolve_right (by exact_mod_cast hcy.ne')
          exact_mod_cast hy
      have hqsub : val (qsub u (qdiv (qmul R2 c.cx) d)) =
          val u - val (qdiv (qmul R2 c.cx) d) := val_qsub hu hax
      rw [vEnergyPhiIn]
      simp only [hvalzero, if_false]
      have hdval' : val (qadd (qsq c.cx) (qsq c.cy)) =
          (val c.cx) ^ 2 + (val c.cy) ^ 2 := by simpa [d] using hdval
      rw [hdval', hqsub, hdivx, hdivy]
      rw [hdval]
      ring
    rw [← htarget]
    simpa [d, val, div_eq_mul_inv, mul_comm] using hbody

theorem phiV_mem (md : Mode) {c : PR} {u : IK.QF} {lr : IK.IV}
    (hu : 0 < u.2) (hcx : 0 < c.cx.2) (hcy : 0 < c.cy.2)
    (hlr : IK.IV.mem lr (Real.log (3 / 5 : ℝ))) :
    IK.IV.mem (phiV md c u lr) (vEnergyPhiV c u) := by
  by_cases hq : qle R u = true
  · rw [phiV, if_pos hq, vEnergyPhiV, if_pos hq]
    exact phiOut_mem md hu hcx hcy
  · have huR : 0 < R.2 := by norm_num [R]
    have hlt : val u < val R := by
      exact lt_of_not_ge ((qle_spec huR hu).not.mp hq)
    have hInU := phiIn_mem md hu hcx hcy hlr
    have hInR := phiIn_mem md huR hcx hcy hlr
    have hOutR := phiOut_mem md huR hcx hcy
    rw [phiV, if_neg hq, vEnergyPhiV, if_neg hq]
    exact IK.add_mem (IK.sub_mem hInU hInR) hOutR

theorem intPoiRow_mem {D : IData} {c : PR} {lr : IK.IV}
    (hz : ∀ p ∈ D.zp, 0 < p.e.2 ∧ 0 < p.J.2)
    (hv : ∀ p ∈ D.vp, 0 < p.e.2 ∧ 0 < p.J.2)
    (hc : 0 < c.cx.2 ∧ 0 < c.cy.2 ∧ 0 < c.w.2)
    (hlr : IK.IV.mem lr (Real.log (3 / 5 : ℝ))) :
    IK.IV.mem (intPoiRow energyMode D.zp D.vp c lr) (vEnergyIntPoiRow D c) := by
  have hzsum : IK.IV.mem (sumI (D.zp.map fun p => smulQ p.J (phiOut energyMode c p.e)))
      ((D.zp.map fun p => val p.J * vEnergyPhiOut c p.e).sum) := by
    apply IK.sumI_map_mem
    intro p hp
    have hp' := hz p hp
    exact IK.smulQ_mem hp'.2 (phiOut_mem energyMode hp'.1 hc.1 hc.2.1)
  have hvsum : IK.IV.mem (sumI (D.vp.map fun p => smulQ p.J (phiV energyMode c p.e lr)))
      ((D.vp.map fun p => val p.J * vEnergyPhiV c p.e).sum) := by
    apply IK.sumI_map_mem
    intro p hp
    have hp' := hv p hp
    exact IK.smulQ_mem hp'.2 (phiV_mem energyMode hp'.1 hc.1 hc.2.1 hlr)
  have hbody := IK.add_mem (IK.smulInt_mem 2 hzsum) hvsum
  have hcoef : 0 < (qneg (qmul (Int.ofNat c.mult, 1) c.w)).2 := by
    simp [qneg, qmul]
    exact hc.2.2
  have hout := IK.smulQ_mem hcoef hbody
  rw [intPoiRow]
  have hvalcoef : val (qneg (qmul (Int.ofNat c.mult, 1) c.w)) =
      -((c.mult : ℝ) * val c.w) := by
    rw [val_qneg, val_qmul]
    simp [val]
  rw [hvalcoef] at hout
  rw [vEnergyIntPoiRow]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hout

/-! A one-row `.intPoi` shard is the exact row term exposed by the
construction-backed `vEnergyTerm` API.  The empty `drop` branch is retained
explicitly, since shard callers may ask for a boundary index. -/
theorem intPoi_term_mem {D : IData} {q : Nat} {lr : IK.IV} (i : Nat)
    (hz : ∀ p ∈ D.zp, 0 < p.e.2 ∧ 0 < p.J.2)
    (hv : ∀ p ∈ D.vp, 0 < p.e.2 ∧ 0 < p.J.2)
    (hp : ∀ p ∈ D.pre, 0 < p.cx.2 ∧ 0 < p.cy.2 ∧ 0 < p.w.2)
    (hlr : IK.IV.mem lr (Real.log (3 / 5 : ℝ))) :
    IK.IV.mem (energyShard D q lr .intPoi i (i + 1))
      (Li2Lean.B3.vEnergyTerm q D .intPoi i) := by
  unfold energyShard
  generalize hrows : D.pre.drop i = rows
  cases rows with
  | nil =>
      simpa [hrows, Li2Lean.B3.vEnergyTerm, sumI] using (IK.zero_mem)
  | cons c rest =>
      have hcdrop : c ∈ D.pre.drop i := by
        rw [hrows]
        simp
      have hc := hp c (List.mem_of_mem_drop hcdrop)
      simpa [hrows, Li2Lean.B3.vEnergyTerm, sumI, IK.add, IK.zero] using
        (intPoiRow_mem hz hv hc hlr)

end Li2Lean.V.EnergyCertI

#print axioms Li2Lean.V.EnergyCertI.aI_mem_phi
#print axioms Li2Lean.V.EnergyCertI.phiOut_mem
#print axioms Li2Lean.V.EnergyCertI.phiV_mem
#print axioms Li2Lean.V.EnergyCertI.intPoiRow_mem
#print axioms Li2Lean.V.EnergyCertI.intPoi_term_mem
