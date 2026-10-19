/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ISoundTrans
import Li2Lean.V.EnergyCertI.IEnergyEval

/-!
# Soundness of the elementary v2 energy evaluators

This module closes the first evaluator layer.  It only combines the already
proved integer interval primitives; measure identities and the field/shard
decompositions remain separate obligations.
-/

namespace Li2Lean.V.EnergyCertI

open IK

private theorem val_qabs {s : QF} (hs : 0 < s.2) :
    val (qabs s) = |val s| := by
  change ((s.1.natAbs : ℝ) / (s.2 : ℝ)) =
    |(s.1 : ℝ) / (s.2 : ℝ)|
  rw [natAbs_cast, abs_div]
  have hsR : (0 : ℝ) < (s.2 : ℝ) := by exact_mod_cast hs
  rw [abs_of_pos hsR]

theorem hsI_mem (md : Mode) {s : QF} (hs : 0 < s.2) :
    IV.mem (hsI md s)
      (val s * Real.log |val s| - val s) := by
  by_cases hzero : s.1 = 0
  · have hval : val s = 0 := by simp [val, hzero]
    simpa [hsI, hzero, hval] using (zero_mem : IV.mem zero 0)
  · have hn : 0 < s.1.natAbs := Int.natAbs_pos.mpr (by
      exact hzero)
    have hqpos : 0 < (qabs s).1 := by
      exact Int.natCast_pos.mpr hn
    have hlog : IV.mem (logQ md.ntl (qabs s))
        (Real.log (val (qabs s))) :=
      logQ_mem md.ntl hqpos hs
    have hlog' : IV.mem (logQ md.ntl (qabs s))
        (Real.log |val s|) := by
      exact mem_of_eq hlog (by rw [val_qabs hs])
    have hmul := smulQ_mem hs hlog'
    have hneg := ofQ_mem (a := qneg s) hs
    have hsum := add_mem hmul hneg
    simp only [hsI, if_neg hzero]
    exact mem_of_eq hsum (by
      rw [val_qneg]
      ring)

theorem gI_mem (md : Mode) {s : QF} (hs : 0 < s.2) :
    IV.mem (gI md s)
      (val s ^ 2 / 2 * Real.log |val s| - 3 * val s ^ 2 / 4) := by
  by_cases hzero : s.1 = 0
  · have hval : val s = 0 := by simp [val, hzero]
    simpa [gI, hzero, hval] using (zero_mem : IV.mem zero 0)
  · have hn : 0 < s.1.natAbs := Int.natAbs_pos.mpr (by
      exact hzero)
    have hqpos : 0 < (qabs s).1 := by
      exact Int.natCast_pos.mpr hn
    have hlog : IV.mem (logQ md.ntl (qabs s))
        (Real.log |val s|) := by
      apply mem_of_eq (logQ_mem md.ntl hqpos hs)
      rw [val_qabs hs]
    have hsq : 0 < (qsq s).2 := by
      dsimp [qsq, qmul]
      exact Nat.mul_pos hs hs
    have hhalf : 0 < (qhalf (qsq s)).2 := by
      dsimp [qhalf]
      omega
    have hmul : IV.mem (smulQ (qhalf (qsq s)) (logQ md.ntl (qabs s)))
        (val (qhalf (qsq s)) * Real.log |val s|) := by
      exact smulQ_mem hhalf hlog
    have hconst : IV.mem (ofQ (qneg (qmul (3, 4) (qsq s))))
        (val (qneg (qmul (3, 4) (qsq s)))) := ofQ_mem (by
      dsimp [qneg, qmul, qsq]
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos hs hs))
    have hsum := add_mem hmul hconst
    have hhalfval : val (qhalf (qsq s)) = val s ^ 2 / 2 := by
      unfold qhalf qsq qmul val
      push_cast
      ring_nf
    have hsqval : val (qsq s) = val s ^ 2 := by
      change val (qmul s s) = val s ^ 2
      rw [val_qmul]
      ring_nf
    have hconstval : val (qneg (qmul (3, 4) (qsq s))) =
        -(3 * val s ^ 2 / 4) := by
      rw [val_qneg, val_qmul, hsqval]
      have hval34 : val (3, 4) = (3 : ℝ) / 4 := by norm_num [val]
      rw [hval34]
      ring_nf
    simp only [gI, if_neg hzero]
    exact mem_of_eq hsum (by rw [hhalfval, hconstval]; ring)

private theorem val_qsq {s : QF} : val (qsq s) = val s ^ 2 := by
  change val (qmul s s) = val s ^ 2
  rw [val_qmul]
  ring_nf

theorem aI_mem (md : Mode) {s Y : QF} (hs : 0 < s.2)
    (hY : 0 < Y.2) :
    IV.mem (aI md s Y)
      (val s / 2 * Real.log (val s ^ 2 + val Y ^ 2) - val s +
        val Y * Real.arctan (val s / val Y)) := by
  by_cases hyzero : Y.1 = 0
  · have hvalY : val Y = 0 := by simp [val, hyzero]
    rw [aI, if_pos hyzero]
    apply mem_of_eq (hsI_mem md hs)
    rw [hvalY]
    norm_num
    ring
  · have hYn : Y.1 ≠ 0 := hyzero
    have hYsqden : 0 < (qsq Y).2 := by
      dsimp [qsq, qmul]
      exact Nat.mul_pos hY hY
    have hSsqden : 0 < (qsq s).2 := by
      dsimp [qsq, qmul]
      exact Nat.mul_pos hs hs
    have hsumden : 0 < (qadd (qsq s) (qsq Y)).2 :=
      qadd_den_pos hSsqden hYsqden
    have hvalYne : val Y ≠ 0 := by
      unfold val
      exact div_ne_zero (by exact_mod_cast hYn) (by exact_mod_cast hY.ne')
    have hsqYpos : 0 < val (qsq Y) := by
      rw [val_qsq]
      exact sq_pos_of_ne_zero hvalYne
    have hsqSnonneg : 0 ≤ val (qsq s) := by rw [val_qsq]; positivity
    have hsumval : val (qadd (qsq s) (qsq Y)) = val (qsq s) + val (qsq Y) :=
      val_qadd hSsqden hYsqden
    have hsumpos : 0 < val (qadd (qsq s) (qsq Y)) := by
      rw [hsumval]
      linarith
    have hsumNum : 0 < (qadd (qsq s) (qsq Y)).1 := by
      have hdenR : (0 : ℝ) < ((qadd (qsq s) (qsq Y)).2 : ℝ) := by exact_mod_cast hsumden
      have hpos := (div_pos_iff).1 (show (0 : ℝ) <
        ((qadd (qsq s) (qsq Y)).1 : ℝ) / (qadd (qsq s) (qsq Y)).2 from hsumpos)
      rcases hpos with ⟨hnum, _⟩ | ⟨_, hden⟩
      · exact_mod_cast hnum
      · linarith
    have hlog : IV.mem (logQ md.ntl (qadd (qsq s) (qsq Y)))
        (Real.log (val s ^ 2 + val Y ^ 2)) := by
      apply mem_of_eq (logQ_mem md.ntl hsumNum hsumden)
      rw [val_qadd hSsqden hYsqden, val_qsq, val_qsq]
    have hdivden : 0 < (qdiv s Y).2 := by
      dsimp [qdiv]
      exact Nat.mul_pos hs (Int.natAbs_pos.mpr hYn)
    have hdiv : IV.mem (atanQ md.nta (qdiv s Y))
        (Real.arctan (val s / val Y)) := by
      apply mem_of_eq (atanQ_mem md.nta hdivden)
      rw [val_qdiv hs hY hYn]
    have hhalfden : 0 < (qhalf s).2 := by dsimp [qhalf]; omega
    have hlogmul := smulQ_mem hhalfden hlog
    have hconst := ofQ_mem (a := qneg s) hs
    have hYmul := smulQ_mem hY hdiv
    have hsum := add_mem (add_mem hlogmul hconst) hYmul
    simp only [aI, if_neg hYn]
    exact mem_of_eq hsum (by
      rw [val_qneg]
      have hhalf : val (qhalf s) = val s / 2 := by
        unfold qhalf val
        push_cast
        ring
      rw [hhalf]
      ring)

end Li2Lean.V.EnergyCertI

#print axioms Li2Lean.V.EnergyCertI.gI_mem
#print axioms Li2Lean.V.EnergyCertI.hsI_mem
#print axioms Li2Lean.V.EnergyCertI.aI_mem
