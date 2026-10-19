/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ProducerInterfaces
import Mathlib.MeasureTheory.Integral.Layercake

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace Li2Lean.B3

noncomputable section

/-!
The closed-ball form of the B3 ball estimate.  It is obtained by the
decreasing open-ball approximation used at the endpoint of the v13
near/far split (`v-analytic.tex:496-520`).
-/
theorem closedBall_bound_of_ballBound
    {nu : Measure Complex} [IsFiniteMeasure nu] {A : Real}
    (hball : VBallBound nu A) {w : Complex} {t : Real} (ht : 0 < t) :
    (nu (closedBall w t)).toReal <= A * t := by
  let s : Nat -> Set Complex := fun n =>
    ball w (t + 1 / ((n : Real) + 1))
  have hs_eq : (⋂ n : Nat, s n) = closedBall w t := by
    rw [show closedBall w t = ⋂ n : Nat,
        ball w (t + 1 / ((n : Real) + 1)) by
      ext z
      simp only [mem_closedBall, mem_iInter, mem_ball]
      constructor
      · intro hz n
        have hn : (0 : Real) < 1 / ((n : Real) + 1) := by positivity
        linarith
      · intro hz
        by_contra hnot
        have hdist_not : ¬ dist w z <= t := by
          simpa [dist_comm] using hnot
        have hgap : 0 < dist w z - t :=
          sub_pos.mpr (lt_of_not_ge hdist_not)
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (dist w z - t))
        have hn0 : (0 : Real) < n := by
          have hpos : (0 : Real) < 1 / (dist w z - t) := by positivity
          linarith
        have hsmall0 : 1 / ((n : Real) + 1) <= 1 / (n : Real) := by
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
        have hsmall1 : 1 / (n : Real) < dist w z - t := by
          have hh := one_div_lt_one_div_of_lt (a := 1 / (dist w z - t))
            (b := (n : Real)) (by positivity) hn
          simpa [one_div_div] using hh
        have hsmall : 1 / ((n : Real) + 1) < dist w z - t :=
          hsmall0.trans_lt hsmall1
        have hdist : dist z w < t + 1 / ((n : Real) + 1) := hz n
        have hdist' : dist w z < t + 1 / ((n : Real) + 1) := by
          simpa [dist_comm] using hdist
        linarith] 
  have hs_meas : ∀ n, NullMeasurableSet (s n) nu := by
    intro n
    exact measurableSet_ball.nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn
    apply Metric.ball_subset_ball
    have hcast : (m : Real) <= (n : Real) := by exact_mod_cast hmn
    gcongr
  have hfinite : ∃ n, nu (s n) ≠ ∞ := by
    exact ⟨0, measure_ne_top nu (s 0)⟩
  have hlim : Tendsto (fun n => nu (s n)) atTop (𝓝 (nu (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop hs_meas hs_anti hfinite
  have hlim_real : Tendsto (fun n => (nu (s n)).toReal) atTop
      (𝓝 (nu (⋂ n, s n)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top nu (⋂ n, s n))).comp hlim
  have hbound : ∀ n, (nu (s n)).toReal <=
      A * (t + 1 / ((n : Real) + 1)) := by
    intro n
    exact hball w _ (by positivity)
  have hnat : Tendsto (fun n : Nat => (n : Real) + 1) atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => 1 / ((n : Real) + 1)) atTop
      (𝓝 (0 : Real)) := by
    simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp hnat)
  have hright : Tendsto (fun n : Nat => A *
      (t + 1 / ((n : Real) + 1))) atTop (𝓝 (A * t)) := by
    simpa using (tendsto_const_nhds.add hinv).const_mul A
  have hdiff : Tendsto (fun n : Nat =>
      (nu (s n)).toReal - A * (t + 1 / ((n : Real) + 1))) atTop
      (𝓝 ((nu (⋂ n, s n)).toReal - A * t)) :=
    hlim_real.sub hright
  have hdiff_le : ∀ n, (nu (s n)).toReal -
      A * (t + 1 / ((n : Real) + 1)) <= 0 := by
    intro n
    linarith [hbound n]
  have hlimit_le : (nu (⋂ n, s n)).toReal - A * t <= 0 :=
    le_of_tendsto' hdiff hdiff_le
  rw [hs_eq] at hlimit_le
  linarith

end
end Li2Lean.B3

#print axioms Li2Lean.B3.closedBall_bound_of_ballBound
