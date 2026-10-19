/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.S0TC5
import Li2Lean.B3.SmoothedEnergy
import Li2Lean.V.AllMSmoothing

namespace Li2Lean.B3

open scoped BigOperators

/-! A first C6 bridge from the finite-product convention to the translated
circle centres.  The translation is common to both arguments, so it cancels
exactly; this is the finite algebraic step used before the analytic smoothing
estimates in v13 `v-analytic.tex:544-549`. -/
theorem c6_two_c5PairLog_eq_translated_offdiag
    {d : ℕ} (u : Fin d → ℂ) (m : ℕ) :
    2 * V.c5PairLog u =
      ∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m) := by
  have hpair := V.c5_strict_pair_eq_half_odFin u
  rw [hpair]
  unfold Li2Lean.P0.CellBound.LogQ.odFin
  calc
    2 * (1 / 2 * ∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else Real.log ‖u i - u j‖) =
      ∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else Real.log ‖u i - u j‖ := by ring
    _ = ∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, v13LogKernel]
        congr 2
        simp [translatedAtomCenter]

/-! The next C6 step is pointwise: smoothing a pair of distinct translated
centres changes the positive logarithmic kernel in the direction needed by
the v13 upper bound.  Keeping this finite sum separate avoids smuggling in a
measure-normalisation claim. -/
theorem c6_cross_pair_transfer
    {d e m : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) (hm : 0 < m)
    (hneq : ∀ i j,
      translatedAtomCenter (u i) m ≠ translatedAtomCenter (v j) m) :
    (∑ i : Fin d, ∑ j : Fin e,
      v13LogKernel (translatedAtomCenter (u i) m)
        (translatedAtomCenter (v j) m)) ≤
      ∑ i : Fin d, ∑ j : Fin e,
        v13CirclePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) (smoothingEpsilon m) := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  rw [v13LogKernel_eq_neg_realLogKernel, v13CirclePairEnergy_eq_neg]
  exact neg_le_neg (Li2Lean.P0.circlePairEnergy_le_realLogKernel
    (translatedAtomCenter (u i) m) (translatedAtomCenter (v j) m)
    (smoothingEpsilon_pos hm) (hneq i j))

/-! A denominator atom estimate in the same direction.  This is the
pointwise input for the later product-measure averaging; it does not assert
the averaged `c5DenominatorLog` identity. -/
theorem c6_denominator_atom_log_upper
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (theta phi : ℝ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    Real.log ‖(q : ℂ) + translatedAtom x m theta *
        translatedAtom y m phi‖ ≤
      Real.log ‖(q : ℂ) + x * y‖ +
        denominatorLipschitz q *
          (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2) := by
  have h := translatedAtom_denominator_log_transfer hq hm x y theta phi hx hy
  have hupper := (abs_le.mp h).2
  linarith

end Li2Lean.B3

#print axioms Li2Lean.B3.c6_two_c5PairLog_eq_translated_offdiag
#print axioms Li2Lean.B3.c6_cross_pair_transfer
#print axioms Li2Lean.B3.c6_denominator_atom_log_upper
