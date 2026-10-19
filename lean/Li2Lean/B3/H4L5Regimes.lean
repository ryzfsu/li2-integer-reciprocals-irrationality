/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.H4ValuationRegimeBridge
import Li2Lean.B3.Q567ArithmeticProofContracts
import Li2Lean.B3.H4OuterPoleBound
import Li2Lean.B3.H4SlabData

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators

/-! The residue and outer regions from v13 `v-arithmetic.tex:128-318`.
The residue region keeps the finite slab table in its predicate; its valuation
bound is supplied by `Q5ResidueProof.sourceDeterminant_gauss_bound`. -/
def v13H4ResidueRegime : V13ResidueRegime := fun n p =>
  max (V.vN n) (V.vU n) < p ^ 2 ∧ p ≤ 5 * n ∧
    ∃ s ∈ v13SlabData,
      s.lo * ((4 * n : ℕ) : ℚ) < p ∧
        (p : ℚ) < s.hi * ((4 * n : ℕ) : ℚ)

def v13H4OuterRegime : V13OuterRegime := fun n p =>
  5 * n < p ∧ p ≤ V.vU n

def v13H4ResidueExponent (n p : ℕ) : ℤ :=
  V.Q5Certificate.q5ResidueExponent (4 * n) p

def v13H4OuterExponent (n p : ℕ) : ℤ :=
  V.Q5Certificate.q5OuterCost n p

/-! This is the exponent used by the actual rational integerizer producer. -/
def v13H4Exponent (q : ℕ) : ℕ → ℕ → ℤ :=
  v13ThreeRegimeExponent q v13H4ResidueRegime v13H4OuterRegime
    v13H4ResidueExponent v13H4OuterExponent

theorem v13H4_residue_gauss_lower {q n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hlarge : max (V.vN n) (V.vU n) < p ^ 2) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -v13H4ResidueExponent n p := by
  rw [V.actualVDeterminant_four_mul]
  exact Q5ResidueProof.sourceDeterminant_gauss_bound n p (-(q : ℤ)) hn hp hlarge

theorem v13H4_regime_data {q : ℕ} (hq : SignedVBaseRange q) :
    V13ValuationRegimeData q v13H4ResidueRegime v13H4OuterRegime
      v13H4ResidueExponent v13H4OuterExponent := by
  constructor
  · intro n p hn hp hdiv hreg
    exact v13H4_residue_gauss_lower hn hp hreg.1
  · intro n p hn hp hdiv hreg
    rw [V.actualVDeterminant_four_mul]
    exact v13_outer_pole_gauss_lower (-(q : ℤ)) hn hp hreg.1 hreg.2

/-! The producer requires this clause for every natural `p`, including
composite values. Above the cutoff all local regimes either contradict their
range conditions or reduce to the zero row-denominator exponent. -/
theorem v13H4Exponent_zero_of_gt_cutoff {q : ℕ}
    (hq : SignedVBaseRange q) :
    ∀ n p : ℕ, 0 < n → V.vU n < p → v13H4Exponent q n p = 0 := by
  intro n p hn hcut
  rcases hq with ⟨hq2, hq7⟩
  dsimp [V.vU] at hcut
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold v13H4Exponent v13ThreeRegimeExponent
  simp only [if_neg hn0]
  by_cases hdiv : p ∣ q * (q + 1)
  · simp only [if_pos hdiv]
    unfold v13ExceptionalExponent v13BaselineExponent
    have hN : V.vN n < p := by
      dsimp [V.vN]
      omega
    have hU : V.vU n < p := hcut
    have hlogN : Nat.log p (V.vN n) = 0 :=
      Nat.log_eq_zero_iff.mpr (Or.inl hN)
    have hlogU : Nat.log p (V.vU n) = 0 :=
      Nat.log_eq_zero_iff.mpr (Or.inl hU)
    have hpq : ¬ p ∣ q := by
      intro hd
      have hp_le : p ≤ q := Nat.le_of_dvd (by omega) hd
      omega
    have hpq1 : ¬ p ∣ q + 1 := by
      intro hd
      have hp_le : p ≤ q + 1 := Nat.le_of_dvd (by omega) hd
      omega
    simp [hlogN, hlogU, padicValNat.eq_zero_of_not_dvd hpq,
      padicValNat.eq_zero_of_not_dvd hpq1]
  · simp only [if_neg hdiv]
    by_cases hres : v13H4ResidueRegime n p
    · simp only [if_pos hres]
      rcases hres with ⟨_, hp5, _⟩
      omega
    · simp only [if_neg hres]
      by_cases hout : v13H4OuterRegime n p
      · simp only [if_pos hout]
        exact False.elim (by
          rcases hout with ⟨_, hpU⟩
          exact (Nat.not_lt_of_ge hpU) hcut)
      · simp only [if_neg hout]
        unfold v13BaselineExponent
        have hN : V.vN n < p := by
          dsimp [V.vN]
          omega
        have hU : V.vU n < p := hcut
        have hlogN : Nat.log p (V.vN n) = 0 :=
          Nat.log_eq_zero_iff.mpr (Or.inl hN)
        have hlogU : Nat.log p (V.vU n) = 0 :=
          Nat.log_eq_zero_iff.mpr (Or.inl hU)
        simp [hlogN, hlogU]

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13H4_residue_gauss_lower
#print axioms Li2Lean.B3.v13H4_regime_data
#print axioms Li2Lean.B3.v13H4Exponent_zero_of_gt_cutoff
