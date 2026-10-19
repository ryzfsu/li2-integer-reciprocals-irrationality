/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizerObligationPlan
import Li2Lean.P0.IntegerizationPaidPrimeLimit
import Li2Lean.P0.RateFinite

namespace Li2Lean.P0

noncomputable section

open Filter Topology
open Integerization

/-- Direct finite-domination adapter for the plan rate field.  This is the
minimal interface needed by a q-dependent budget: convergence to a limit at
or below the target, plus the finite prime-sum domination itself. -/
theorem integerizerPlan_rate_of_budget_le
    (cutoff : ℕ → ℕ) (exponent : ℕ → ℕ → ℤ)
    (budget : ℕ → ℝ) (limit target : ℝ)
    (hbudget : Tendsto budget atTop (𝓝 limit)) (hle : limit ≤ target)
    (hfinite : ∀ m : ℕ, 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (cutoff m),
        (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ budget m) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      0 < m → 4 ∣ m →
        (∑ p ∈ Nat.primesLE (cutoff m),
          (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ target + ε := by
  intro ε hε
  have hlt : limit < target + ε := by linarith
  have he := (tendsto_order.mp hbudget).2 (target + ε) hlt
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  refine ⟨M, ?_⟩
  intro m hm hpos h4
  exact le_trans (hfinite m hpos h4) (hM m hm).le

/-- Transfer a finite domination bound for the plan prime-product exponent
sum to its eventual rate field. The denominator witness is linked to the
same finite prime product by `hD`; no convergence statement is used without
that finite domination input. -/
theorem integerizerPlan_rate_of_finite_domination
    (cutoff : ℕ → ℕ) (exponent : ℕ → ℕ → ℤ) (D : ℕ → ℚ)
    (hD : ∀ m : ℕ, 0 < m → 4 ∣ m →
      D m = rationalPrimeProduct (Nat.primesLE (cutoff m)) (exponent m))
    (budget : ℕ → ℝ) (limit target : ℝ)
    (hbudget : Tendsto budget atTop (𝓝 limit)) (hbelow : limit < target)
    (hfinite : ∀ m : ℕ, 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (cutoff m),
        (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ budget m) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      0 < m → 4 ∣ m →
        (∑ p ∈ Nat.primesLE (cutoff m),
          (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ target + ε := by
  have hfiniteD : ∀ m : ℕ, 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ budget m := by
    intro m hm h4
    rw [hD m hm h4, rationalPrimeProduct_log]
    · exact hfinite m hm h4
    · intro p hp
      exact Nat.prime_of_mem_primesLE hp
  obtain ⟨M, hM⟩ := p0Scalar_rate_of_tendsto_paidBudget D budget limit target
    hbudget hbelow hfiniteD
  intro ε hε
  refine ⟨M, ?_⟩
  intro m hm hpos h4
  have hlog := hM m hm hpos h4
  have hEq : Real.log (D m : ℝ) =
      ∑ p ∈ Nat.primesLE (cutoff m),
        (exponent m p : ℝ) * Real.log p := by
    rw [hD m hpos h4, rationalPrimeProduct_log]
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hlog' : (∑ p ∈ Nat.primesLE (cutoff m),
      (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ target := by
    rw [← hEq]
    exact hlog
  exact le_trans hlog' (le_add_of_nonneg_right hε.le)

/-- Convenient specialization for the finite paid profile budget. The
remaining input is exactly the finite domination inequality for the selected
exponent function, together with the vanishing squarefull or wall cost. -/
theorem integerizerPlan_rate_of_finitePaidBudget
    (cutoff : ℕ → ℕ) (exponent : ℕ → ℕ → ℤ) (D : ℕ → ℚ)
    (hD : ∀ m : ℕ, 0 < m → 4 ∣ m →
      D m = rationalPrimeProduct (Nat.primesLE (cutoff m)) (exponent m))
    (smallCost : ℕ → ℝ)
    (hsmall : Tendsto (fun m : ℕ => smallCost m / (m : ℝ) ^ 2)
      atTop (𝓝 0))
    (wallCount : ℕ)
    (hfinite : ∀ m : ℕ, 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (cutoff m),
        (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤
        p0FinitePaidProfileBudget m + smallCost m / (m : ℝ) ^ 2 +
          p0FiniteWallBudget wallCount m) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      0 < m → 4 ∣ m →
        (∑ p ∈ Nat.primesLE (cutoff m),
          (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤
            (248 / 125 : ℝ) + ε := by
  have hbudget : Tendsto
      (fun m : ℕ => p0FinitePaidProfileBudget m +
        smallCost m / (m : ℝ) ^ 2 + p0FiniteWallBudget wallCount m)
      atTop (𝓝 p0FinitePaidRateConstant) :=
    p0FinitePaidBudget_with_error_tendsto smallCost hsmall wallCount
  exact integerizerPlan_rate_of_finite_domination cutoff exponent D hD _
    p0FinitePaidRateConstant (248 / 125 : ℝ) hbudget
    p0FinitePaidRateConstant_lt hfinite

end
end Li2Lean.P0

#print axioms Li2Lean.P0.integerizerPlan_rate_of_finite_domination
#print axioms Li2Lean.P0.integerizerPlan_rate_of_finitePaidBudget

namespace Li2Lean.P0
noncomputable section
open Integerization

theorem p0IntegerizerExponent_eq_moving_add_credit
    (q m p : ℕ) (hq : 3 ≤ q) (hqm : q ^ 2 ≤ m)
    (hp : p.Prime) (hpU : p ≤ formalDivisorCutoff m) :
    p0IntegerizerExponent q m p =
      min (p0RateW m p)
        (((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ)) +
      formalDivisorH m * (padicValNat p (q - 1) : ℤ) -
      (formalDivisorN m : ℤ) * (padicValNat p q : ℤ) := by
  by_cases hex : p ∣ q * (q - 1)
  · have hpq : p ≤ q := by
      rcases hp.dvd_mul.mp hex with hd | hd
      · exact Nat.le_of_dvd (by omega) hd
      · exact (Nat.le_of_dvd (by omega : 0 < q - 1) hd).trans (Nat.sub_le _ _)
    have hpsq : p ^ 2 ≤ p0SquarefullCutoff m := by
      have hpq2 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq 2
      have hqpos : 0 < m := by nlinarith
      unfold p0SquarefullCutoff p0DenominatorU
      omega
    have hW : p0RateW m p =
        (((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ)) := by
      simp [p0RateW, not_lt.mpr hpsq, formalDivisorCutoff, p0DenominatorU]
    simp [p0IntegerizerExponent, p0IntegerizerMovingExponent, hex, hW,
      formalDivisorCredit]
  · have hnotq : ¬ p ∣ q := by intro hd; exact hex (dvd_mul_of_dvd_left hd _)
    have hnotq1 : ¬ p ∣ q - 1 := by intro hd; exact hex (dvd_mul_of_dvd_right hd _)
    have hvq := padicValNat.eq_zero_of_not_dvd hnotq
    have hvq1 := padicValNat.eq_zero_of_not_dvd hnotq1
    simp [p0IntegerizerExponent, p0IntegerizerMovingExponent, hex, hpU,
      formalDivisorCredit, hvq, hvq1, min_comm, min_left_comm]

end
end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open Filter Topology Integerization

/-- The large-prime part of the actual generic plan is bounded by the
already proved, uncredited q=2 profile cost. The omitted squarefull terms
are nonnegative baseline costs. -/
theorem p0Integerizer_nonsquarefull_sum_le_uncredited
    (q m : ℕ) (hq : 3 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m) (hqm : q^2 ≤ m) :
    (∑ p ∈ (Nat.primesLE (p0IntegerizerCutoff q m)).filter
        (fun p => p ∉ p0SquarefullPrimes m),
      (p0IntegerizerExponent q m p : ℝ) * Real.log p) ≤
        p0A2SettledUncreditedPrimeCost m p0RateW := by
  classical
  let S := (Nat.primesLE (p0IntegerizerCutoff q m)).filter
    (fun p => p ∉ p0SquarefullPrimes m)
  let T := (Nat.primesLE (p0DenominatorU m)).filter
    (fun p => p ∉ p0SquarefullPrimes m)
  have hsub : T ⊆ S := by
    intro p hp
    obtain ⟨hpU, hpL⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpL⟩
    obtain ⟨hple, hprime⟩ := Nat.mem_primesLE.mp hpU
    apply Nat.mem_primesLE.mpr
    exact ⟨hple.trans (Nat.le_add_right _ q), hprime⟩
  have heq : (∑ p ∈ T, (p0IntegerizerExponent q m p : ℝ) * Real.log p) =
      ∑ p ∈ S, (p0IntegerizerExponent q m p : ℝ) * Real.log p := by
    apply Finset.sum_subset hsub
    intro p hp hpnot
    have hps := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesLE hps.1
    have hU : ¬ p ≤ formalDivisorCutoff m := by
      intro hle
      exact hpnot (Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle, hprime⟩, hps.2⟩)
    have hex := p0Integerizer_not_exceptional_of_not_squarefull q m p (by omega)
      hm hqm hprime hps.2
    have hq0 : ¬ p ∣ q := fun h => hex (dvd_mul_of_dvd_left h _)
    have hq1 : ¬ p ∣ q-1 := fun h => hex (dvd_mul_of_dvd_right h _)
    have hlog := Nat.log_of_lt (Nat.lt_of_not_ge hU)
    have hz : p0IntegerizerExponent q m p = 0 := by
      simp [p0IntegerizerExponent, p0IntegerizerMovingExponent, hex, hU,
        formalDivisorCredit, hlog, padicValNat.eq_zero_of_not_dvd hq0,
        padicValNat.eq_zero_of_not_dvd hq1]
    simp [hz]
  have hterm : ∀ p ∈ T,
      (p0IntegerizerExponent q m p : ℝ) * Real.log p = p0RateCostTerm m p := by
    intro p hp
    obtain ⟨hpU, hpL⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesLE hpU
    have hple := (Nat.mem_primesLE.mp hpU).1
    have hid := p0IntegerizerExponent_eq_settled_of_not_squarefull q m p (by omega)
      hm hqm hprime hpL hple
    have hp2 : p ≠ 2 := by
      intro he
      apply hpL
      subst p
      apply mem_p0SquarefullPrimes.mpr
      refine ⟨Nat.prime_two, ?_⟩
      have h4m : 4 ≤ m := Nat.le_of_dvd hm h4
      unfold p0SquarefullCutoff p0DenominatorU
      omega
    simp only [hid, p0RateCostTerm, if_neg hp2]
    rfl
  rw [← heq, Finset.sum_congr rfl hterm, p0Rate_cost_eq m hm h4]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp hpnot
  have hprime := Nat.prime_of_mem_primesLE hp
  have hsmall : p ∈ p0SquarefullPrimes m := by
    by_contra hlarge
    exact hpnot (Finset.mem_filter.mpr ⟨hp, hlarge⟩)
  have hs := (mem_p0SquarefullPrimes.mp hsmall).2
  have hW : p0RateW m p = (((3*m*Nat.log p (p0DenominatorU m) : ℕ) : ℤ)) := by
    simp [p0RateW, not_lt.mpr hs]
  unfold p0RateCostTerm
  split
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · rw [hW, min_self, Int.cast_natCast]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))

end
end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open Filter Topology Integerization IntegerizationTables

/-- The base-independent uncredited profile constant is below the relaxed
core rate; the q-dependent credits are kept separate. -/
theorem p0UncreditedProfileConstant_lt :
    p0FinitePaidRateConstant + (13/16 : ℝ) * Real.log 2 < 1273/500 := by
  have ht0 : ((p0FiniteTailIntegral + 3/256 : ℚ) : ℝ) < ((197/10000 : ℚ) : ℝ) := by
    exact_mod_cast p0FiniteTail_total_lt_197_over_10000
  have ht : (p0FiniteTailIntegral : ℝ) + 3/256 < (197/10000 : ℝ) := by
    push_cast at ht0
    exact ht0
  have hn : (p0LowIntegralClaim : ℝ) + 287/192 + 197/10000 < 1273/500 := by
    norm_num [p0LowIntegralClaim]
  unfold p0FinitePaidRateConstant
  linarith

theorem p0UncreditedProfile_rate :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0A2SettledUncreditedPrimeCost m p0RateW / (m : ℝ)^2 ≤ 1273/500 := by
  have hi : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop))
  have hf : Tendsto p0FinitePaidFeatureCost atTop
      (𝓝 ((13/16 : ℝ)*Real.log 2)) := by
    change Tendsto (fun m : ℕ => ((13/16 : ℝ) - 1/(m:ℝ))*Real.log 2)
      atTop (𝓝 ((13/16 : ℝ)*Real.log 2))
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (13/16 : ℝ)) atTop
      (𝓝 (13/16 : ℝ))).sub hi).mul_const (Real.log 2)
  have hb := (p0FinitePaidBudget_with_error_tendsto p0SquarefullPrimeLayerCost
    p0SquarefullPrimeLayerCost_div_sq_tendsto_zero p0RateWallCount).add hf
  have he := (tendsto_order.mp hb).2 (1273/500) p0UncreditedProfileConstant_lt
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  refine ⟨M, ?_⟩
  intro m hm hpos h4
  have hcost := p0A2SettledD_le_paidBudget p0RateW p0RateWallCount p0Rate_finite_profile
    m hpos h4
  rw [p0A2SettledD_logRate_split m hpos h4 p0RateW] at hcost
  have hbnd := hM m hm
  unfold p0FinitePaidFeatureCost at hbnd
  linarith

/-- The actual generic plan prime sum, with its literal exponent witnesses,
has the q-dependent relaxed rate. All finite profile domination inputs have
been discharged by the existing uncredited profile bound. -/
theorem p0IntegerizerExponent_rate
    (q : ℕ) (hq : 3 ≤ q) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (p0IntegerizerCutoff q m),
        (p0IntegerizerExponent q m p : ℝ) * Real.log p) / (m : ℝ)^2 ≤
          (1273/500 : ℝ) + (1/16 : ℝ) * Real.log ((q-1:ℕ) : ℝ) -
            (13/16 : ℝ) * Real.log (q : ℝ) + ε := by
  classical
  intro ε hε
  obtain ⟨M1, hM1⟩ := p0UncreditedProfile_rate
  obtain ⟨M2, hM2⟩ := p0LowPrime_minExponent_signed_rate_bound q (by omega)
    (p0IntegerizerCutoff q)
    (by intro m hm h4; exact Nat.le_add_right _ _) (p0IntegerizerMovingExponent q) ε hε
  refine ⟨max (max M1 M2) (q^2), ?_⟩
  intro m hm hpos h4
  have hlow := hM2 m ((le_max_right M1 M2).trans ((le_max_left _ _).trans hm)) hpos h4
  have hlarge := p0Integerizer_nonsquarefull_sum_le_uncredited q m hq hpos h4
    ((le_max_right _ _).trans hm)
  have hlargeNorm := div_le_div_of_nonneg_right hlarge (sq_nonneg (m : ℝ))
  have hcore := hM1 m ((le_max_left M1 M2).trans ((le_max_left _ _).trans hm)) hpos h4
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Nat.primesLE (p0IntegerizerCutoff q m))
    (p := fun p => p ∈ p0SquarefullPrimes m)
    (f := fun p => (p0IntegerizerExponent q m p : ℝ) * Real.log p)
  change (∑ p ∈ (Nat.primesLE (p0IntegerizerCutoff q m)).filter
      (fun p => p ∈ p0SquarefullPrimes m),
      (p0IntegerizerExponent q m p : ℝ) * Real.log p) / (m : ℝ)^2 ≤ _ at hlow
  rw [← hsplit, add_div]
  linarith

end
end Li2Lean.P0
#print axioms Li2Lean.P0.p0IntegerizerExponent_rate
