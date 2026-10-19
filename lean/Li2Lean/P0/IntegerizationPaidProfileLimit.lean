/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.PNTAdapter

namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology

/-- The sum of normalized weighted-prime profile contributions. -/
def p0PaidPrimeProfileSum (profiles : List PrimeAffineProfile) (m : ℕ) : ℝ :=
  (profiles.map fun profile => weightedPrimeSum profile m / (m : ℝ)).sum

/-- The limiting integral budget of a finite profile family. -/
def p0PaidPrimeProfileRate (profiles : List PrimeAffineProfile) : ℝ :=
  (profiles.map fun profile => ∫ t : ℝ, profile.eval t).sum

theorem p0PaidPrimeProfileSum_tendsto (profiles : List PrimeAffineProfile) :
    Tendsto (p0PaidPrimeProfileSum profiles) atTop
      (𝓝 (p0PaidPrimeProfileRate profiles)) := by
  induction profiles with
  | nil =>
      change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)
      exact tendsto_const_nhds
  | cons profile profiles ih =>
      change Tendsto
        (fun m : ℕ => weightedPrimeSum profile m / (m : ℝ) +
          p0PaidPrimeProfileSum profiles m)
        atTop
        (𝓝 ((∫ t : ℝ, profile.eval t) + p0PaidPrimeProfileRate profiles))
      have hprofile : Tendsto
          (fun m : ℕ => weightedPrimeSum profile m / (m : ℝ))
          atTop (𝓝 (∫ t : ℝ, profile.eval t)) := by
        exact (l3WeightedPrimeLimit_unconditional profile).comp
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
      exact hprofile.add ih

/-- A finite paid budget consists of profile contributions, a remainder,
and a subtracted feature payment. -/
def p0PaidProfileBudget (profiles : List PrimeAffineProfile)
    (remainder feature : ℕ → ℝ) (m : ℕ) : ℝ :=
  p0PaidPrimeProfileSum profiles m + remainder m - feature m

theorem p0PaidProfileBudget_tendsto
    (profiles : List PrimeAffineProfile) (remainder feature : ℕ → ℝ)
    (remainderLimit featureLimit : ℝ)
    (hremainder : Tendsto remainder atTop (𝓝 remainderLimit))
    (hfeature : Tendsto feature atTop (𝓝 featureLimit)) :
    Tendsto (p0PaidProfileBudget profiles remainder feature) atTop
      (𝓝 (p0PaidPrimeProfileRate profiles + remainderLimit - featureLimit)) := by
  change Tendsto
    (fun m : ℕ => p0PaidPrimeProfileSum profiles m + remainder m - feature m)
    atTop (𝓝 (p0PaidPrimeProfileRate profiles + remainderLimit - featureLimit))
  exact ((p0PaidPrimeProfileSum_tendsto profiles).add hremainder).sub hfeature

/-- A strict gap between a convergent paid budget and the target rate turns
any matching finite domination into an eventual rate bound. -/
theorem p0Scalar_rate_of_tendsto_paidBudget
    (D : ℕ → ℚ) (budget : ℕ → ℝ) (limit target : ℝ)
    (hbudget : Tendsto budget atTop (𝓝 limit)) (hbelow : limit < target)
    (hfinite : ∀ m : ℕ, 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ)^2 ≤ budget m) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ)^2 ≤ target := by
  have he := (tendsto_order.mp hbudget).2 target hbelow
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  refine ⟨M, ?_⟩
  intro m hm hp h4
  exact le_trans (hfinite m hp h4) (hM m hm).le

end
end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0PaidPrimeProfileSum_tendsto
#print axioms Li2Lean.P0.Integerization.p0PaidProfileBudget_tendsto
#print axioms Li2Lean.P0.Integerization.p0Scalar_rate_of_tendsto_paidBudget
