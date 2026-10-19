/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.Kit.PNTAdapter
import Li2Lean.Kit.L3Rate

namespace Li2Lean.B3

open Filter Topology

/--
The eventual form of the v13 prime-sum bridge.  The finite certificate is
allowed an error tending to zero; the small-prime strip is represented by the
explicit theta term.  This is the analytic bridge used by the H4 rate proof.
-/
theorem qv13PrimeSumRate_of_budget
    (cutoff : ℕ → ℕ) (E : ℕ → ℕ → ℤ) (tau c : ℝ) (P : PrimeAffineProfile)
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hint : (∫ t : ℝ, P.eval t) + 13 / 160 - c < tau)
    (hmajor : ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (cutoff n), (E n p : ℝ) * Real.log p) /
          (((4 * n : ℕ) : ℝ) ^ 2) ≤
        weightedPrimeSum P ((4 * n : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) +
          13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) /
            (((4 * n : ℕ) : ℝ) ^ 2) - c + err n) :
    QV13PrimeSumRate cutoff E tau := by
  let I : ℝ := ∫ t : ℝ, P.eval t
  have hweighted : Tendsto
      (fun n : ℕ => weightedPrimeSum P ((4 * n : ℕ) : ℝ) /
        ((4 * n : ℕ) : ℝ)) atTop (𝓝 I) := by
    have hlim : Tendsto
        (fun x : ℝ => weightedPrimeSum P x / x) atTop (𝓝 I) := by
      simpa [I] using (l3WeightedPrimeLimit_unconditional P)
    have h4nat : Tendsto (fun n : ℕ => 4 * n) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      refine eventually_atTop.2 ⟨b, ?_⟩
      intro n hn
      omega
    exact hlim.comp (tendsto_natCast_atTop_atTop.comp h4nat)
  have hthetaBase : Tendsto
      (fun n : ℕ => Chebyshev.theta ((1 / 10 : ℝ) * (n : ℝ)) /
        (n : ℝ)) atTop (𝓝 (1 / 10 : ℝ)) := by
    exact (hPNT_theta_scaled hPNT_of_primeNumberTheoremAnd (1 / 10)
      (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hthetaScaled : Tendsto
      (fun n : ℕ => (13 / 16 : ℝ) *
        (Chebyshev.theta ((1 / 10 : ℝ) * (n : ℝ)) / (n : ℝ))) atTop
      (𝓝 ((13 / 16 : ℝ) * (1 / 10 : ℝ))) := by
    exact (tendsto_const_nhds.mul hthetaBase)
  have htheta : Tendsto
      (fun n : ℕ => 13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) /
        (((4 * n : ℕ) : ℝ) ^ 2)) atTop (𝓝 (13 / 160 : ℝ)) := by
    have hEq : (fun n : ℕ => 13 * (n : ℝ) *
        Chebyshev.theta ((n : ℝ) / 10) /
          (((4 * n : ℕ) : ℝ) ^ 2)) =ᶠ[atTop]
        (fun n : ℕ => (13 / 16 : ℝ) *
          (Chebyshev.theta ((1 / 10 : ℝ) * (n : ℝ)) / (n : ℝ))) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      norm_num [Nat.cast_mul]
      field_simp [hnR]
      ring
    have h := hthetaScaled.congr' hEq.symm
    norm_num at h ⊢
    exact h
  have hright : Tendsto
      (fun n : ℕ => weightedPrimeSum P ((4 * n : ℕ) : ℝ) /
          ((4 * n : ℕ) : ℝ) +
        13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) /
          (((4 * n : ℕ) : ℝ) ^ 2) - c + err n) atTop
      (𝓝 (I + 13 / 160 - c)) := by
    have hsum := hweighted.add htheta
    have hsub := hsum.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    have hadd := hsub.add herr
    simpa [sub_eq_add_neg] using hadd
  intro ε hε
  have hupper : ∀ᶠ n : ℕ in atTop,
      weightedPrimeSum P ((4 * n : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) +
        13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) /
          (((4 * n : ℕ) : ℝ) ^ 2) - c + err n < tau + ε := by
    exact (tendsto_order.mp hright).2 (tau + ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmajor.and hupper)
  refine ⟨N, ?_⟩
  intro n hn hnpos
  exact (hN n hn).1.trans (le_of_lt ((hN n hn).2))

end Li2Lean.B3

#print axioms Li2Lean.B3.qv13PrimeSumRate_of_budget
