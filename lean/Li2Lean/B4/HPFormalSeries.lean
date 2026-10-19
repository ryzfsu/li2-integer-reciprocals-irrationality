/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Li2Lean/B4/HPFormalSeries.lean (compiled formal power-series layer)

Shared formal power series layer (S1-S2) for
  * B4 #1  `hpIntegralInput_producer`  (V_n integrality, HPVpolyIntegrality.lean)
  * B4 #5  `delta_identity`            (the delta identity construction, the proof component)

The source and toolchain are fixed by the release build.
Paper: v13 `hp-tail.tex:20-52` (residues, A_n/B_n/C_n, eq:hp-tail-series,
the two Casoratian eliminations).

Names and statements of `hpCo`, `hpLogSeriesQ`, `hpLi2SeriesQ`, `hpRSeries`,
`coeff_hpCo_monomialSum_mul`, `coeff_hpRSeries`, `hpRSeries_coeff_lt`,
`hpRSeries_coeff_ge`, `hpRSeries_eq_X_pow_mul`, `X_pow_dvd_hpRSeries`,
`coeff_mul_eq_zero_of_X_pow_dvd`, `hpBpoly_natDegree_le`, `hpCpoly_natDegree_le`,
`hpApoly_natDegree_le` are IDENTICAL to the delta source (namespace
`Li2Lean.B4.TailAnalytic`).  The delta file should `import Li2Lean.B4.HPFormalSeries`
and delete its own copies of S1, S2 and the three degree lemmas of S5.

Changes w.r.t. the delta source (proofs only, statements unchanged):
  * `coeff_hpRSeries` goes through the general convolution `coeff_hpCo_mul_mk`
    (antidiagonal + truncation), not through `C_mul_X_pow_eq_monomial`/`coe_X`.
  * the `k = 0` case uses the local `hpThreeFormCoeff_zero_fs` (same one-line
    proof as master `HPNoAdjSeriesBridge.lean:348`), so this file does not
    import HPNoAdjSeriesBridge / HPNoAdjacentActual.

Imports only HPIntegralForm (W_n, V_n, hpbN, hpLR) and M0c (all-n residue facts).
-/
import Mathlib
import Li2Lean.B4.HPIntegralForm
import Li2Lean.B4.ResidueCertificateAllN_M0c

open Finset Polynomial

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues

/-! ## S1a. Series and the polynomial-to-series ring hom -/

/-- Polynomial-to-power-series coercion as a ring hom (same abbrev as
P0/IntegerizationS08Determinant.lean:33). -/
abbrev hpCo : ℚ[X] →+* PowerSeries ℚ := Polynomial.coeToPowerSeries.ringHom

/-- `-log(1-X) = Σ_{k≥1} X^k/k`; the `k = 0` term is `(0:ℚ)⁻¹ = 0`. -/
def hpLogSeriesQ : PowerSeries ℚ := PowerSeries.mk fun k => ((k : ℚ))⁻¹

/-- `Li₂(X) = Σ_{k≥1} X^k/k²`. -/
def hpLi2SeriesQ : PowerSeries ℚ := PowerSeries.mk fun k => ((k : ℚ))⁻¹ ^ 2

/-- Formal `R_m = A_m + B_m(-log(1-X)) + C_m Li₂(X)`, hp-tail.tex:38. -/
def hpRSeries (m : ℕ) : PowerSeries ℚ :=
  hpCo (hpApoly m) + hpCo (hpBpoly m) * hpLogSeriesQ +
    hpCo (hpCpoly m) * hpLi2SeriesQ

/-! ## S1b. Degrees of A, B, C (hp-tail.tex:26-32) -/

theorem hpBpoly_natDegree_le (m : ℕ) : (hpBpoly m).natDegree ≤ m := by
  unfold hpBpoly
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hj; omega)

theorem hpCpoly_natDegree_le (m : ℕ) : (hpCpoly m).natDegree ≤ m := by
  unfold hpCpoly
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hj; omega)

theorem hpApoly_natDegree_le (m : ℕ) : (hpApoly m).natDegree ≤ m := by
  unfold hpApoly
  apply natDegree_sum_le_of_forall_le
  intro r hr
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hr; omega)

/-! ## S1c. Coefficients of `polynomial × series` -/

theorem coeff_hpCo (p : ℚ[X]) (k : ℕ) : PowerSeries.coeff k (hpCo p) = p.coeff k :=
  Polynomial.coeff_coe p k

/-- Truncation of a finite convolution: both sides equal the sum over
`range (k+n+1)` of the guarded term. -/
theorem sum_range_trunc (c s : ℕ → ℚ) {n : ℕ} (hc : ∀ j, n < j → c j = 0) (k : ℕ) :
    ∑ x ∈ range (k + 1), c x * s (k - x) =
      ∑ j ∈ range (n + 1), if j ≤ k then c j * s (k - j) else 0 := by
  have hsub1 : range (k + 1) ⊆ range (k + n + 1) := Finset.range_subset_range.mpr (by omega)
  have hsub2 : range (n + 1) ⊆ range (k + n + 1) := Finset.range_subset_range.mpr (by omega)
  calc ∑ x ∈ range (k + 1), c x * s (k - x)
      = ∑ x ∈ range (k + 1), (if x ≤ k then c x * s (k - x) else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxk : x ≤ k := by have := Finset.mem_range.mp hx; omega
        rw [if_pos hxk]
    _ = ∑ x ∈ range (k + n + 1), (if x ≤ k then c x * s (k - x) else 0) := by
        refine Finset.sum_subset hsub1 fun x _ hx => ?_
        have hxk : ¬ x ≤ k := fun h => hx (Finset.mem_range.mpr (by omega))
        rw [if_neg hxk]
    _ = ∑ x ∈ range (n + 1), (if x ≤ k then c x * s (k - x) else 0) := by
        refine (Finset.sum_subset hsub2 fun x _ hx => ?_).symm
        have hxn : n < x := by
          by_contra h
          exact hx (Finset.mem_range.mpr (by omega))
        rw [hc x hxn]
        simp

/-- General convolution: `natDegree p ≤ n`.  The guard `j ≤ k` is the exact
shape of the delta source; under `j = k` the series term `s 0` survives, and for
`s = (·)⁻¹`, `(·)⁻¹ ^ 2` it is `0`. -/
theorem coeff_hpCo_mul_mk (p : ℚ[X]) (s : ℕ → ℚ) {n : ℕ} (hp : p.natDegree ≤ n) (k : ℕ) :
    PowerSeries.coeff k (hpCo p * PowerSeries.mk s) =
      ∑ j ∈ range (n + 1), if j ≤ k then p.coeff j * s (k - j) else 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_hpCo, PowerSeries.coeff_mk]
  exact sum_range_trunc (fun j => p.coeff j) s
    (fun j hj => coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hj)) k

/-- Convolution of a finite monomial sum against `mk s` (delta-Generated statement). -/
theorem coeff_hpCo_monomialSum_mul (m k : ℕ) (w s : ℕ → ℚ) :
    PowerSeries.coeff k
        (hpCo (∑ j ∈ range (m + 1), Polynomial.monomial j (w j)) *
          PowerSeries.mk s) =
      ∑ j ∈ range (m + 1), if j ≤ k then w j * s (k - j) else 0 := by
  classical
  have hdeg : (∑ j ∈ range (m + 1), Polynomial.monomial j (w j)).natDegree ≤ m := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hj; omega)
  rw [coeff_hpCo_mul_mk _ s hdeg k]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  have hcoef : (∑ i ∈ range (m + 1), Polynomial.monomial i (w i)).coeff j = w j := by
    simp [Polynomial.coeff_monomial, hjm]
  rw [hcoef]

/-- `hpThreeFormCoeff m 0 = 0` (same proof as master HPNoAdjSeriesBridge.lean:348;
re-proved here to keep the import set small). -/
theorem hpThreeFormCoeff_zero_fs (m : ℕ) : hpThreeFormCoeff m 0 = 0 := by
  simp [hpThreeFormCoeff, hpApoly_coeff, hpResidueConvolution]

/-- (S1) The formal remainder has exactly the three-form coefficients. -/
theorem coeff_hpRSeries (m k : ℕ) :
    PowerSeries.coeff k (hpRSeries m) = hpThreeFormCoeff m k := by
  unfold hpRSeries hpLogSeriesQ hpLi2SeriesQ
  rw [map_add, map_add, coeff_hpCo,
    coeff_hpCo_mul_mk _ _ (hpBpoly_natDegree_le m),
    coeff_hpCo_mul_mk _ _ (hpCpoly_natDegree_le m),
    hpThreeFormCoeff, hpResidueConvolution, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  rw [hpBpoly_coeff_of_le m j hjm, hpCpoly_coeff_of_le m j hjm]
  by_cases hjk : j < k
  · rw [if_pos hjk.le, if_pos hjk.le, if_pos hjk, Nat.cast_sub hjk.le]
    have hpos : (0 : ℚ) < (k : ℚ) - (j : ℚ) := by
      apply sub_pos.mpr
      exact_mod_cast hjk
    have hden : ((k : ℚ) - (j : ℚ)) ≠ 0 := ne_of_gt hpos
    field_simp [hden]
  · by_cases hje : j = k
    · subst hje
      simp
    · have hnle : ¬ j ≤ k := by omega
      rw [if_neg hnle, if_neg hnle, if_neg hjk, add_zero]

/-! ## S2. Order and leading part of `R_m` (existing all-n residue facts) -/

theorem hpRSeries_coeff_lt (m k : ℕ) (hk : k < 3 * m + 2) :
    PowerSeries.coeff k (hpRSeries m) = 0 := by
  rw [coeff_hpRSeries]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hpThreeFormCoeff_zero_fs m
  by_cases hkm : k ≤ m
  · exact hpThreeFormCoeff_eq_zero_of_le m k hk0 hkm            -- ResidueTailAlgebra.lean:171
  · exact hpThreeFormCoeff_eq_zero_of_middle m k (by omega) (by omega)
      (_root_.Li2Lean.B4.hpartial_for_residueTailAlgebra_all m k (by omega))  -- M0c:278

theorem hpRSeries_coeff_ge (m k : ℕ) (hk : 3 * m + 2 ≤ k) :
    PowerSeries.coeff k (hpRSeries m) = hpPhiValue m k := by
  rw [coeff_hpRSeries]
  exact _root_.Li2Lean.B4.hpTailCoeff_all m k hk     -- M0c:283

/-- (S2) `R_m = X^(3m+2) * Σ_j Φ_m(j+3m+2) X^j`, eq:hp-tail-series. -/
theorem hpRSeries_eq_X_pow_mul (m : ℕ) :
    hpRSeries m = PowerSeries.X ^ (3 * m + 2) *
      PowerSeries.mk (fun j => hpPhiValue m (j + (3 * m + 2))) := by
  refine PowerSeries.ext fun k => ?_
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hk
  · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel hk, hpRSeries_coeff_ge m k hk]
  · exact hpRSeries_coeff_lt m k (by omega)

theorem X_pow_dvd_hpRSeries (m : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ (3 * m + 2) ∣ hpRSeries m :=
  ⟨_, hpRSeries_eq_X_pow_mul m⟩

theorem coeff_mul_eq_zero_of_X_pow_dvd {f : PowerSeries ℚ} {N k : ℕ}
    (hf : PowerSeries.X ^ N ∣ f) (hk : k < N) (g : PowerSeries ℚ) :
    PowerSeries.coeff k (f * g) = 0 :=
  PowerSeries.X_pow_dvd_iff.mp (hf.mul_right g) k hk

/-! ## S1d. The two Casoratian eliminations (hp-tail.tex:42-52, 81-88)

Used by HPVpolyIntegrality (moments).  Not used by the delta file. -/

/-- Polynomial part of the second elimination `C_{n+1}R_n - C_nR_{n+1}`. -/
def hpWpolyLog (n : ℕ) : ℚ[X] :=
  hpCpoly (n + 1) * hpApoly n - hpCpoly n * hpApoly (n + 1)

theorem hpVpoly_natDegree_le (n : ℕ) : (hpVpoly n).natDegree ≤ 2 * n + 1 := by
  unfold hpVpoly
  refine (natDegree_sub_le_of_le
    (natDegree_mul_le_of_le (hpBpoly_natDegree_le (n + 1)) (hpCpoly_natDegree_le n))
    (natDegree_mul_le_of_le (hpBpoly_natDegree_le n) (hpCpoly_natDegree_le (n + 1)))).trans ?_
  exact max_le (by omega) (by omega)

theorem hpWpoly_natDegree_le (n : ℕ) : (hpWpoly n).natDegree ≤ 2 * n + 1 := by
  unfold hpWpoly
  refine (natDegree_sub_le_of_le
    (natDegree_mul_le_of_le (hpBpoly_natDegree_le (n + 1)) (hpApoly_natDegree_le n))
    (natDegree_mul_le_of_le (hpBpoly_natDegree_le n) (hpApoly_natDegree_le (n + 1)))).trans ?_
  exact max_le (by omega) (by omega)

theorem hpWpolyLog_natDegree_le (n : ℕ) : (hpWpolyLog n).natDegree ≤ 2 * n + 1 := by
  unfold hpWpolyLog
  refine (natDegree_sub_le_of_le
    (natDegree_mul_le_of_le (hpCpoly_natDegree_le (n + 1)) (hpApoly_natDegree_le n))
    (natDegree_mul_le_of_le (hpCpoly_natDegree_le n) (hpApoly_natDegree_le (n + 1)))).trans ?_
  exact max_le (by omega) (by omega)

/-- `B_{n+1}R_n - B_nR_{n+1} = W_n + V_n Li₂` (log part cancels identically). -/
theorem hpE_series (n : ℕ) :
    hpCo (hpBpoly (n + 1)) * hpRSeries n - hpCo (hpBpoly n) * hpRSeries (n + 1) =
      hpCo (hpWpoly n) + hpCo (hpVpoly n) * hpLi2SeriesQ := by
  simp only [hpRSeries, hpWpoly, hpVpoly, map_sub, map_mul]
  ring

/-- `C_{n+1}R_n - C_nR_{n+1} = W'_n - V_n (-log(1-X))` (Li₂ part cancels). -/
theorem hpF_series (n : ℕ) :
    hpCo (hpCpoly (n + 1)) * hpRSeries n - hpCo (hpCpoly n) * hpRSeries (n + 1) =
      hpCo (hpWpolyLog n) - hpCo (hpVpoly n) * hpLogSeriesQ := by
  simp only [hpRSeries, hpWpolyLog, hpVpoly, map_sub, map_mul]
  ring

theorem X_pow_dvd_elim (n : ℕ) (P Q : ℚ[X]) :
    (PowerSeries.X : PowerSeries ℚ) ^ (3 * n + 2) ∣
      hpCo P * hpRSeries n - hpCo Q * hpRSeries (n + 1) := by
  refine dvd_sub (Dvd.dvd.mul_left (X_pow_dvd_hpRSeries n) _) (Dvd.dvd.mul_left ?_ _)
  exact (pow_dvd_pow (PowerSeries.X : PowerSeries ℚ)
    (show 3 * n + 2 ≤ 3 * (n + 1) + 2 by omega)).trans (X_pow_dvd_hpRSeries (n + 1))

theorem hpE_coeff_eq_zero (n k : ℕ) (hk : k ≤ 3 * n + 1) :
    PowerSeries.coeff k (hpCo (hpWpoly n) + hpCo (hpVpoly n) * hpLi2SeriesQ) = 0 := by
  rw [← hpE_series]
  exact PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_elim n _ _) k (by omega)

theorem hpF_coeff_eq_zero (n k : ℕ) (hk : k ≤ 3 * n + 1) :
    PowerSeries.coeff k (hpCo (hpWpolyLog n) - hpCo (hpVpoly n) * hpLogSeriesQ) = 0 := by
  rw [← hpF_series]
  exact PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_elim n _ _) k (by omega)

end

end Li2Lean.B4.TailAnalytic
