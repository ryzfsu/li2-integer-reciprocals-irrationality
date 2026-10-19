/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Li2Lean/B4/HPVpolyIntegrality.lean (compiled integrality certificate)

B4 #1 `hpIntegralInput_producer`: integrality of the actual v13 linear forms,
`HPIntegralForm a` for every `a ≠ 0`.  All six `sorry`s of
`the construction source` are replaced by proofs; the file
contains no `sorry`, `admit` or `axiom`.

Base: verified source snapshot, with Mathlib `25e572b8`.
Paper: v13 `hp-tail.tex:26-197`.
Exact checks of every lemma STATEMENT below (n <= 12, plus sympy for the two
closing rational identities): the finite-data check, output `.out`.

Route (finite algebra over ℚ, no Mellin integral, no J_n, no dimension count):
  S2  moments of π_j = V_{N-j} from `X^(3n+2) ∣ E_n, F_n`   (HPFormalSeries)
  S3  Lagrange lemma: moments ⇒ π_j = (-1)^j C(N,j) C(n+j,j)^2 (α+βj)
  S4  π_0 = -b²(12n+17), π_1 = b²(2n+1)(n+1)((n+1)(12n+17)+21n+29)
      (split per the §5 alternative: harmonic elimination by `ring` first, then
       the factorial/binomial products by `field_simp`, then a small rational
       identity)
  S5  V_i/b² = Q_i ∈ ℤ, W_k/b² = -Σ Q_j/(k-j)², `HPIntegerizationInput`
  S6  a^N·eval(1/a) and `HPIntegralForm`

Convention: every `field_simp` / `push_cast` whose closing behaviour is not
certain is followed by `all_goals ring` (a no-op when the goal is already
closed), so a stronger normal form cannot turn into a "no goals" error.
-/
import Li2Lean.B4.HPFormalSeries
import Li2Lean.B4.DenominatorRate

open Finset Polynomial

namespace Li2Lean.B4.HPVpolyIntegrality

noncomputable section

open Li2Lean.B4.Residues Li2Lean.B4.TailAnalytic

/-! ### S2b: coefficient form of the two eliminations (C3, C4 in the checks) -/

/-- `E_n` coefficient, all `k ≤ 3n+1`. -/
theorem hpW_add_li2_conv (n k : ℕ) (hk : k ≤ 3 * n + 1) :
    (hpWpoly n).coeff k +
      (∑ i ∈ range (2 * n + 1 + 1),
        if i ≤ k then (hpVpoly n).coeff i * (((k - i : ℕ) : ℚ))⁻¹ ^ 2 else 0) = 0 := by
  have h := hpE_coeff_eq_zero n k hk
  rw [map_add, coeff_hpCo, hpLi2SeriesQ,
    coeff_hpCo_mul_mk _ _ (hpVpoly_natDegree_le n)] at h
  exact h

/-- `F_n` coefficient, all `k ≤ 3n+1`. -/
theorem hpWlog_sub_log_conv (n k : ℕ) (hk : k ≤ 3 * n + 1) :
    (hpWpolyLog n).coeff k -
      (∑ i ∈ range (2 * n + 1 + 1),
        if i ≤ k then (hpVpoly n).coeff i * (((k - i : ℕ) : ℚ))⁻¹ else 0) = 0 := by
  have h := hpF_coeff_eq_zero n k hk
  rw [map_sub, coeff_hpCo, hpLogSeriesQ,
    coeff_hpCo_mul_mk _ _ (hpVpoly_natDegree_le n)] at h
  exact h

/-- Reversed coefficients `π_j = v_{N-j}`, `N = 2n+1` (v13 `hp-tail.tex:73`). -/
def hpPi (n j : ℕ) : ℚ := (hpVpoly n).coeff (2 * n + 1 - j)

/-- The two moment families (v13 eq:hp-moments), in the reflected index. -/
theorem hpPi_moments (n ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    (∑ j ∈ range (2 * n + 1 + 1), hpPi n j / ((ℓ + j : ℕ) : ℚ)) = 0 ∧
    (∑ j ∈ range (2 * n + 1 + 1), hpPi n j / ((ℓ + j : ℕ) : ℚ) ^ 2) = 0 := by
  have hWk : (hpWpoly n).coeff (2 * n + 1 + ℓ) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hpWpoly_natDegree_le n) (by omega))
  have hWlk : (hpWpolyLog n).coeff (2 * n + 1 + ℓ) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hpWpolyLog_natDegree_le n) (by omega))
  have h1 := hpWlog_sub_log_conv n (2 * n + 1 + ℓ) (by omega)
  have h2 := hpW_add_li2_conv n (2 * n + 1 + ℓ) (by omega)
  rw [hWlk, zero_sub, neg_eq_zero, ← Finset.sum_range_reflect] at h1
  rw [hWk, zero_add, ← Finset.sum_range_reflect] at h2
  constructor
  · refine Eq.trans (Finset.sum_congr rfl fun j hj => ?_) h1
    have hj' : j < 2 * n + 1 + 1 := Finset.mem_range.mp hj
    have hle : 2 * n + 1 + 1 - 1 - j ≤ 2 * n + 1 + ℓ := by omega
    have hsub : 2 * n + 1 + ℓ - (2 * n + 1 + 1 - 1 - j) = ℓ + j := by omega
    have hidx : 2 * n + 1 + 1 - 1 - j = 2 * n + 1 - j := by omega
    rw [if_pos hle, hsub, hidx, hpPi, div_eq_mul_inv]
  · refine Eq.trans (Finset.sum_congr rfl fun j hj => ?_) h2
    have hj' : j < 2 * n + 1 + 1 := Finset.mem_range.mp hj
    have hle : 2 * n + 1 + 1 - 1 - j ≤ 2 * n + 1 + ℓ := by omega
    have hsub : 2 * n + 1 + ℓ - (2 * n + 1 + 1 - 1 - j) = ℓ + j := by omega
    have hidx : 2 * n + 1 + 1 - 1 - j = 2 * n + 1 - j := by omega
    rw [if_pos hle, hsub, hidx, hpPi, div_eq_mul_inv, inv_pow]

/-! ### S3: Lagrange two-parameter lemma (pure algebra; C12, C14 in the checks)

`D_j = ∏_{r≤N, r≠j} (X + (r+1))`, `G = Σ_j c_j D_j`.  For every `k`,
`G = F0·D − F1·(X − k)·D + (X − k)²·H_k`, `F0 = Σ c_j/(k+j+1)`,
`F1 = Σ c_j/(k+j+1)²`.  The moments kill `F0, F1` for `k = ℓ−1 ∈ [0,n)`, so
`∏_{k<n}(X−k)² ∣ G`; degree forces the cofactor to be linear; evaluation at
`−(j+1)` gives the shape. -/

section Lagrange

variable (N : ℕ)

def lagD : ℚ[X] := ∏ r ∈ range (N + 1), (X + C ((r : ℚ) + 1))
def lagDj (j : ℕ) : ℚ[X] := ∏ r ∈ (range (N + 1)).erase j, (X + C ((r : ℚ) + 1))
def lagG (pc : ℕ → ℚ) : ℚ[X] := ∑ j ∈ range (N + 1), C (pc j) * lagDj N j

theorem lagD_eq (j : ℕ) (hj : j ∈ range (N + 1)) :
    lagD N = (X + C ((j : ℚ) + 1)) * lagDj N j := by
  unfold lagD lagDj
  exact (Finset.mul_prod_erase (range (N + 1)) (fun r : ℕ => X + C ((r : ℚ) + 1)) hj).symm

/-- Per-term identity (C14). -/
theorem lag_term (p k c : ℚ) (hc : c ≠ 0) (Dj : ℚ[X]) :
    C p * Dj = C (p / c) * ((X - C k) + C c) * Dj
      - C (p / c ^ 2) * (X - C k) * ((X - C k) + C c) * Dj
      + (X - C k) ^ 2 * (C (p / c ^ 2) * Dj) := by
  have h1 : C (p / c) * C c = C p := by
    rw [← C_mul]
    congr 1
    field_simp
    all_goals ring
  have h2 : C (p / c ^ 2) * C c = C (p / c) := by
    rw [← C_mul]
    congr 1
    field_simp
    all_goals ring
  linear_combination (-Dj) * h1 + ((X - C k) * Dj) * h2

theorem lagG_expand (pc : ℕ → ℚ) (k : ℕ) :
    lagG N pc =
      C (∑ j ∈ range (N + 1), pc j / ((k : ℚ) + j + 1)) * lagD N
      - C (∑ j ∈ range (N + 1), pc j / ((k : ℚ) + j + 1) ^ 2) * (X - C (k : ℚ)) * lagD N
      + (X - C (k : ℚ)) ^ 2 *
          ∑ j ∈ range (N + 1), C (pc j / ((k : ℚ) + j + 1) ^ 2) * lagDj N j := by
  rw [lagG, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hc : ((k : ℚ) + j + 1) ≠ 0 := by positivity
  have hX : X + C ((j : ℚ) + 1) = (X - C (k : ℚ)) + C ((k : ℚ) + j + 1) := by
    simp only [map_add, map_one]
    ring
  rw [lagD_eq N j hj, hX]
  linear_combination lag_term (pc j) (k : ℚ) ((k : ℚ) + j + 1) hc (lagDj N j)

theorem lagDj_natDegree (j : ℕ) (hj : j ∈ range (N + 1)) : (lagDj N j).natDegree = N := by
  have hmon : ∀ r ∈ (range (N + 1)).erase j, (X + C ((r : ℚ) + 1)).Monic :=
    fun r _ => monic_X_add_C _
  have hdeg : ∀ r ∈ (range (N + 1)).erase j, (X + C ((r : ℚ) + 1)).natDegree = 1 :=
    fun r _ => natDegree_X_add_C _
  unfold lagDj
  rw [natDegree_prod_of_monic (h := hmon), Finset.sum_const_nat hdeg,
    Finset.card_erase_of_mem hj, Finset.card_range]
  omega

theorem lagG_natDegree_le (pc : ℕ → ℚ) : (lagG N pc).natDegree ≤ N := by
  unfold lagG
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans (lagDj_natDegree N j hj).le

/-- (C12) `D_j(-(j+1)) = ∏_{r≤N, r≠j} (r - j) = (-1)^j j! (N-j)!`.
Reduced to the compiled master lemma `eval_hpOffPoly_at_pole`
(ResidueCertificateFactorialHarmonic.lean:88). -/
theorem lagDj_eval (j : ℕ) (hj : j ≤ N) :
    (lagDj N j).eval (-((j : ℚ) + 1)) =
      (-1) ^ j * (j.factorial : ℚ) * ((N - j).factorial : ℚ) := by
  have hmem : j ∈ range (N + 1) := Finset.mem_range.mpr (by omega)
  have hprod : (lagDj N j).eval (-((j : ℚ) + 1)) =
      ∏ r ∈ (range (N + 1)).erase j, (-((j : ℚ) - (r : ℚ))) := by
    unfold lagDj
    rw [eval_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [eval_add, eval_X, eval_C]
    ring
  have hoff : (Li2Lean.B4.ResidueTailBridge.hpOffPoly N j).eval (j : ℚ) =
      ∏ r ∈ (range (N + 1)).erase j, ((j : ℚ) - (r : ℚ)) := by
    unfold Li2Lean.B4.ResidueTailBridge.hpOffPoly hpPole
    rw [eval_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [eval_sub, eval_X, eval_C]
  rw [hprod, Finset.prod_neg, Finset.card_erase_of_mem hmem, Finset.card_range,
    Nat.add_sub_cancel, ← hoff, Li2Lean.B4.ResidueTailBridge.eval_hpOffPoly_at_pole N j hj]
  have hpow : ((-1 : ℚ)) ^ N = (-1) ^ j * (-1) ^ (N - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hpow]
  have hsq : ((-1 : ℚ) ^ (N - j)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  linear_combination ((-1 : ℚ) ^ j * (j.factorial : ℚ) * ((N - j).factorial : ℚ)) * hsq

end Lagrange

/-- (C12) `M(-(j+1)) = ∏_{k<n} (j+1+k)^2 = ((n+j)!/j!)^2`, via the compiled master
lemma `prod_shift_factorial` (ResidueCertificateFactorialHarmonic.lean:45). -/
theorem lagM_eval (n j : ℕ) :
    (∏ k ∈ range n, (X - C (k : ℚ)) ^ 2).eval (-((j : ℚ) + 1)) =
      (((n + j).factorial : ℚ) / (j.factorial : ℚ)) ^ 2 := by
  have hterm : ∀ k ∈ range n,
      ((X - C (k : ℚ)) ^ 2).eval (-((j : ℚ) + 1)) = (((j + k + 1 : ℕ) : ℚ)) ^ 2 := by
    intro k _
    rw [eval_pow, eval_sub, eval_X, eval_C]
    push_cast
    all_goals ring
  have hfj : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h := Li2Lean.B4.ResidueTailBridge.prod_shift_factorial j n
  rw [Nat.add_comm j n] at h
  have hP : ∏ t ∈ range n, (((j + t + 1 : ℕ)) : ℚ) =
      ((n + j).factorial : ℚ) / (j.factorial : ℚ) := by
    rw [eq_div_iff hfj]
    linear_combination h
  rw [eval_prod, Finset.prod_congr rfl hterm, Finset.prod_pow, hP]

/-- Main generic lemma: `2n` moment conditions on `c_0..c_{2n+1}` ⇒ two-parameter shape. -/
theorem hp_lagrange_two_param (n : ℕ) (pc : ℕ → ℚ)
    (hm : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ n →
      (∑ j ∈ range (2 * n + 1 + 1), pc j / ((ℓ + j : ℕ) : ℚ)) = 0 ∧
      (∑ j ∈ range (2 * n + 1 + 1), pc j / ((ℓ + j : ℕ) : ℚ) ^ 2) = 0) :
    ∃ α β : ℚ, ∀ j, j ≤ 2 * n + 1 →
      pc j = (-1) ^ j * ((2 * n + 1).choose j : ℚ) * ((n + j).choose j : ℚ) ^ 2 *
        (α + β * j) := by
  classical
  -- (1) double roots at k = 0..n-1
  have hroot : ∀ k ∈ range n, (X - C (k : ℚ)) ^ 2 ∣ lagG (2 * n + 1) pc := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    obtain ⟨h0, h1⟩ := hm (k + 1) (by omega) (by omega)
    have hcast : ∀ j : ℕ, ((k + 1 + j : ℕ) : ℚ) = (k : ℚ) + j + 1 := by
      intro j
      push_cast
      all_goals ring
    have e0 : (∑ j ∈ range (2 * n + 1 + 1), pc j / ((k : ℚ) + j + 1)) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h0
      rw [hcast j]
    have e1 : (∑ j ∈ range (2 * n + 1 + 1), pc j / ((k : ℚ) + j + 1) ^ 2) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
      rw [hcast j]
    rw [lagG_expand (2 * n + 1) pc k, e0, e1]
    simp only [map_zero, zero_mul, sub_zero, zero_add]
    exact dvd_mul_right _ _
  -- (2) product of coprime squares divides G
  have hMdvd : (∏ k ∈ range n, (X - C (k : ℚ)) ^ 2) ∣ lagG (2 * n + 1) pc := by
    refine Finset.prod_dvd_of_coprime ?_ hroot
    intro a _ b _ hab
    exact IsCoprime.pow
      (pairwise_coprime_X_sub_C (s := fun k : ℕ => (k : ℚ)) Nat.cast_injective hab)
  obtain ⟨L, hL⟩ := hMdvd
  have hMmon : ∀ k ∈ range n, ((X - C (k : ℚ)) ^ 2).Monic := fun k _ => (monic_X_sub_C _).pow 2
  have hMmonic : (∏ k ∈ range n, (X - C (k : ℚ)) ^ 2).Monic :=
    monic_prod_of_monic _ _ hMmon
  have hMk : ∀ k ∈ range n, ((X - C (k : ℚ)) ^ 2).natDegree = 2 := fun k _ => by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hMdeg : (∏ k ∈ range n, (X - C (k : ℚ)) ^ 2).natDegree = 2 * n := by
    rw [natDegree_prod_of_monic (h := hMmon), Finset.sum_const_nat hMk, Finset.card_range]
    omega
  -- (3) cofactor is linear
  have hLdeg : L.natDegree ≤ 1 := by
    by_cases hL0 : L = 0
    · simp [hL0]
    · have h := lagG_natDegree_le (2 * n + 1) pc
      rw [hL, hMmonic.natDegree_mul' hL0, hMdeg] at h
      omega
  have hLlin := eq_X_add_C_of_natDegree_le_one hLdeg
  -- (4) evaluate at -(j+1)
  refine ⟨(L.coeff 0 - L.coeff 1) * (n.factorial : ℚ) ^ 2 / ((2 * n + 1).factorial : ℚ),
          -(L.coeff 1) * (n.factorial : ℚ) ^ 2 / ((2 * n + 1).factorial : ℚ), ?_⟩
  intro j hj
  have hjS : j ∈ range (2 * n + 1 + 1) := Finset.mem_range.mpr (by omega)
  have hevalG : (lagG (2 * n + 1) pc).eval (-((j : ℚ) + 1)) =
      pc j * (lagDj (2 * n + 1) j).eval (-((j : ℚ) + 1)) := by
    unfold lagG
    rw [eval_finsetSum, Finset.sum_eq_single j]
    · rw [eval_mul, eval_C]
    · intro i _ hij
      have hz : (lagDj (2 * n + 1) i).eval (-((j : ℚ) + 1)) = 0 := by
        unfold lagDj
        rw [eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩)
        rw [eval_add, eval_X, eval_C]
        ring
      rw [eval_mul, eval_C, hz, mul_zero]
    · intro h
      exact absurd hjS h
  have hGL : (lagG (2 * n + 1) pc).eval (-((j : ℚ) + 1)) =
      (∏ k ∈ range n, (X - C (k : ℚ)) ^ 2).eval (-((j : ℚ) + 1)) *
        (L.coeff 1 * (-((j : ℚ) + 1)) + L.coeff 0) := by
    rw [hL, eval_mul]
    congr 1
    conv_lhs => rw [hLlin]
    rw [eval_add, eval_mul, eval_C, eval_X, eval_C]
  have hDj := lagDj_eval (2 * n + 1) j hj
  have hM := lagM_eval n j
  have hfj : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfN : ((2 * n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  -- binomial normalisations: C(N,j) j! (N-j)! = N!,  C(n+j,j) n! j! = (n+j)!
  have hc1 : (((2 * n + 1).choose j : ℕ) : ℚ) * (j.factorial : ℚ) *
      ((2 * n + 1 - j).factorial : ℚ) = ((2 * n + 1).factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hc2 : (((n + j).choose j : ℕ) : ℚ) * (n.factorial : ℚ) * (j.factorial : ℚ) =
      ((n + j).factorial : ℚ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n j
  have hq : ((n + j).factorial : ℚ) / (j.factorial : ℚ) =
      (((n + j).choose j : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [div_eq_iff hfj]
    linear_combination (-1 : ℚ) * hc2
  have hs : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  -- E : c_j · D_j(-(j+1)) = M(-(j+1)) · L(-(j+1))
  have E := hevalG.symm.trans hGL
  rw [hDj, hM, hq] at E
  have K : pc j * ((2 * n + 1).factorial : ℚ) =
      (-1) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) ^ 2 *
        (n.factorial : ℚ) ^ 2 * (L.coeff 0 - L.coeff 1 * ((j : ℚ) + 1)) := by
    linear_combination ((-1 : ℚ) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ)) * E
      - pc j * hc1
      - (pc j * (((2 * n + 1).choose j : ℕ) : ℚ) * (j.factorial : ℚ) *
          ((2 * n + 1 - j).factorial : ℚ)) * hs
  have hπ : pc j =
      (-1) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) ^ 2 *
        (n.factorial : ℚ) ^ 2 * (L.coeff 0 - L.coeff 1 * ((j : ℚ) + 1)) /
          ((2 * n + 1).factorial : ℚ) := by
    rw [eq_div_iff hfN]
    linear_combination K
  rw [hπ]
  ring

/-! ### S4: top two coefficients from boundary residues (C7 in the checks)
v13 `hp-tail.tex:128-158`. -/

/-- Second-from-top coefficient of a product. -/
theorem coeff_mul_top_two {p q : ℚ[X]} {a b : ℕ}
    (hp : p.natDegree ≤ a + 1) (hq : q.natDegree ≤ b + 1) :
    (p * q).coeff (a + b + 1) = p.coeff a * q.coeff (b + 1) + p.coeff (a + 1) * q.coeff b := by
  have hne : ((a, b + 1) : ℕ × ℕ) ≠ (a + 1, b) := by
    intro h
    injection h with h1 h2
    omega
  have h0 : ∀ x ∈ antidiagonal (a + b + 1), x ≠ (a, b + 1) ∧ x ≠ (a + 1, b) →
      p.coeff x.1 * q.coeff x.2 = 0 := by
    rintro ⟨x1, x2⟩ hx hxne
    have hsum : x1 + x2 = a + b + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    show p.coeff x1 * q.coeff x2 = 0
    rcases lt_or_ge (a + 1) x1 with h1 | h1
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h1), zero_mul]
    · rcases lt_or_ge x1 a with h2 | h2
      · have hx2 : b + 1 < x2 := by omega
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hx2), mul_zero]
      · exfalso
        have hcase : x1 = a ∨ x1 = a + 1 := by omega
        rcases hcase with h | h
        · exact hxne.1 (by rw [h, show x2 = b + 1 by omega])
        · exact hxne.2 (by rw [h, show x2 = b by omega])
  have ha : (a, b + 1) ∉ antidiagonal (a + b + 1) →
      p.coeff (a, b + 1).1 * q.coeff (a, b + 1).2 = 0 := fun h =>
    absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (show a + (b + 1) = a + b + 1 by omega)) h
  have hb : (a + 1, b) ∉ antidiagonal (a + b + 1) →
      p.coeff (a + 1, b).1 * q.coeff (a + 1, b).2 = 0 := fun h =>
    absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (show a + 1 + b = a + b + 1 by omega)) h
  rw [coeff_mul]
  exact Finset.sum_eq_add (a, b + 1) (a + 1, b) hne h0 ha hb

/-- `H_{k+1} = H_k + 1/(k+1)` in the `1/(k+1)` form (from master
`ResidueTailBridge.hpHarmonic_succ`, FactorialHarmonic.lean:148). -/
theorem hpHarmonic_add_one (k : ℕ) :
    hpHarmonic (k + 1) = hpHarmonic k + 1 / ((k : ℚ) + 1) := by
  rw [Li2Lean.B4.ResidueTailBridge.hpHarmonic_succ k]
  push_cast
  all_goals ring

theorem hpResidueU_diag (m : ℕ) :
    hpResidueU m m = -(((2 * m + 1).factorial : ℚ) / (m.factorial : ℚ) ^ 2) := by
  rw [hpResidueU, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one,
    show 3 * m + 1 - m = 2 * m + 1 by omega]

theorem hpResidueU_subdiag (m : ℕ) :
    hpResidueU (m + 1) m = -(((2 * m + 4).factorial : ℚ) / (m.factorial : ℚ) ^ 2) := by
  rw [hpResidueU, show 3 * (m + 1) + 1 - m = 2 * m + 4 by omega,
    show m + 1 - m = 1 by omega, Nat.factorial_one, Nat.cast_one, one_pow, mul_one]

theorem hpResidueV_diag (m : ℕ) :
    hpResidueV m m = hpResidueU m m * (-2 * hpHarmonic m - hpHarmonic (2 * m + 1)) := by
  have h0 : hpHarmonic 0 = 0 := by simp [hpHarmonic]
  rw [hpResidueV, Nat.sub_self, h0, show 3 * m + 1 - m = 2 * m + 1 by omega]
  ring

theorem hpResidueV_subdiag (m : ℕ) :
    hpResidueV (m + 1) m =
      hpResidueU (m + 1) m * (3 - 2 * hpHarmonic m - hpHarmonic (2 * m + 4)) := by
  have h1 : hpHarmonic 1 = 1 := by simp [hpHarmonic]
  rw [hpResidueV, show m + 1 - m = 1 by omega, show 3 * (m + 1) + 1 - m = 2 * m + 4 by omega, h1]
  ring

theorem hpbN_pos (n : ℕ) : 0 < hpbN n := by
  unfold hpbN
  exact Nat.choose_pos (by omega)

theorem hpbN_cast_ne_zero (n : ℕ) : (hpbN n : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (hpbN_pos n).ne'

/-- `b_n n! (n+1)! = (2n+1)!`. -/
theorem hpbN_factorial (n : ℕ) :
    (hpbN n : ℚ) * (n.factorial : ℚ) * ((n + 1).factorial : ℚ) =
      ((2 * n + 1).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n + 1 by omega)
  rw [show 2 * n + 1 - n = n + 1 by omega] at h
  unfold hpbN
  exact_mod_cast h

/-- `v_N = v_{n+1,n+1} u_{n,n} - v_{n,n} u_{n+1,n+1}`. -/
theorem hpVpoly_coeff_top (n : ℕ) :
    (hpVpoly n).coeff (2 * n + 1) =
      hpResidueV (n + 1) (n + 1) * hpResidueU n n -
        hpResidueV n n * hpResidueU (n + 1) (n + 1) := by
  have e1 : (hpBpoly (n + 1) * hpCpoly n).coeff (2 * n + 1) =
      hpResidueV (n + 1) (n + 1) * hpResidueU n n := by
    rw [show 2 * n + 1 = (n + 1) + n by omega,
      coeff_mul_add_eq_of_natDegree_le (hpBpoly_natDegree_le (n + 1)) (hpCpoly_natDegree_le n),
      hpBpoly_coeff_of_le (n + 1) (n + 1) le_rfl, hpCpoly_coeff_of_le n n le_rfl]
  have e2 : (hpBpoly n * hpCpoly (n + 1)).coeff (2 * n + 1) =
      hpResidueV n n * hpResidueU (n + 1) (n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) by omega,
      coeff_mul_add_eq_of_natDegree_le (hpBpoly_natDegree_le n) (hpCpoly_natDegree_le (n + 1)),
      hpBpoly_coeff_of_le n n le_rfl, hpCpoly_coeff_of_le (n + 1) (n + 1) le_rfl]
  rw [hpVpoly, coeff_sub, e1, e2]

/-- `u_{n,n} u_{n+1,n+1} = b_n² (2n+2)(2n+3)`. -/
theorem hpUU_diag (n : ℕ) :
    hpResidueU n n * hpResidueU (n + 1) (n + 1) =
      (hpbN n : ℚ) ^ 2 * ((2 * (n : ℚ) + 2) * (2 * (n : ℚ) + 3)) := by
  have hb := hpbN_factorial n
  have hf1 : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ n]
    push_cast
    all_goals ring
  have hF : ((2 * (n + 1) + 1).factorial : ℚ) =
      (2 * (n : ℚ) + 3) * (2 * (n : ℚ) + 2) * ((2 * n + 1).factorial : ℚ) := by
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega,
      Nat.factorial_succ (2 * n + 1 + 1), Nat.factorial_succ (2 * n + 1)]
    push_cast
    all_goals ring
  have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [hpResidueU_diag n, hpResidueU_diag (n + 1), hF, ← hb, hf1]
  field_simp
  all_goals ring

/-- `π_0 = v_N = -b_n^2 (12n+17)` (C7). -/
theorem hpPi_zero (n : ℕ) :
    hpPi n 0 = -((hpbN n : ℚ) ^ 2 * (12 * (n : ℚ) + 17)) := by
  have hH1 : hpHarmonic (n + 1) = hpHarmonic n + 1 / ((n : ℚ) + 1) := hpHarmonic_add_one n
  have hH3 : hpHarmonic (2 * (n + 1) + 1) =
      hpHarmonic (2 * n + 1) + 1 / (2 * (n : ℚ) + 2) + 1 / (2 * (n : ℚ) + 3) := by
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega,
      hpHarmonic_add_one (2 * n + 1 + 1), hpHarmonic_add_one (2 * n + 1)]
    push_cast
    all_goals ring
  have hdelta : hpPi n 0 = (hpResidueU n n * hpResidueU (n + 1) (n + 1)) *
      (-(2 / ((n : ℚ) + 1)) - 1 / (2 * (n : ℚ) + 2) - 1 / (2 * (n : ℚ) + 3)) := by
    rw [hpPi, Nat.sub_zero, hpVpoly_coeff_top, hpResidueV_diag (n + 1), hpResidueV_diag n,
      hH3, hH1]
    ring
  have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (n : ℚ) + 2 ≠ 0 := by positivity
  have h3 : 2 * (n : ℚ) + 3 ≠ 0 := by positivity
  rw [hdelta, hpUU_diag]
  field_simp
  all_goals ring

/-- Coefficient `2n` of `V_n` for `n = m+1`: four boundary products. -/
theorem hpVpoly_coeff_second (m : ℕ) :
    (hpVpoly (m + 1)).coeff (2 * (m + 1)) =
      (hpResidueV (m + 1 + 1) (m + 1) * hpResidueU (m + 1) (m + 1) +
        hpResidueV (m + 1 + 1) (m + 1 + 1) * hpResidueU (m + 1) m) -
      (hpResidueV (m + 1) m * hpResidueU (m + 1 + 1) (m + 1 + 1) +
        hpResidueV (m + 1) (m + 1) * hpResidueU (m + 1 + 1) (m + 1)) := by
  have e1 : (hpBpoly (m + 1 + 1) * hpCpoly (m + 1)).coeff (2 * (m + 1)) =
      hpResidueV (m + 1 + 1) (m + 1) * hpResidueU (m + 1) (m + 1) +
        hpResidueV (m + 1 + 1) (m + 1 + 1) * hpResidueU (m + 1) m := by
    rw [show 2 * (m + 1) = m + 1 + m + 1 by omega,
      coeff_mul_top_two (hpBpoly_natDegree_le (m + 1 + 1)) (hpCpoly_natDegree_le (m + 1)),
      hpBpoly_coeff_of_le (m + 1 + 1) (m + 1) (by omega),
      hpBpoly_coeff_of_le (m + 1 + 1) (m + 1 + 1) le_rfl,
      hpCpoly_coeff_of_le (m + 1) (m + 1) le_rfl,
      hpCpoly_coeff_of_le (m + 1) m (by omega)]
  have e2 : (hpBpoly (m + 1) * hpCpoly (m + 1 + 1)).coeff (2 * (m + 1)) =
      hpResidueV (m + 1) m * hpResidueU (m + 1 + 1) (m + 1 + 1) +
        hpResidueV (m + 1) (m + 1) * hpResidueU (m + 1 + 1) (m + 1) := by
    rw [show 2 * (m + 1) = m + (m + 1) + 1 by omega,
      coeff_mul_top_two (hpBpoly_natDegree_le (m + 1)) (hpCpoly_natDegree_le (m + 1 + 1)),
      hpBpoly_coeff_of_le (m + 1) m (by omega),
      hpBpoly_coeff_of_le (m + 1) (m + 1) le_rfl,
      hpCpoly_coeff_of_le (m + 1 + 1) (m + 1 + 1) le_rfl,
      hpCpoly_coeff_of_le (m + 1 + 1) (m + 1) (by omega)]
  rw [hpVpoly, coeff_sub, e1, e2]

/-- Factorial atoms for `n = m+1`: everything in terms of `F = (2m+3)!`. -/
theorem hp_fact_F4 (m : ℕ) :
    ((2 * m + 4).factorial : ℚ) = (2 * (m : ℚ) + 4) * ((2 * (m + 1) + 1).factorial : ℚ) := by
  rw [show 2 * m + 4 = 2 * (m + 1) + 1 + 1 by omega, Nat.factorial_succ (2 * (m + 1) + 1)]
  push_cast
  all_goals ring

theorem hp_fact_F5 (m : ℕ) :
    ((2 * (m + 1 + 1) + 1).factorial : ℚ) =
      (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) * ((2 * (m + 1) + 1).factorial : ℚ) := by
  rw [show 2 * (m + 1 + 1) + 1 = 2 * (m + 1) + 1 + 1 + 1 by omega,
    Nat.factorial_succ (2 * (m + 1) + 1 + 1), Nat.factorial_succ (2 * (m + 1) + 1)]
  push_cast
  all_goals ring

theorem hp_fact_F6 (m : ℕ) :
    ((2 * (m + 1) + 4).factorial : ℚ) =
      (2 * (m : ℚ) + 6) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) *
        ((2 * (m + 1) + 1).factorial : ℚ) := by
  rw [show 2 * (m + 1) + 4 = 2 * (m + 1) + 1 + 1 + 1 + 1 by omega,
    Nat.factorial_succ (2 * (m + 1) + 1 + 1 + 1), Nat.factorial_succ (2 * (m + 1) + 1 + 1),
    Nat.factorial_succ (2 * (m + 1) + 1)]
  push_cast
  all_goals ring

theorem hp_fact_f2 (m : ℕ) :
    ((m + 1 + 1).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
  rw [Nat.factorial_succ (m + 1)]
  push_cast
  all_goals ring

theorem hp_fact_f1 (m : ℕ) :
    ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ m]
  push_cast
  all_goals ring

/-- `u_{m+2,m+1} u_{m+1,m+1} = b_{m+1}² (2m+4)(2m+5)(2m+6)(m+2)²`. -/
theorem hpUU_one (m : ℕ) :
    hpResidueU (m + 1 + 1) (m + 1) * hpResidueU (m + 1) (m + 1) =
      (hpbN (m + 1) : ℚ) ^ 2 *
        ((2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 6) * ((m : ℚ) + 2) ^ 2) := by
  have hb := hpbN_factorial (m + 1)
  have hf1 : ((m + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm2 : (m : ℚ) + 2 ≠ 0 := by positivity
  rw [hpResidueU_subdiag (m + 1), hpResidueU_diag (m + 1), hp_fact_F6 m, ← hb, hp_fact_f2 m]
  field_simp
  all_goals ring

/-- `u_{m+2,m+2} u_{m+1,m} = b_{m+1}² (2m+4)²(2m+5)(m+1)²`. -/
theorem hpUU_two (m : ℕ) :
    hpResidueU (m + 1 + 1) (m + 1 + 1) * hpResidueU (m + 1) m =
      (hpbN (m + 1) : ℚ) ^ 2 *
        ((2 * (m : ℚ) + 4) ^ 2 * (2 * (m : ℚ) + 5) * ((m : ℚ) + 1) ^ 2) := by
  have hb := hpbN_factorial (m + 1)
  have hf : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℚ) + 2 ≠ 0 := by positivity
  rw [hpResidueU_diag (m + 1 + 1), hpResidueU_subdiag m, hp_fact_F5 m, hp_fact_F4 m, ← hb,
    hp_fact_f2 m, hp_fact_f1 m]
  field_simp
  all_goals ring

/-- `π_1 = v_{N-1} = b_n^2 (2n+1)(n+1)((n+1)(12n+17) + 21n+29)` (C7). -/
theorem hpPi_one (n : ℕ) :
    hpPi n 1 = (hpbN n : ℚ) ^ 2 * (2 * (n : ℚ) + 1) * ((n : ℚ) + 1) *
      (((n : ℚ) + 1) * (12 * (n : ℚ) + 17) + (21 * (n : ℚ) + 29)) := by
  rcases n with _ | m
  · -- n = 0: V_0 = 46 - 17 X
    have hU00 : hpResidueU 0 0 = -1 := by
      rw [hpResidueU_diag 0]
      norm_num
    have h4 : (2 * 0 + 4).factorial = 24 := rfl
    have hU10 : hpResidueU (0 + 1) 0 = -24 := by
      rw [hpResidueU_subdiag 0, h4]
      norm_num
    have hH1 : hpHarmonic (2 * 0 + 1) = 1 := by
      simp [hpHarmonic]
    have hH4 : hpHarmonic (2 * 0 + 4) = 25 / 12 := by
      norm_num [hpHarmonic, Finset.sum_range_succ]
    have hV00 : hpResidueV 0 0 = 1 := by
      have hH0 : hpHarmonic 0 = 0 := by simp [hpHarmonic]
      rw [hpResidueV_diag 0, hU00, hH0, hH1]
      norm_num
    have hV10 : hpResidueV (0 + 1) 0 = -22 := by
      have hH0 : hpHarmonic 0 = 0 := by simp [hpHarmonic]
      rw [hpResidueV_subdiag 0, hU10, hH0, hH4]
      norm_num
    have hc : hpPi 0 1 =
        hpResidueV (0 + 1) 0 * hpResidueU 0 0 - hpResidueV 0 0 * hpResidueU (0 + 1) 0 := by
      rw [hpPi, show 2 * 0 + 1 - 1 = 0 from rfl, hpVpoly, coeff_sub, mul_coeff_zero,
        mul_coeff_zero, hpBpoly_coeff_of_le (0 + 1) 0 (Nat.zero_le _),
        hpCpoly_coeff_of_le 0 0 le_rfl, hpBpoly_coeff_of_le 0 0 le_rfl,
        hpCpoly_coeff_of_le (0 + 1) 0 (Nat.zero_le _)]
    have hb0 : hpbN 0 = 1 := rfl
    rw [hc, hU00, hU10, hV00, hV10, hb0]
    norm_num
  · -- n = m+1
    have hc : hpPi (m + 1) 1 =
        (hpResidueV (m + 1 + 1) (m + 1) * hpResidueU (m + 1) (m + 1) +
          hpResidueV (m + 1 + 1) (m + 1 + 1) * hpResidueU (m + 1) m) -
        (hpResidueV (m + 1) m * hpResidueU (m + 1 + 1) (m + 1 + 1) +
          hpResidueV (m + 1) (m + 1) * hpResidueU (m + 1 + 1) (m + 1)) := by
      rw [hpPi, show 2 * (m + 1) + 1 - 1 = 2 * (m + 1) by omega]
      exact hpVpoly_coeff_second m
    -- harmonic atoms: H_m and G = H_{2m+3}
    have hHa : hpHarmonic (m + 1) = hpHarmonic m + 1 / ((m : ℚ) + 1) := hpHarmonic_add_one m
    have hHb : hpHarmonic (m + 1 + 1) =
        hpHarmonic m + 1 / ((m : ℚ) + 1) + 1 / ((m : ℚ) + 2) := by
      rw [hpHarmonic_add_one (m + 1), hpHarmonic_add_one m]
      push_cast
      all_goals ring
    have hHc : hpHarmonic (2 * m + 4) =
        hpHarmonic (2 * (m + 1) + 1) + 1 / (2 * (m : ℚ) + 4) := by
      rw [show 2 * m + 4 = 2 * (m + 1) + 1 + 1 by omega, hpHarmonic_add_one (2 * (m + 1) + 1)]
      push_cast
      all_goals ring
    have hHd : hpHarmonic (2 * (m + 1 + 1) + 1) =
        hpHarmonic (2 * (m + 1) + 1) + 1 / (2 * (m : ℚ) + 4) + 1 / (2 * (m : ℚ) + 5) := by
      rw [show 2 * (m + 1 + 1) + 1 = 2 * (m + 1) + 1 + 1 + 1 by omega,
        hpHarmonic_add_one (2 * (m + 1) + 1 + 1), hpHarmonic_add_one (2 * (m + 1) + 1)]
      push_cast
      all_goals ring
    have hHe : hpHarmonic (2 * (m + 1) + 4) =
        hpHarmonic (2 * (m + 1) + 1) + 1 / (2 * (m : ℚ) + 4) + 1 / (2 * (m : ℚ) + 5) +
          1 / (2 * (m : ℚ) + 6) := by
      rw [show 2 * (m + 1) + 4 = 2 * (m + 1) + 1 + 1 + 1 + 1 by omega,
        hpHarmonic_add_one (2 * (m + 1) + 1 + 1 + 1), hpHarmonic_add_one (2 * (m + 1) + 1 + 1),
        hpHarmonic_add_one (2 * (m + 1) + 1)]
      push_cast
      all_goals ring
    -- harmonic elimination (pure `ring`, no denominators cleared)
    have hδ : hpPi (m + 1) 1 =
        (hpResidueU (m + 1 + 1) (m + 1) * hpResidueU (m + 1) (m + 1)) *
          (3 - 1 / (2 * (m : ℚ) + 4) - 1 / (2 * (m : ℚ) + 5) - 1 / (2 * (m : ℚ) + 6)) +
        (hpResidueU (m + 1 + 1) (m + 1 + 1) * hpResidueU (m + 1) m) *
          (-3 - 2 / ((m : ℚ) + 1) - 2 / ((m : ℚ) + 2) - 1 / (2 * (m : ℚ) + 5)) := by
      rw [hc, hpResidueV_subdiag (m + 1), hpResidueV_diag (m + 1 + 1), hpResidueV_subdiag m,
        hpResidueV_diag (m + 1), hHe, hHd, hHc, hHb, hHa]
      ring
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (m : ℚ) + 2 ≠ 0 := by positivity
    have h4 : 2 * (m : ℚ) + 4 ≠ 0 := by positivity
    have h5 : 2 * (m : ℚ) + 5 ≠ 0 := by positivity
    have h6 : 2 * (m : ℚ) + 6 ≠ 0 := by positivity
    rw [hδ, hpUU_one m, hpUU_two m]
    push_cast
    field_simp
    all_goals ring

/-! ### S5: closed form, Q, W relation -/

/-- v13 eq:hp-Pn with `C(n+k,k-1)` written as `C(n+k,n+1)` (zero at `k=0`, no `ite`). -/
def hpPnCoeff (n k : ℕ) : ℤ :=
  -((-1 : ℤ) ^ k * ((2 * n + 1).choose k : ℤ) * ((n + k).choose k : ℤ) *
    ((12 * n + 17 : ℤ) * ((n + k).choose k : ℤ) +
      (21 * n + 29 : ℤ) * ((n + k).choose (n + 1) : ℤ)))

/-- `Q_n = V_n / b_n^2 = X^N P_n(1/X)`. -/
def hpQpoly (n : ℕ) : ℤ[X] :=
  ∑ i ∈ range (2 * n + 1 + 1), monomial i (hpPnCoeff n (2 * n + 1 - i))

theorem hpQpoly_coeff (n i : ℕ) (hi : i ≤ 2 * n + 1) :
    (hpQpoly n).coeff i = hpPnCoeff n (2 * n + 1 - i) := by
  have hi' : i < 2 * n + 1 + 1 := by omega
  simp [hpQpoly, Polynomial.coeff_monomial, hi, hi']

/-- `(n+1) C(n+k,n+1) = k C(n+k,k)` (C13). -/
theorem choose_n_succ_identity (n k : ℕ) :
    (n + 1) * (n + k).choose (n + 1) = k * (n + k).choose k := by
  rcases k with _ | j
  · have h0 : n.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
  · have h1 := Nat.add_one_mul_choose_eq (n + j) n
    have h2 := Nat.add_one_mul_choose_eq (n + j) j
    have h3 : (n + j).choose n = (n + j).choose j := Nat.choose_symm_add
    rw [h3] at h1
    rw [show n + (j + 1) = n + j + 1 by omega]
    calc (n + 1) * (n + j + 1).choose (n + 1)
        = (n + j + 1).choose (n + 1) * (n + 1) := Nat.mul_comm _ _
      _ = (n + j + 1) * (n + j).choose j := h1.symm
      _ = (n + j + 1).choose (j + 1) * (j + 1) := h2
      _ = (j + 1) * (n + j + 1).choose (j + 1) := Nat.mul_comm _ _

/-- `π_j = b_n² P_n(j)` for all `j ≤ N` (C8). -/
theorem hpPi_closed (n j : ℕ) (hj : j ≤ 2 * n + 1) :
    hpPi n j = (hpbN n : ℚ) ^ 2 * (hpPnCoeff n j : ℚ) := by
  obtain ⟨α, β, hshape⟩ :=
    hp_lagrange_two_param n (hpPi n) (fun ℓ h1 h2 => hpPi_moments n ℓ h1 h2)
  have e0 : hpPi n 0 = α := by
    rw [hshape 0 (Nat.zero_le _)]
    simp
  have e1 : hpPi n 1 = -((2 * (n : ℚ) + 1) * ((n : ℚ) + 1) ^ 2 * (α + β)) := by
    rw [hshape 1 (by omega), Nat.choose_one_right, Nat.choose_one_right]
    push_cast
    all_goals ring
  have hα : α = -((hpbN n : ℚ) ^ 2 * (12 * (n : ℚ) + 17)) := by
    rw [← e0, hpPi_zero]
  have key : ((2 * (n : ℚ) + 1) * ((n : ℚ) + 1)) *
      (β * ((n : ℚ) + 1) + (hpbN n : ℚ) ^ 2 * (21 * (n : ℚ) + 29)) = 0 := by
    have h1 := hpPi_one n
    linear_combination e1 - h1 - ((2 * (n : ℚ) + 1) * ((n : ℚ) + 1) ^ 2) * hα
  have hNn : (2 * (n : ℚ) + 1) * ((n : ℚ) + 1) ≠ 0 := by positivity
  have hβ : β * ((n : ℚ) + 1) = -((hpbN n : ℚ) ^ 2 * (21 * (n : ℚ) + 29)) := by
    have h := (mul_eq_zero.mp key).resolve_left hNn
    linear_combination h
  have hπ := hshape j hj
  have hcs : ((n : ℚ) + 1) * (((n + j).choose (n + 1) : ℕ) : ℚ) =
      (j : ℚ) * (((n + j).choose j : ℕ) : ℚ) := by
    exact_mod_cast choose_n_succ_identity n j
  have hP : (hpPnCoeff n j : ℚ) =
      -((-1 : ℚ) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) *
        ((12 * (n : ℚ) + 17) * (((n + j).choose j : ℕ) : ℚ) +
          (21 * (n : ℚ) + 29) * (((n + j).choose (n + 1) : ℕ) : ℚ))) := by
    unfold hpPnCoeff
    push_cast
    all_goals ring
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hmain : ((n : ℚ) + 1) * (hpPi n j - (hpbN n : ℚ) ^ 2 * (hpPnCoeff n j : ℚ)) = 0 := by
    rw [hP]
    linear_combination ((n : ℚ) + 1) * hπ
      + ((-1 : ℚ) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) *
          (((n : ℚ) + 1) * (((n + j).choose j : ℕ) : ℚ))) * hα
      + ((-1 : ℚ) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) *
          ((((n + j).choose j : ℕ) : ℚ) * (j : ℚ))) * hβ
      + ((-1 : ℚ) ^ j * (((2 * n + 1).choose j : ℕ) : ℚ) * (((n + j).choose j : ℕ) : ℚ) *
          ((hpbN n : ℚ) ^ 2 * (21 * (n : ℚ) + 29))) * hcs
  have h := (mul_eq_zero.mp hmain).resolve_left hn1
  linear_combination h

theorem hpVpoly_coeff_eq (n i : ℕ) (hi : i ≤ 2 * n + 1) :
    (hpVpoly n).coeff i = (hpbN n : ℚ) ^ 2 * ((hpQpoly n).coeff i : ℚ) := by
  rw [hpQpoly_coeff n i hi]
  have h := hpPi_closed n (2 * n + 1 - i) (by omega)
  rw [hpPi, show 2 * n + 1 - (2 * n + 1 - i) = i by omega] at h
  exact h

/-- V_coeff field. -/
theorem hpVpoly_coeff_closed (n : ℕ) :
    ∀ i, i ≤ 2 * n + 1 → (hpVpoly n).coeff i / (hpbN n : ℚ) ^ 2 = ((hpQpoly n).coeff i : ℚ) := by
  intro i hi
  have hb := hpbN_cast_ne_zero n
  rw [hpVpoly_coeff_eq n i hi]
  field_simp
  all_goals ring

/-- W_coeff field: `W_k / b^2 = -Σ_{j<k} Q_j/(k-j)^2` for `k ≤ N` (C9). -/
theorem hpWpoly_coeff_closed (n : ℕ) :
    ∀ k, k ≤ 2 * n + 1 →
      (hpWpoly n).coeff k / (hpbN n : ℚ) ^ 2 = -hpLi2ProductCoeff (hpQpoly n) k := by
  intro k hk
  have hb := hpbN_cast_ne_zero n
  have h := hpW_add_li2_conv n k (by omega)
  have hIco : (∑ i ∈ Ico k (2 * n + 1 + 1),
      if i ≤ k then (hpVpoly n).coeff i * (((k - i : ℕ) : ℚ))⁻¹ ^ 2 else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hki : k ≤ i := (Finset.mem_Ico.mp hi).1
    by_cases hik : i ≤ k
    · have hz : k - i = 0 := by omega
      rw [if_pos hik, hz]
      simp
    · rw [if_neg hik]
  have hsum : (∑ i ∈ range (2 * n + 1 + 1),
        if i ≤ k then (hpVpoly n).coeff i * (((k - i : ℕ) : ℚ))⁻¹ ^ 2 else 0) =
      (hpbN n : ℚ) ^ 2 * hpLi2ProductCoeff (hpQpoly n) k := by
    rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ 2 * n + 1 + 1 by omega), hIco, add_zero,
      hpLi2ProductCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    rw [if_pos hik.le, hpVpoly_coeff_eq n i (by omega)]
    ring
  rw [hsum] at h
  rw [div_eq_iff (pow_ne_zero 2 hb)]
  linear_combination h

/-- The actual integerization input (HPIntegralForm.lean:115). -/
def hpIntegerizationInput_actual (n : ℕ) :
    HPIntegerizationInput n (2 * n + 1) (hpbN n) where
  Q := hpQpoly n
  b_pos := hpbN_pos n
  W_degree := hpWpoly_natDegree_le n
  V_degree := hpVpoly_natDegree_le n
  W_coeff := hpWpoly_coeff_closed n
  V_coeff := hpVpoly_coeff_closed n

/-! ### S6: evaluation and `HPIntegralForm` -/

theorem int_poly_eval_inv_mul_pow {P : ℤ[X]} {N : ℕ} (hP : P.natDegree ≤ N)
    {a : ℤ} (ha : a ≠ 0) :
    ∃ x : ℤ, (a : ℚ) ^ N * (P.map (Int.castRingHom ℚ)).eval ((a : ℚ)⁻¹) = x := by
  refine ⟨∑ i ∈ range (N + 1), P.coeff i * a ^ (N - i), ?_⟩
  have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hlt : (P.map (Int.castRingHom ℚ)).natDegree < N + 1 :=
    lt_of_le_of_lt (natDegree_map_le.trans hP) (Nat.lt_succ_self N)
  rw [eval_eq_sum_range' hlt, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
  rw [coeff_map, eq_intCast, Int.cast_mul, Int.cast_pow]
  have hpow : (a : ℚ) ^ N = (a : ℚ) ^ (N - i) * (a : ℚ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hiN]
  have hai : (a : ℚ) ^ i ≠ 0 := pow_ne_zero _ haq
  rw [hpow, inv_pow]
  field_simp
  all_goals ring

theorem hpDR_eq_scale (n : ℕ) :
    hpDR n = ((hpIntegerizationScale (hpDenominator (2 * n + 1)) (hpbN n) : ℚ) : ℝ) := by
  simp only [hpDR, hpIntegerizationScale]
  rw [← hpDenominator_eq_lcmUpto]
  push_cast
  all_goals ring

theorem hpIntegralForm_of_ne_zero {a : ℤ} (ha : a ≠ 0) : HPIntegralForm a := by
  have key : ∀ n, ∃ x y : ℤ, hpLR a n = (x : ℝ) + (y : ℝ) * li2InvValue a := by
    intro n
    obtain ⟨WZ, VZ, hW, hV⟩ :=
      hp_integerization_input_certificate (hpIntegerizationInput_actual n)
    have hWdeg : WZ.natDegree ≤ 2 * n + 1 := by
      rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) WZ, hW]
      exact (natDegree_C_mul_le _ _).trans (hpWpoly_natDegree_le n)
    have hVdeg : VZ.natDegree ≤ 2 * n + 1 := by
      rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) VZ, hV]
      exact (natDegree_C_mul_le _ _).trans (hpVpoly_natDegree_le n)
    obtain ⟨x, hx⟩ := int_poly_eval_inv_mul_pow hWdeg ha
    obtain ⟨y, hy⟩ := int_poly_eval_inv_mul_pow hVdeg ha
    rw [hW, eval_mul, eval_C] at hx
    rw [hV, eval_mul, eval_C] at hy
    refine ⟨x, y, ?_⟩
    have hx' : (a : ℝ) ^ (2 * n + 1) *
        (((hpIntegerizationScale (hpDenominator (2 * n + 1)) (hpbN n) : ℚ) : ℝ) *
          (((hpWpoly n).eval ((a : ℚ)⁻¹) : ℚ) : ℝ)) = (x : ℝ) := by
      exact_mod_cast hx
    have hy' : (a : ℝ) ^ (2 * n + 1) *
        (((hpIntegerizationScale (hpDenominator (2 * n + 1)) (hpbN n) : ℚ) : ℝ) *
          (((hpVpoly n).eval ((a : ℚ)⁻¹) : ℚ) : ℝ)) = (y : ℝ) := by
      exact_mod_cast hy
    rw [hpLR, hpDR_eq_scale]
    linear_combination hx' + li2InvValue a * hy'
  choose Xs Ys h using key
  exact ⟨Xs, Ys, h⟩

theorem hpIntegralForm_of_range {a : ℤ} (ha : (12 : ℤ) ≤ a ∨ a ≤ -8) : HPIntegralForm a :=
  hpIntegralForm_of_ne_zero (by omega)

end

end Li2Lean.B4.HPVpolyIntegrality

/-! ======================================================================
    Producers.lean wiring (add `import Li2Lean.B4.HPVpolyIntegrality`):

    theorem hpIntegralInput_producer :
        ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
          Li2Lean.B4.TailAnalytic.HPIntegralForm a :=
      fun _ ha => Li2Lean.B4.HPVpolyIntegrality.hpIntegralForm_of_range ha
    ====================================================================== -/

#print axioms Li2Lean.B4.HPVpolyIntegrality.hpIntegralForm_of_ne_zero
