/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  Generated (compiled) -- M0: the explicit residue certificate for all n.
  Target file suggestion: Li2Lean/B4/ResidueCertificateAllN.lean
  (or append below `explicitResidueCertificate_zero` in ResidueTailBridge.lean).

  Paper: output/li2-alln-paper-v13/source/chapters/hp-tail.tex
    L12-18  Phi_n = prod_{r=n+1}^{3n+1}(w-r) / prod_{j=0}^n (w-j)^2
            = sum_j ( u_{n,j}/(w-j)^2 + v_{n,j}/(w-j) )
    L19     H_k = sum_{r=1}^k 1/r, H_0 = 0       (master: `hpHarmonic`)
    L20-22  u_{n,j} = -(3n+1-j)! / ((j!)^2 ((n-j)!)^3)
            v_{n,j} = u_{n,j} (3 H_{n-j} - 2 H_j - H_{3n+1-j})
    L26-27  B_n, C_n built from v, u  (=> W_n, V_n at L49-50)

  Route (no generic Hermite theorem, no rootMultiplicity):
    R := hpNumerator n - sum_j T_j,   T_j := (C u_j + C v_j * hpPole j) * hpOffPoly_j^2
    (1) for each j <= n: (X - j)^2 | R
        (a) i /= j: (X - j)^2 | T_i            (factor of hpOffPoly_i)
        (b) (N - T_j)(j) = 0, (N - T_j)'(j) = 0  =>  (X - j)^2 | N - T_j
            via value/log-derivative closed forms (factorials + harmonic sums)
    (2) pairwise coprime => prod_j (X - j)^2 | R
    (3) natDegree R <= 2n+1 < 2n+2 = natDegree prod  =>  R = 0.

  Mathlib name references are documented below.
  Names marked "checked" in B4-residues partial-fraction proof plan, section 2.1
  are not re-marked.
-/
import Li2Lean.B4.ResidueTailBridge

open Finset Polynomial

namespace Li2Lean.B4.ResidueTailBridge

noncomputable section

open Li2Lean.B4.Residues
theorem m0_Icc_eq_Ico_succ (a b : ℕ) :
    Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-! ## Part 2. Factorial products -/

/-- `a! * prod_{t<c} (a+t+1) = (a+c)!`, division-free. -/
theorem prod_shift_factorial (a c : ℕ) :
    (a.factorial : ℚ) * ∏ t ∈ Finset.range c, (((a + t + 1 : ℕ)) : ℚ) =
      ((a + c).factorial : ℚ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih,
      show a + (c + 1) = (a + c) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring

/-- `prod_{t<c} (t+1) = c!` over ℚ. -/
theorem prod_range_cast_succ (c : ℕ) :
    ∏ t ∈ Finset.range c, (((t + 1 : ℕ)) : ℚ) = (c.factorial : ℚ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- Numerator at a pole, `hp-tail.tex:14,21`:
    `(n-j)! * N(j) = -(3n+1-j)!`. -/
theorem eval_hpNumerator_at_pole (n j : ℕ) (hj : j ≤ n) :
    ((n - j).factorial : ℚ) * (hpNumerator n).eval (j : ℚ) =
      -((3 * n + 1 - j).factorial : ℚ) := by
  unfold hpNumerator
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [m0_Icc_eq_Ico_succ, Finset.prod_Ico_eq_prod_range,
    show 3 * n + 1 + 1 - (n + 1) = 2 * n + 1 by omega]
  have hterm : ∀ t ∈ Finset.range (2 * n + 1),
      (j : ℚ) - ((n + 1 + t : ℕ) : ℚ) = -(((n - j + t + 1 : ℕ)) : ℚ) := by
    intro t _
    push_cast [Nat.cast_sub hj]
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.card_range,
    Odd.neg_one_pow ⟨n, rfl⟩]
  have h := prod_shift_factorial (n - j) (2 * n + 1)
  rw [show n - j + (2 * n + 1) = 3 * n + 1 - j by omega] at h
  linear_combination (-1 : ℚ) * h

/-- Removed-pole product at its own pole, `hp-tail.tex:14-18`:
    `prod_{i<=n, i/=j} (j - i) = j! * (-1)^(n-j) * (n-j)!`. -/
theorem eval_hpOffPoly_at_pole (n j : ℕ) (hj : j ≤ n) :
    (hpOffPoly n j).eval (j : ℚ) =
      (j.factorial : ℚ) * ((-1 : ℚ) ^ (n - j) * ((n - j).factorial : ℚ)) := by
  unfold hpOffPoly hpPole
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  set g : ℕ → ℚ := fun i => if i = j then (1 : ℚ) else (j : ℚ) - (i : ℚ)
    with hg
  have h1 : ∏ i ∈ (Finset.range (n + 1)).erase j, ((j : ℚ) - (i : ℚ)) =
      ∏ i ∈ (Finset.range (n + 1)).erase j, g i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hg, hij]
  have h2 : ∏ i ∈ (Finset.range (n + 1)).erase j, g i =
      ∏ i ∈ Finset.range (n + 1), g i :=
    Finset.prod_erase (Finset.range (n + 1)) (by simp [hg])

  have hA : ∏ i ∈ Finset.range j, g i = (j.factorial : ℚ) := by
    rw [← Finset.prod_range_reflect g j, ← prod_range_cast_succ j]
    apply Finset.prod_congr rfl
    intro t ht
    have ht' : t < j := Finset.mem_range.mp ht
    have hne : j - 1 - t ≠ j := by omega
    have hnat : j - 1 - t + (t + 1) = j := by omega
    have hcast : ((j - 1 - t : ℕ) : ℚ) + ((t : ℚ) + 1) = (j : ℚ) := by
      exact_mod_cast hnat
    simp only [hg]
    rw [if_neg hne]
    push_cast
    linarith
  have hB : ∏ t ∈ Finset.range (n - j + 1), g (j + t) =
      (-1 : ℚ) ^ (n - j) * ((n - j).factorial : ℚ) := by
    rw [Finset.prod_range_succ']
    have h0 : g (j + 0) = 1 := by simp [hg]
    have hs : ∀ t ∈ Finset.range (n - j), g (j + (t + 1)) =
        -(((t + 1 : ℕ)) : ℚ) := by
      intro t _
      have hne : j + (t + 1) ≠ j := by omega
      simp only [hg]
      rw [if_neg hne]
      push_cast
      ring
    rw [h0, mul_one, Finset.prod_congr rfl hs, Finset.prod_neg,
      Finset.card_range, prod_range_cast_succ]
  rw [h1, h2, show n + 1 = j + (n - j + 1) by omega, Finset.prod_range_add,
    hA, hB]

/-- Squared form used by `u_{n,j}`, `hp-tail.tex:21`. -/
theorem eval_hpOffPoly_sq_at_pole (n j : ℕ) (hj : j ≤ n) :
    ((hpOffPoly n j).eval (j : ℚ)) ^ 2 =
      (j.factorial : ℚ) ^ 2 * ((n - j).factorial : ℚ) ^ 2 := by
  rw [eval_hpOffPoly_at_pole n j hj]
  have hsq : ((-1 : ℚ) ^ (n - j)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  linear_combination
    ((j.factorial : ℚ) ^ 2 * ((n - j).factorial : ℚ) ^ 2) * hsq

/-! ## Part 3. Harmonic sums (`hp-tail.tex:19`) -/

theorem hpHarmonic_succ (k : ℕ) :
    hpHarmonic (k + 1) = hpHarmonic k + (((k + 1 : ℕ)) : ℚ)⁻¹ := by
  unfold hpHarmonic
  rw [Finset.sum_range_succ]

/-- `sum_{t<c} 1/(a+t+1) = H_{a+c} - H_a`. -/
theorem sum_shift_inv (a c : ℕ) :
    ∑ t ∈ Finset.range c, (((a + t + 1 : ℕ)) : ℚ)⁻¹ =
      hpHarmonic (a + c) - hpHarmonic a := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih, show a + (c + 1) = (a + c) + 1 by omega,
      hpHarmonic_succ]
    ring

/-- Log-derivative of the numerator at `j`:
    `sum_{r=n+1}^{3n+1} 1/(j-r) = H_{n-j} - H_{3n+1-j}`. -/
theorem sum_inv_numerator (n j : ℕ) (hj : j ≤ n) :
    ∑ r ∈ Finset.Icc (n + 1) (3 * n + 1), ((j : ℚ) - (r : ℚ))⁻¹ =
      hpHarmonic (n - j) - hpHarmonic (3 * n + 1 - j) := by
  rw [m0_Icc_eq_Ico_succ, Finset.sum_Ico_eq_sum_range,
    show 3 * n + 1 + 1 - (n + 1) = 2 * n + 1 by omega]
  have hterm : ∀ t ∈ Finset.range (2 * n + 1),
      ((j : ℚ) - ((n + 1 + t : ℕ) : ℚ))⁻¹ =
        -((((n - j + t + 1 : ℕ)) : ℚ))⁻¹ := by
    intro t _
    rw [← inv_neg]
    congr 1
    push_cast [Nat.cast_sub hj]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sum_shift_inv,
    show n - j + (2 * n + 1) = 3 * n + 1 - j by omega]
  ring

/-- `sum_{i<j} 1/(j-i) = H_j`. -/
theorem sum_inv_below (j : ℕ) :
    ∑ i ∈ Finset.range j, ((j : ℚ) - (i : ℚ))⁻¹ = hpHarmonic j := by
  unfold hpHarmonic
  rw [← Finset.sum_range_reflect (fun i : ℕ => ((j : ℚ) - (i : ℚ))⁻¹) j]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t < j := Finset.mem_range.mp ht
  have hnat : j - 1 - t + (t + 1) = j := by omega
  have hcast : ((j - 1 - t : ℕ) : ℚ) + ((t : ℚ) + 1) = (j : ℚ) := by
    exact_mod_cast hnat
  show ((j : ℚ) - ((j - 1 - t : ℕ) : ℚ))⁻¹ = (((t + 1 : ℕ)) : ℚ)⁻¹
  congr 1
  push_cast
  linarith

/-- `sum_{t<=m} 1/(j-(j+t)) = -H_m` (the `t=0` term is `1/0 = 0` in Lean). -/
theorem sum_inv_above (j m : ℕ) :
    ∑ t ∈ Finset.range (m + 1), ((j : ℚ) - ((j + t : ℕ) : ℚ))⁻¹ =
      -hpHarmonic m := by
  have h0 : ((j : ℚ) - ((j + 0 : ℕ) : ℚ))⁻¹ = 0 := by simp
  rw [Finset.sum_range_succ', h0, add_zero]
  unfold hpHarmonic
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← inv_neg]
  congr 1
  push_cast
  ring

/-- Log-derivative of the removed-pole product at `j`:
    `sum_{i<=n, i/=j} 1/(j-i) = H_j - H_{n-j}`. -/
theorem sum_inv_offPoly (n j : ℕ) (hj : j ≤ n) :
    ∑ i ∈ (Finset.range (n + 1)).erase j, ((j : ℚ) - (i : ℚ))⁻¹ =
      hpHarmonic j - hpHarmonic (n - j) := by
  rw [Finset.sum_erase (Finset.range (n + 1))
      (f := fun i : ℕ => ((j : ℚ) - (i : ℚ))⁻¹) (a := j) (by simp)]

  rw [show n + 1 = j + (n - j + 1) by omega, Finset.sum_range_add,
    sum_inv_below, sum_inv_above]
  ring


end

end Li2Lean.B4.ResidueTailBridge
