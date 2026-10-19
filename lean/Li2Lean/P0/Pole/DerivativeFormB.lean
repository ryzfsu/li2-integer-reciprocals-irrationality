/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Pole.BinomialPoly
namespace Li2Lean.P0.Pole
open Polynomial Finset
noncomputable section

theorem bp_succR (N : ℤ) (n : ℕ) :
    bp N (n + 1) =
      C (((n + 1 : ℕ) : ℚ)⁻¹) * (X + C (N : ℚ) - C (n : ℚ)) * bp N n := by
  unfold bp
  rw [descPochhammer_succ_right, Polynomial.mul_comp]
  simp only [Polynomial.C_comp, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.sub_comp, Nat.factorial_succ]
  have hfac :
      C ((((n + 1 : ℕ) * n.factorial : ℕ) : ℚ)⁻¹) =
        C (((n + 1 : ℕ) : ℚ)⁻¹) * C ((n.factorial : ℚ)⁻¹) := by
    rw [← C_mul]
    congr 1
    push_cast
    field_simp
  rw [hfac]
  have hncomp :
      ((n : ℚ[X]).comp (X + C (N : ℚ))) = C (n : ℚ) := by simp
  rw [hncomp]
  ring

theorem bp_shiftR (M : ℤ) (n : ℕ) :
    (X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n =
      (X + C ((M + 1 : ℤ) : ℚ)) * bp M n := by
  have hp := bp_pascal M n
  rw [bp_succR (M + 1) n, bp_succR M n] at hp
  have hnq : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hmul := congrArg (fun p : ℚ[X] => C ((n + 1 : ℕ) : ℚ) * p) hp
  have hcancel :
      C ((n + 1 : ℕ) : ℚ) * C (((n + 1 : ℕ) : ℚ)⁻¹) = (1 : ℚ[X]) := by
    rw [← C_mul]
    congr 1
    rw [mul_inv_cancel₀ hnq]
    simp
  rw [mul_add] at hmul
  have hL :
      C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            ((X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n)) =
        (X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n := by
    rw [← mul_assoc, hcancel, one_mul]
  have hR :
      C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            ((X + C (M : ℚ) - C (n : ℚ)) * bp M n)) =
        (X + C (M : ℚ) - C (n : ℚ)) * bp M n := by
    rw [← mul_assoc, hcancel, one_mul]
  have hL' :
      C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            (X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n) =
        (X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n := by
    calc
      _ = C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            ((X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n)) := by ring
      _ = _ := hL
  have hR' :
      C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            (X + C (M : ℚ) - C (n : ℚ)) * bp M n) =
        (X + C (M : ℚ) - C (n : ℚ)) * bp M n := by
    calc
      _ = C ((n + 1 : ℕ) : ℚ) *
          (C (((n + 1 : ℕ) : ℚ)⁻¹) *
            ((X + C (M : ℚ) - C (n : ℚ)) * bp M n)) := by ring
      _ = _ := hR
  rw [hL', hR'] at hmul
  have hcast : ((M + 1 : ℤ) : ℚ) = (M : ℚ) + 1 := by norm_num
  rw [hcast] at hmul
  have hncast : C ((n + 1 : ℕ) : ℚ) = C (1 : ℚ) + C (n : ℚ) := by
    norm_num
    ring
  rw [hncast] at hmul
  have hMcast : C ((M : ℚ) + 1) = C (M : ℚ) + C (1 : ℚ) := by
    rw [← map_add]
  rw [hMcast] at hmul
  simp only [Polynomial.C_1, one_mul, mul_one] at hmul
  calc
    (X + C ((M + 1 : ℤ) : ℚ) - C (n : ℚ)) * bp (M + 1) n =
        (X + (C (M : ℚ) + 1) - C (n : ℚ)) * bp (M + 1) n := by
          rw [hcast, hMcast]
          simp
    _ = (X + C (M : ℚ) - C (n : ℚ)) * bp M n +
          (1 + C (n : ℚ)) * bp M n := hmul
    _ = (X + C ((M + 1 : ℤ) : ℚ)) * bp M n := by
          rw [hcast, hMcast]
          simp
          ring

theorem reflect_step (N M : ℤ) (n : ℕ)
    (hM : (M : ℚ) = -(N : ℚ) + (n : ℚ))
    (hs : (X + C (M : ℚ) - C (n : ℚ)) * bp M n =
      (X + C (M : ℚ)) * bp (M - 1) n) :
    C ((↑(n + 1) : ℚ)⁻¹) *
          (-X + C (N : ℚ) - C (n : ℚ)) *
            (C ((-1 : ℚ) ^ n) * bp (M - 1) n) =
      C (-(-1 : ℚ) ^ n) *
        (C ((↑(n + 1) : ℚ)⁻¹) *
          (X + C (M : ℚ) - C (n : ℚ)) * bp M n) := by
  have hfac : -X + C (N : ℚ) - C (n : ℚ) =
      -(X + C (M : ℚ)) := by
    have hc : C (M : ℚ) = -C (N : ℚ) + C (n : ℚ) := by
      rw [hM]
      rw [← map_neg, ← map_add]
    rw [hc]
    ring
  rw [hfac]
  have hpowC : C (-(-1 : ℚ) ^ n) = -C ((-1 : ℚ) ^ n) := by
    rw [map_neg]
  calc
    C ((↑(n + 1) : ℚ)⁻¹) *
          -(X + C (M : ℚ)) *
            (C ((-1 : ℚ) ^ n) * bp (M - 1) n) =
      C (-(-1 : ℚ) ^ n) *
        (C ((↑(n + 1) : ℚ)⁻¹) *
          ((X + C (M : ℚ) - C (n : ℚ)) * bp M n)) := by
            rw [hs, hpowC]
            ring
    _ = C (-(-1 : ℚ) ^ n) *
        (C ((↑(n + 1) : ℚ)⁻¹) *
          (X + C (M : ℚ) - C (n : ℚ)) * bp M n) := by ac_rfl

set_option maxHeartbeats 1000000 in
theorem bp_reflect2 (N : ℤ) (n : ℕ) :
    (bp N n).comp (-X) =
      C ((-1 : ℚ) ^ n) * bp (-N + (n : ℤ) - 1) n := by
  induction n with
  | zero => simp [bp]
  | succ n ih =>
      rw [bp_succR, Polynomial.mul_comp, ih, bp_succR, Polynomial.mul_comp]
      simp only [Polynomial.C_comp, Polynomial.add_comp, Polynomial.X_comp,
        Polynomial.sub_comp]
      have hparam :
          -N + ((n + 1 : ℕ) : ℤ) - 1 = -N + (n : ℤ) := by
        push_cast
        ring
      rw [hparam]
      have hM : (-N + (n : ℤ) - 1 : ℤ) + 1 = -N + (n : ℤ) := by ring
      have hs := bp_shiftR (-N + (n : ℤ) - 1) n
      rw [hM] at hs
      have hs' := reflect_step N (-N + (n : ℤ)) n (by
        push_cast
        ring) hs
      have hpow : (-1 : ℚ) ^ (n + 1) = -(-1 : ℚ) ^ n := by
        rw [pow_succ]
        ring
      rw [hpow]
      simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs'

theorem derivative_bp_formB (N : ℤ) (n : ℕ) :
    derivative (bp N n) =
      ∑ r ∈ Icc 1 n, C ((r : ℚ)⁻¹) * bp (N - (r : ℤ)) (n - r) := by
  by_cases hn : n = 0
  · subst n
    simp [bp]
  let N' : ℤ := -N + (n : ℤ) - 1
  have href := bp_reflect2 N' n
  have hder := congrArg derivative href
  rw [derivative_comp] at hder
  have hA := derivative_bp_formA N' n
  have hAc := congrArg (fun p : ℚ[X] => p.comp (-X)) hA
  rw [Polynomial.sum_comp] at hAc
  simp only [Polynomial.mul_comp, Polynomial.C_comp] at hAc
  have hcomp (j : ℕ) (hj : j ≤ n) :
      (bp N' (n - j)).comp (-X) =
        C ((-1 : ℚ) ^ (n - j)) * bp (N - (j : ℤ)) (n - j) := by
    have hrf := bp_reflect2 N' (n - j)
    have hpar : -N' + ((n - j : ℕ) : ℤ) - 1 = N - (j : ℤ) := by
      dsimp [N']
      rw [Nat.cast_sub hj]
      ring
    rw [hpar] at hrf
    exact hrf
  have hAc' :
      (derivative (bp N' n)).comp (-X) =
        ∑ j ∈ Icc 1 n,
          C ((-1 : ℚ) ^ (j - 1) / j) *
            (C ((-1 : ℚ) ^ (n - j)) * bp (N - (j : ℤ)) (n - j)) := by
    calc
      _ = (∑ j ∈ Icc 1 n,
          C ((-1 : ℚ) ^ (j - 1) / j) * bp N' (n - j)).comp (-X) := by
            rw [hA]
      _ = _ := by
            rw [Polynomial.sum_comp]
            simp only [Polynomial.mul_comp, Polynomial.C_comp]
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcomp j (Finset.mem_Icc.mp hj).2]
  have hleft :
      (derivative (bp N' n)).comp (-X) =
        -C ((-1 : ℚ) ^ n) * derivative (bp N n) := by
    have hparamN : -N' + (n : ℤ) - 1 = N := by
      dsimp [N']
      ring
    rw [hparamN] at href
    have hcompder :
        derivative ((bp N' n).comp (-X)) =
          -(derivative (bp N' n)).comp (-X) := by
      rw [Polynomial.derivative_comp]
      simp
    rw [href] at hcompder
    rw [Polynomial.derivative_mul] at hcompder
    have hpowC : derivative (C ((-1 : ℚ) ^ n)) = 0 := by simp
    rw [hpowC, zero_mul, zero_add] at hcompder
    have hcompder' :
        C ((-1 : ℚ) ^ n) * derivative (bp N n) =
          -(derivative (bp N' n)).comp (-X) := by
      simpa using hcompder
    calc
      (derivative (bp N' n)).comp (-X) =
          -(-(derivative (bp N' n)).comp (-X)) := by ring
      _ = -(C ((-1 : ℚ) ^ n) * derivative (bp N n)) := by
        rw [hcompder']
      _ = -C ((-1 : ℚ) ^ n) * derivative (bp N n) := by ring
  rw [hleft] at hAc'
  have hsum :
      -C ((-1 : ℚ) ^ n) * derivative (bp N n) =
        ∑ j ∈ Icc 1 n,
          C ((-1 : ℚ) ^ (j - 1) / j) *
            (C ((-1 : ℚ) ^ (n - j)) * bp (N - (j : ℤ)) (n - j)) := hAc'
  have hsign (j : ℕ) (hj : j ∈ Icc 1 n) :
      C ((-1 : ℚ) ^ (j - 1) / j) * C ((-1 : ℚ) ^ (n - j)) =
        -C ((-1 : ℚ) ^ n) * C ((j : ℚ)⁻¹) := by
    have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hjpos)
    have he : j - 1 + (n - j) = n - 1 := by omega
    simp only [← C_mul, ← map_neg]
    congr 1
    rw [div_eq_mul_inv]
    have hp : (-1 : ℚ) ^ (n - 1) = -(-1 : ℚ) ^ n := by
      have hn' : n = (n - 1) + 1 := by omega
      calc
        (-1 : ℚ) ^ (n - 1) = -((-1 : ℚ) ^ (n - 1) * (-1 : ℚ)) := by ring
        _ = -((-1 : ℚ) ^ ((n - 1) + 1)) := by rw [pow_succ]
        _ = -(-1 : ℚ) ^ n := by
          exact congrArg (fun t : ℕ => -((-1 : ℚ) ^ t)) hn'.symm
    have hpowmul :
        (-1 : ℚ) ^ (j - 1) * (-1 : ℚ) ^ (n - j) =
          (-1 : ℚ) ^ (n - 1) := by
      rw [← pow_add, he]
    calc
      (-1 : ℚ) ^ (j - 1) * (j : ℚ)⁻¹ * (-1 : ℚ) ^ (n - j) =
          ((-1 : ℚ) ^ (j - 1) * (-1 : ℚ) ^ (n - j)) * (j : ℚ)⁻¹ := by ring
      _ = (-1 : ℚ) ^ (n - 1) * (j : ℚ)⁻¹ := by rw [hpowmul]
      _ = (-(-1 : ℚ) ^ n) * (j : ℚ)⁻¹ := by rw [hp]
      _ = -(-1 : ℚ) ^ n * (j : ℚ)⁻¹ := by ring
  have hsum' :
      -C ((-1 : ℚ) ^ n) * derivative (bp N n) =
        -C ((-1 : ℚ) ^ n) *
          (∑ j ∈ Icc 1 n, C ((j : ℚ)⁻¹) * bp (N - (j : ℤ)) (n - j)) := by
    calc
      -C ((-1 : ℚ) ^ n) * derivative (bp N n) =
          ∑ j ∈ Icc 1 n,
            C ((-1 : ℚ) ^ (j - 1) / j) *
              (C ((-1 : ℚ) ^ (n - j)) * bp (N - (j : ℤ)) (n - j)) := hsum
      _ = ∑ j ∈ Icc 1 n,
          (-C ((-1 : ℚ) ^ n) * C ((j : ℚ)⁻¹)) *
            bp (N - (j : ℤ)) (n - j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← hsign j hj]
              ring
      _ = -C ((-1 : ℚ) ^ n) *
          (∑ j ∈ Icc 1 n,
            C ((j : ℚ)⁻¹) * bp (N - (j : ℤ)) (n - j)) := by
              calc
                _ = ∑ j ∈ Icc 1 n,
                    (-C ((-1 : ℚ) ^ n)) *
                      (C ((j : ℚ)⁻¹) * bp (N - (j : ℤ)) (n - j)) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                _ = _ := by rw [Finset.mul_sum]
  have hnonzero : C ((-1 : ℚ) ^ n) ≠ 0 := by
    simp
  have hnonzero' : -C ((-1 : ℚ) ^ n) ≠ 0 := neg_ne_zero.mpr hnonzero
  exact mul_left_cancel₀ hnonzero' hsum'

end
end Li2Lean.P0.Pole
