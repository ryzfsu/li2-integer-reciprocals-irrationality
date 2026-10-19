/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.AllN.ProducerAssembly
import Li2Lean.B4.HPIntegralForm
import Li2Lean.B4.HPNoAdjacentActual
import Li2Lean.B4.NegativeContourTyped
import Li2Lean.B4.NegativeTailElementary

set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues
open Li2Lean.B4.NegativeContour

/-!
Construction-bound decay glue for the three exceptional negative bases in
v13 `hp-tail.tex:198-220, 258-410, 411-475`.  The contour certificate gives
the actual `hpBpoly` bound with a `(n+1)^k` factor; the beta remainder
envelope is kept as a separate input until the all-n beta producer is merged.
-/

def hpContourGamma : ℝ := Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16

theorem hpContour_exp_4004_le :
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) ≤
      (27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000) := by
  have h1 : Real.exp (4 * (1 + 1 / 1000 : ℝ)) =
      Real.exp 1 ^ 4 * Real.exp (1 / 250) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1 <;> norm_num
  have h3 : Real.exp (1 / 250 : ℝ) ≤ 1008 / 1000 := by
    have h := Real.abs_exp_sub_one_le (x := (1 / 250 : ℝ)) (by norm_num)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 250)] at h
    linarith [(abs_le.mp h).2]
  have h4 : Real.exp 1 ^ 4 ≤ (27182818286 / 10 ^ 10 : ℝ) ^ 4 := by
    have h := Real.exp_one_lt_d9
    have h' : Real.exp 1 ≤ (27182818286 / 10 ^ 10 : ℝ) := by
      norm_num at h ⊢
      linarith
    exact pow_le_pow_left₀ (Real.exp_pos 1).le h' 4
  rw [h1]
  exact mul_le_mul h4 h3 (Real.exp_pos _).le (by norm_num)

theorem hpContourGamma_nonneg : 0 ≤ hpContourGamma := by
  unfold hpContourGamma
  positivity

theorem hpContourDR_upper : ∀ᶠ n : ℕ in atTop,
    hpDR n ≤ Real.exp (2 * (1 + 1 / 1000 : ℝ)) *
      (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    hp_lcmUpto_log_upper_one_thousandth
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  set ε : ℝ := 1 + 1 / 1000 with hε
  have hlog := hN (2 * n + 1) (by omega)
  have hdpos : (0 : ℝ) < Nat.lcmUpto (2 * n + 1) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have hd : (Nat.lcmUpto (2 * n + 1) : ℝ) ≤
      Real.exp (ε * (2 * n + 1)) := by
    rw [← Real.log_le_iff_le_exp hdpos]
    push_cast at hlog
    linarith
  have hb : (4 : ℝ) ^ n ≤ (2 * n + 1 : ℝ) * hpbN n := by
    calc
      (4 : ℝ) ^ n ≤ (2 * n + 1 : ℝ) * Nat.centralBinom n := by
        exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
      _ ≤ (2 * n + 1 : ℝ) * hpbN n := by
        unfold hpbN
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact_mod_cast
          (Nat.mul_le_mul_left (2 * n + 1)
            (Nat.choose_le_choose n (by omega : 2 * n ≤ 2 * n + 1)))
  have hbpos : (0 : ℝ) < hpbN n := by
    unfold hpbN
    exact_mod_cast Nat.choose_pos (by omega)
  have hexp : Real.exp (ε * (2 * n + 1)) ^ 2 =
      Real.exp (2 * ε) * Real.exp (4 * ε) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1 <;> push_cast <;> ring
  have h16 : (16 : ℝ) ^ n ≤
      (2 * n + 1 : ℝ) ^ 2 * (hpbN n : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 ^ n) hb 2
    calc
      (16 : ℝ) ^ n = ((4 : ℝ) ^ n) ^ 2 := by
        calc
          (16 : ℝ) ^ n = ((4 : ℝ) ^ 2) ^ n := by norm_num
          _ = (4 : ℝ) ^ (2 * n) := by rw [← pow_mul]
          _ = (4 : ℝ) ^ (n * 2) := by congr 1 <;> omega
          _ = ((4 : ℝ) ^ n) ^ 2 := by rw [pow_mul]
      _ ≤ ((2 * n + 1 : ℝ) * hpbN n) ^ 2 := h
      _ = _ := by ring
  unfold hpDR hpContourGamma
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (hpbN n : ℝ) ^ 2)]
  calc
    (Nat.lcmUpto (2 * n + 1) : ℝ) ^ 2 ≤
        Real.exp (ε * (2 * n + 1)) ^ 2 :=
      pow_le_pow_left₀ hdpos.le hd 2
    _ = Real.exp (2 * ε) * Real.exp (4 * ε) ^ n := hexp
    _ = Real.exp (2 * ε) *
        ((Real.exp (4 * ε) / 16) ^ n * 16 ^ n) := by
      rw [div_pow]
      field_simp
    _ ≤ Real.exp (2 * ε) *
        ((Real.exp (4 * ε) / 16) ^ n *
          ((2 * n + 1 : ℝ) ^ 2 * (hpbN n : ℝ) ^ 2)) := by
      gcongr
    _ = _ := by ring

theorem hpBR_ratCast (n : ℕ) (z : ℚ) :
    hpBR n (z : ℝ) = ((Polynomial.eval z (hpBpoly n) : ℚ) : ℝ) := by
  simp [hpBR, hpBpoly, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

private theorem hpBR_eq_hpBRealAt (a : ℤ) (n : ℕ) :
    hpBR n ((a : ℝ)⁻¹) = hpBRealAt a n := by
  have hz : (a : ℝ)⁻¹ = (((a : ℚ)⁻¹ : ℚ) : ℝ) := by simp
  rw [hz, hpBR_ratCast]
  rfl

private theorem hpDR_nonneg_local (n : ℕ) : 0 ≤ hpDR n := by
  have hd : 0 < (Nat.lcmUpto (2 * n + 1) : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have hb : 0 < (hpbN n : ℝ) := by
    unfold hpbN
    exact_mod_cast Nat.choose_pos (by omega)
  unfold hpDR
  positivity

private theorem hpCasoratian_decomp_cast (n : ℕ) (z : ℚ) (ell li : ℝ) :
    (((Polynomial.eval z (hpBpoly (n + 1)) : ℚ) : ℝ) *
        (((Polynomial.eval z (hpApoly n) : ℚ) : ℝ) +
          ((Polynomial.eval z (hpBpoly n) : ℚ) : ℝ) * ell +
          ((Polynomial.eval z (hpCpoly n) : ℚ) : ℝ) * li) -
      ((Polynomial.eval z (hpBpoly n) : ℚ) : ℝ) *
        (((Polynomial.eval z (hpApoly (n + 1)) : ℚ) : ℝ) +
          ((Polynomial.eval z (hpBpoly (n + 1)) : ℚ) : ℝ) * ell +
          ((Polynomial.eval z (hpCpoly (n + 1)) : ℚ) : ℝ) * li)) =
      ((Polynomial.eval z (hpWpoly n) : ℚ) : ℝ) +
        ((Polynomial.eval z (hpVpoly n) : ℚ) : ℝ) * li := by
  have hW : Polynomial.eval z (hpWpoly n) =
      Polynomial.eval z (hpBpoly (n + 1)) * Polynomial.eval z (hpApoly n) -
        Polynomial.eval z (hpBpoly n) * Polynomial.eval z (hpApoly (n + 1)) := by
    simp [hpWpoly]
  have hV : Polynomial.eval z (hpVpoly n) =
      Polynomial.eval z (hpBpoly (n + 1)) * Polynomial.eval z (hpCpoly n) -
        Polynomial.eval z (hpBpoly n) * Polynomial.eval z (hpCpoly (n + 1)) := by
    simp [hpVpoly]
  rw [hW, hV]
  push_cast
  ring

theorem hpLR_eq_casoratian_of_v13_input {a : ℤ}
    (I : HPNoAdjacentV13Input a) (n : ℕ) :
    hpLR a n = (a : ℝ) ^ (2 * n + 1) * hpDR n *
      (hpBRealAt a (n + 1) * hpRR n ((a : ℝ)⁻¹) -
        hpBRealAt a n * hpRR (n + 1) ((a : ℝ)⁻¹)) := by
  let zq : ℚ := (a : ℚ)⁻¹
  let z : ℝ := (a : ℝ)⁻¹
  let ell : ℝ := -Real.log (1 - z)
  have hcas := hpCasoratian_decomp_cast n zq ell (li2InvValue a)
  have htail0 := I.tail_representation n
  have htail1 := I.tail_representation (n + 1)
  have hcas' :
      hpBRealAt a (n + 1) * hpRR n z - hpBRealAt a n * hpRR (n + 1) z =
        ((Polynomial.eval zq (hpWpoly n) : ℚ) : ℝ) +
          ((Polynomial.eval zq (hpVpoly n) : ℚ) : ℝ) * li2InvValue a := by
    rw [← htail0, ← htail1]
    simpa [zq, z, ell, hpTailCombinationAt, hpARealAt, hpBRealAt,
      hpCRealAt] using hcas
  unfold hpLR
  rw [← hcas']

theorem abs_sub_le_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

theorem hpLR_abs_le_of_v13_input {a : ℤ}
    (I : HPNoAdjacentV13Input a) (n : ℕ) :
    |hpLR a n| ≤ |(a : ℝ)| ^ (2 * n + 1) * hpDR n *
      (|hpBRealAt a (n + 1)| * |hpRR n ((a : ℝ)⁻¹)| +
        |hpBRealAt a n| * |hpRR (n + 1) ((a : ℝ)⁻¹)|) := by
  rw [hpLR_eq_casoratian_of_v13_input I n]
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (hpDR_nonneg_local n)]
  have hsub := abs_sub_le_add_abs
    (hpBRealAt a (n + 1) * hpRR n ((a : ℝ)⁻¹))
    (hpBRealAt a n * hpRR (n + 1) ((a : ℝ)⁻¹))
  rw [abs_mul, abs_mul] at hsub
  have hscale : 0 ≤ |(a : ℝ)| ^ (2 * n + 1) * hpDR n :=
    mul_nonneg (by positivity) (hpDR_nonneg_local n)
  calc
    |(a : ℝ)| ^ (2 * n + 1) * hpDR n *
        |hpBRealAt a (n + 1) * hpRR n ((a : ℝ)⁻¹) -
          hpBRealAt a n * hpRR (n + 1) ((a : ℝ)⁻¹)| ≤
      |(a : ℝ)| ^ (2 * n + 1) * hpDR n *
        (|hpBRealAt a (n + 1)| * |hpRR n ((a : ℝ)⁻¹)| +
          |hpBRealAt a n| * |hpRR (n + 1) ((a : ℝ)⁻¹)|) :=
      mul_le_mul_of_nonneg_left hsub hscale
    _ = _ := by ring

theorem hpLR_tendsto_zero_of_tail_bounds
    {q K M2 Cz CB e2 : ℝ} {k : ℕ} {Bf Rf D L : ℕ → ℝ}
    (hq : 0 < q) (hK : 0 ≤ K) (hM2 : 0 ≤ M2) (hCz : 0 ≤ Cz)
    (hCB : 0 ≤ CB) (he2 : 0 ≤ e2)
    (hB : ∀ m : ℕ, |Bf m| ≤ CB * ((m + 1 : ℕ) : ℝ) ^ k * K ^ m)
    (hR : ∀ m : ℕ, |Rf m| ≤
      (2 * m + 1 : ℝ) * 4 ^ m * q⁻¹ ^ (3 * m + 2) * (Cz * M2 ^ m))
    (hD : ∀ᶠ n : ℕ in atTop,
      0 ≤ D n ∧ D n ≤ e2 * (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n)
    (hL : ∀ n : ℕ, |L n| ≤ q ^ (2 * n + 1) * D n *
      (|Bf (n + 1)| * |Rf n| + |Bf n| * |Rf (n + 1)|))
    (hρ : hpContourGamma * K * (4 * M2) * q⁻¹ < 1) :
    Tendsto L atTop (𝓝 0) := by
  let w : ℝ := q⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.2 hq.le
  have hqw : q * w = 1 := mul_inv_cancel₀ hq.ne'
  let ρ : ℝ := hpContourGamma * K * (4 * M2) * w
  have hγ : 0 ≤ hpContourGamma := hpContourGamma_nonneg
  have hρ0 : 0 ≤ ρ := by positivity
  have hpw : ∀ i j : ℕ, q ^ i * w ^ (i + j) = w ^ j := by
    intro i j
    rw [pow_add, ← mul_assoc, ← mul_pow, hqw, one_pow, one_mul]
  let C1 : ℝ := e2 * Cz * CB * K * w
  let C2 : ℝ := e2 * Cz * CB * 4 * M2 * w ^ 4
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  have hpoly1 : ∀ n : ℕ, 3 ≤ n →
      (2 * (n : ℝ) + 1) ^ 3 * ((n : ℝ) + 2) ^ k ≤
        27 * (2 : ℝ) ^ k * (n : ℝ) ^ (k + 3) := by
    intro n hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
    have h2 : (n : ℝ) + 2 ≤ 2 * n := by linarith
    calc
      (2 * (n : ℝ) + 1) ^ 3 * (n + 2) ^ k ≤
          (3 * n) ^ 3 * (2 * n) ^ k := by gcongr
      _ = 27 * (2 : ℝ) ^ k * n ^ (k + 3) := by
          rw [mul_pow, mul_pow, pow_add]
          ring
  have hpoly2 : ∀ n : ℕ, 3 ≤ n →
      (2 * (n : ℝ) + 1) ^ 2 * (2 * n + 3) * ((n : ℝ) + 1) ^ k ≤
        27 * (2 : ℝ) ^ k * (n : ℝ) ^ (k + 3) := by
    intro n hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
    have h2 : 2 * (n : ℝ) + 3 ≤ 3 * n := by linarith
    have h3 : (n : ℝ) + 1 ≤ 2 * n := by linarith
    calc
      (2 * (n : ℝ) + 1) ^ 2 * (2 * n + 3) * (n + 1) ^ k ≤
          (3 * n) ^ 2 * (3 * n) * (2 * n) ^ k := by gcongr
      _ = 27 * (2 : ℝ) ^ k * n ^ (k + 3) := by
          rw [mul_pow, mul_pow, pow_add]
          ring
  have hkey : ∀ᶠ n : ℕ in atTop,
      |L n| ≤ (C1 + C2) * (27 * (2 : ℝ) ^ k) *
        (n : ℝ) ^ (k + 3) * ρ ^ n := by
    filter_upwards [hD, eventually_ge_atTop 3] with n hDn hn
    rcases hDn with ⟨hD0, hDle⟩
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hB0 := hB n
    have hR0 := hR n
    have hB0' : |Bf n| ≤ CB * ((n : ℝ) + 1) ^ k * K ^ n := by
      simpa using hB0
    have hB1 : |Bf (n + 1)| ≤ CB * ((n : ℝ) + 2) ^ k * K ^ (n + 1) := by
      convert hB (n + 1) using 1 <;> push_cast <;> ring
    have hR0' : |Rf n| ≤
        (2 * (n : ℝ) + 1) * 4 ^ n * w ^ (3 * n + 2) * (Cz * M2 ^ n) := by
      simpa [w] using hR0
    have hR1 : |Rf (n + 1)| ≤
        (2 * (n : ℝ) + 3) * 4 ^ (n + 1) * w ^ (3 * (n + 1) + 2) *
          (Cz * M2 ^ (n + 1)) := by
      convert hR (n + 1) using 1 <;> push_cast <;> ring
    have hpow1 : q ^ (2 * n + 1) * w ^ (3 * n + 2) = w ^ (n + 1) := by
      rw [show 3 * n + 2 = (2 * n + 1) + (n + 1) by omega, hpw]
    have hpow2 : q ^ (2 * n + 1) * w ^ (3 * (n + 1) + 2) = w ^ (n + 4) := by
      rw [show 3 * (n + 1) + 2 = (2 * n + 1) + (n + 4) by omega, hpw]
    have hpowAll : hpContourGamma ^ n * K ^ n * 4 ^ n * M2 ^ n * w ^ n = ρ ^ n := by
      dsimp [ρ]
      rw [mul_pow, mul_pow, mul_pow]
      ring
    have hT1 : q ^ (2 * n + 1) * D n * (|Bf (n + 1)| * |Rf n|) ≤
        C1 * (27 * (2 : ℝ) ^ k) * (n : ℝ) ^ (k + 3) * ρ ^ n := by
      calc
        q ^ (2 * n + 1) * D n * (|Bf (n + 1)| * |Rf n|) ≤
            q ^ (2 * n + 1) *
              (e2 * (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 2) ^ k * K ^ (n + 1) *
                ((2 * n + 1 : ℝ) * 4 ^ n * w ^ (3 * n + 2) * (Cz * M2 ^ n))) := by
          have hD0' : 0 ≤ e2 * (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by positivity
          have hB0' : 0 ≤ CB * ((n : ℝ) + 2) ^ k * K ^ (n + 1) := by positivity
          have hR0' : 0 ≤ (2 * n + 1 : ℝ) * 4 ^ n * w ^ (3 * n + 2) * (Cz * M2 ^ n) := by
            positivity
          gcongr <;> first | assumption | positivity
        _ = (q ^ (2 * n + 1) * w ^ (3 * n + 2)) *
              (e2 * (2 * (n : ℝ) + 1) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 2) ^ k * K ^ (n + 1) *
                ((2 * (n : ℝ) + 1) * 4 ^ n * (Cz * M2 ^ n))) := by ring
        _ = w ^ (n + 1) *
              (e2 * (2 * (n : ℝ) + 1) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 2) ^ k * K ^ (n + 1) *
                ((2 * (n : ℝ) + 1) * 4 ^ n * (Cz * M2 ^ n))) := by rw [hpow1]
        _ = e2 * Cz * CB * K * w * (2 * (n : ℝ) + 1) ^ 3 *
              ((n : ℝ) + 2) ^ k *
              (hpContourGamma ^ n * K ^ n * 4 ^ n * M2 ^ n * w ^ n) := by
          simp only [pow_succ]
          ring
        _ = C1 * (2 * (n : ℝ) + 1) ^ 3 * ((n : ℝ) + 2) ^ k * ρ ^ n := by
          simpa [C1, ρ, ← hpowAll]
        _ ≤ C1 * (27 * (2 : ℝ) ^ k) * (n : ℝ) ^ (k + 3) * ρ ^ n := by
          have hp := hpoly1 n hn
          have hfac : 0 ≤ C1 * ρ ^ n := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hp hfac]
    have hT2 : q ^ (2 * n + 1) * D n * (|Bf n| * |Rf (n + 1)|) ≤
        C2 * (27 * (2 : ℝ) ^ k) * (n : ℝ) ^ (k + 3) * ρ ^ n := by
      calc
        q ^ (2 * n + 1) * D n * (|Bf n| * |Rf (n + 1)|) ≤
            q ^ (2 * n + 1) *
              (e2 * (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 1) ^ k * K ^ n *
                ((2 * (n : ℝ) + 3) * 4 ^ (n + 1) * w ^ (3 * (n + 1) + 2) *
                  (Cz * M2 ^ (n + 1)))) := by
          have hD0' : 0 ≤ e2 * (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by positivity
          have hB0' : 0 ≤ CB * ((n : ℝ) + 1) ^ k * K ^ n := by positivity
          have hR0' : 0 ≤ (2 * (n : ℝ) + 3) * 4 ^ (n + 1) *
              w ^ (3 * (n + 1) + 2) * (Cz * M2 ^ (n + 1)) := by positivity
          gcongr <;> first | assumption | positivity
        _ = (q ^ (2 * n + 1) * w ^ (3 * (n + 1) + 2)) *
              (e2 * (2 * (n : ℝ) + 1) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 1) ^ k * K ^ n *
                ((2 * (n : ℝ) + 3) * 4 ^ (n + 1) * (Cz * M2 ^ (n + 1)))) := by ring
        _ = w ^ (n + 4) *
              (e2 * (2 * (n : ℝ) + 1) ^ 2 * hpContourGamma ^ n) *
              (CB * ((n : ℝ) + 1) ^ k * K ^ n *
                ((2 * (n : ℝ) + 3) * 4 ^ (n + 1) * (Cz * M2 ^ (n + 1)))) := by
          rw [hpow2]
        _ = e2 * Cz * CB * 4 * M2 * w ^ 4 *
              (2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3) *
              ((n : ℝ) + 1) ^ k *
              (hpContourGamma ^ n * K ^ n * 4 ^ n * M2 ^ n * w ^ n) := by
          rw [pow_add, pow_succ, pow_succ]
          ring
        _ = C2 * (2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3) *
              ((n : ℝ) + 1) ^ k * ρ ^ n := by
          simpa [C2, ρ, ← hpowAll]
        _ ≤ C2 * (27 * (2 : ℝ) ^ k) * (n : ℝ) ^ (k + 3) * ρ ^ n := by
          have hp := hpoly2 n hn
          have hfac : 0 ≤ C2 * ρ ^ n := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hp hfac]
    calc
      |L n| ≤ q ^ (2 * n + 1) * D n *
          (|Bf (n + 1)| * |Rf n| + |Bf n| * |Rf (n + 1)|) := hL n
      _ = q ^ (2 * n + 1) * D n * (|Bf (n + 1)| * |Rf n|) +
            q ^ (2 * n + 1) * D n * (|Bf n| * |Rf (n + 1)|) := by ring
      _ ≤ C1 * (27 * (2 : ℝ) ^ k) * n ^ (k + 3) * ρ ^ n +
            C2 * (27 * (2 : ℝ) ^ k) * n ^ (k + 3) * ρ ^ n := add_le_add hT1 hT2
      _ = _ := by ring
  have hlim : Tendsto
      (fun n : ℕ => (C1 + C2) * (27 * (2 : ℝ) ^ k) *
        (n : ℝ) ^ (k + 3) * ρ ^ n) atTop (𝓝 0) := by
    have hρabs : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact hρ
    have hpow := tendsto_pow_const_mul_const_pow_of_abs_lt_one (k + 3)
      (r := ρ) hρabs
    convert hpow.const_mul ((C1 + C2) * (27 * (2 : ℝ) ^ k)) using 1
    · ext n
      ring
    · simp
  have habs : Tendsto (fun n : ℕ => |L n|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => abs_nonneg (L n)) hkey hlim
  exact (tendsto_zero_iff_abs_tendsto_zero L).2 habs

theorem hpLR_tendsto_zero_of_contour_beta_bounds {a : ℤ} {q : ℕ}
    (ha : a = -(q : ℤ)) (hq : 0 < q)
    (certificate : Nonempty (NegContourRectangleCertificate hpBSequence q))
    (I : HPNoAdjacentV13Input a) {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hR : ∀ n : ℕ, |hpRR n ((a : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * M2 ^ n)
    (hρ : hpContourGamma * 29 * (4 * M2) * (q : ℝ)⁻¹ < 1) :
    Tendsto (hpLR a) atTop (𝓝 0) := by
  rcases certificate with ⟨certificate⟩
  rcases certificate.contour_bound with ⟨C, k, hB⟩
  have hC : 0 ≤ C := by
    have h := hB 0
    have h' : (0 : ℝ) ≤ C * ((0 + 1 : ℕ) : ℝ) ^ k * 29 ^ 0 :=
      le_trans (abs_nonneg _) h
    simpa using h'
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqRat : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinv : (a : ℝ)⁻¹ = -((1 : ℝ) / (q : ℝ)) := by
    rw [ha]
    push_cast
    field_simp
  have hBactual : ∀ m : ℕ,
      |hpBR m ((a : ℝ)⁻¹)| ≤ C * ((m + 1 : ℕ) : ℝ) ^ k * (29 : ℝ) ^ m := by
    intro m
    rw [hinv]
    have hz : -((1 : ℝ) / (q : ℝ)) =
        ((-(1 : ℚ) / (q : ℚ) : ℚ) : ℝ) := by
      push_cast
      ring
    rw [hz, hpBR_ratCast]
    have heq : (-(1 : ℚ) / (q : ℚ) : ℚ) = -((q : ℚ)⁻¹) := by
      field_simp [hqRat]
    rw [heq]
    simpa [NegativeContour.hpBSequence] using hB m
  have hD : ∀ᶠ n : ℕ in atTop,
      0 ≤ hpDR n ∧ hpDR n ≤ Real.exp (2 * (1 + 1 / 1000 : ℝ)) *
        (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by
    filter_upwards [hpContourDR_upper] with n hn
    exact ⟨hpDR_nonneg_local n, hn⟩
  have hL : ∀ n : ℕ, |hpLR a n| ≤
      (q : ℝ) ^ (2 * n + 1) * hpDR n *
        (|hpBR (n + 1) ((a : ℝ)⁻¹)| * |hpRR n ((a : ℝ)⁻¹)| +
          |hpBR n ((a : ℝ)⁻¹)| * |hpRR (n + 1) ((a : ℝ)⁻¹)|) := by
    intro n
    have h := hpLR_abs_le_of_v13_input I n
    rw [ha] at h ⊢
    have hqcast : |((-(q : ℤ) : ℤ) : ℝ)| = (q : ℝ) := by
      push_cast
      rw [abs_neg]
      exact abs_of_nonneg (by positivity)
    rw [hqcast] at h
    rw [← hpBR_eq_hpBRealAt (-(q : ℤ)) (n + 1),
      ← hpBR_eq_hpBRealAt (-(q : ℤ)) n] at h
    exact h
  have hR' : ∀ m : ℕ,
      |hpRR m ((a : ℝ)⁻¹)| ≤
        (2 * m + 1 : ℝ) * 4 ^ m * (q : ℝ)⁻¹ ^ (3 * m + 2) * (1 * M2 ^ m) := by
    intro m
    simpa using hR m
  exact hpLR_tendsto_zero_of_tail_bounds (q := (q : ℝ)) (K := 29)
    (M2 := M2) (Cz := 1) (CB := C) (e2 := Real.exp (2 * (1 + 1 / 1000 : ℝ)))
    (k := k) (Bf := fun m => hpBR m ((a : ℝ)⁻¹))
    (Rf := fun m => hpRR m ((a : ℝ)⁻¹)) (D := hpDR) (L := hpLR a)
    hqR (by norm_num) hM2 (by norm_num) hC (Real.exp_pos _).le
    hBactual hR' hD hL hρ

/-- The B4 decay form in the AllN producer assembly is the same `d²/b²`
form as `hpLR`; the denominator and binomial factors are exactly those of
v13 `hp-tail.tex:177-194`. -/
theorem hpIntegerFormL_eq_hpLR (a : ℤ) (n : ℕ) :
    Li2Lean.AllNAssembly.hpIntegerFormL a n = hpLR a n := by
  unfold Li2Lean.AllNAssembly.hpIntegerFormL hpLR hpDR
  rw [hpDenominator_eq_lcmUpto]
  simp [hpIntegerizationScale, Li2Lean.AllNAssembly.hpB, hpbN]

/-- Convert convergence of the residue-normalized form to the exact `HPDecay`
field consumed by `AllNProducers`; this is v13 `hp-tail.tex:188-194`. -/
theorem HPDecay_of_hpLR_tendsto_zero {a : ℤ}
    (h : Tendsto (hpLR a) atTop (𝓝 0)) :
    Li2Lean.AllNAssembly.HPDecay a := by
  change Tendsto (Li2Lean.AllNAssembly.hpIntegerFormL a) atTop (𝓝 0)
  have hfun : Li2Lean.AllNAssembly.hpIntegerFormL a = hpLR a :=
    funext (hpIntegerFormL_eq_hpLR a)
  simpa only [hfun] using h

/-- Exceptional negative-base producer for `q = 8,9,10`. The contour and
beta inputs are attached to the concrete v13 `hpBpoly` and `hpRR` families;
the conclusion has exactly the AllN `HPDecay` type. The analytic inputs
implement v13 `hp-tail.tex:198-220,258-410,411-475`. -/
theorem hpDecayNeg_exceptional_of_contour_beta_bound {q : ℕ}
    (hq : 0 < q)
    (certificate : Nonempty (NegContourRectangleCertificate hpBSequence q))
    (I : HPNoAdjacentV13Input (-(q : ℤ))) {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hR : ∀ n : ℕ,
      |hpRR n ((-(q : ℤ) : ℝ)⁻¹)| ≤
        (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * M2 ^ n)
    (hρ : hpContourGamma * 29 * (4 * M2) * (q : ℝ)⁻¹ < 1) :
    Li2Lean.AllNAssembly.HPDecay (-(q : ℤ)) := by
  apply HPDecay_of_hpLR_tendsto_zero
  have hR' : ∀ n : ℕ,
      |hpRR n ((↑(-(q : ℤ)) : ℝ)⁻¹)| ≤
        (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * M2 ^ n := by
    intro n
    simpa only [Int.cast_neg] using hR n
  exact hpLR_tendsto_zero_of_contour_beta_bounds
    (a := -(q : ℤ)) (q := q) rfl hq certificate I hM2 hR' hρ

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hpLR_tendsto_zero_of_contour_beta_bounds
