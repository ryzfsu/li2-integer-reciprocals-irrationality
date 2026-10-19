/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvBank
import Li2Lean.P0.EnvContourQ

open Finset Filter Topology

namespace Li2Lean.P0.Env

noncomputable section

/-- The q-geometric tail used in the first and second frequency moments. -/
def geoTailQ (q s n : ℕ) : ℝ :=
  if n = 0 then 0 else ((n + s).choose s : ℝ) * (q : ℝ)⁻¹ ^ n

/-- The q-logarithmic tail occurring in the first frequency moment. -/
def logTailQ (q n : ℕ) : ℝ :=
  if n = 0 then 0 else (q : ℝ)⁻¹ ^ n / n

/-- The q-dilogarithmic tail occurring in the diagonal second moment. -/
def li2TailQ (q n : ℕ) : ℝ :=
  if n = 0 then 0 else (q : ℝ)⁻¹ ^ n / (n : ℝ) ^ 2

theorem hasSum_geoTailQ (q s : ℕ) (hq : 2 ≤ q) :
    HasSum (geoTailQ q s)
      (((q : ℝ) / ((q : ℝ) - 1)) ^ (s + 1) - 1) := by
  convert hasSum_geo_tail_q q s hq using 1
  funext n
  by_cases hn : n = 0 <;> simp [geoTailQ, hn, inv_pow]

theorem hasSum_logTailQ (q : ℕ) (hq : 2 ≤ q) :
    HasSum (logTailQ q) (Real.log ((q : ℝ) / ((q : ℝ) - 1))) := by
  convert hasSum_log_q q hq using 1
  funext n
  by_cases hn : n = 0 <;> simp [logTailQ, hn, inv_pow]

theorem hasSum_li2TailQ (q : ℕ) (hq : 2 ≤ q) :
    HasSum (li2TailQ q) (li2InvValue (q : ℤ)) := by
  convert hasSum_li2_q q hq using 1
  funext n
  by_cases hn : n = 0 <;> simp [li2TailQ, hn, inv_pow]

def headFirstQ (q g i n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n ≤ i then ((i - n + g).choose g : ℝ) / n * (q : ℝ)⁻¹ ^ n else 0

def tailFirstQ (q g i n : ℕ) : ℝ :=
  if i + g < n then ((n - i - 1).choose g : ℝ) / n * (q : ℝ)⁻¹ ^ n else 0

theorem hasSum_headFirstQ (q g i : ℕ) :
    HasSum (headFirstQ q g i)
      (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
        (q : ℝ)⁻¹ ^ (r + 1)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := range (i + 1)) (f := headFirstQ q g i) (by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [headFirstQ, show ¬ (1 ≤ n ∧ n ≤ i) by omega])
  convert h using 1
  rw [Finset.sum_range_succ']
  simp only [headFirstQ, show ¬ (1 ≤ 0 ∧ 0 ≤ i) by omega, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  rw [if_pos (show 1 ≤ r + 1 ∧ r + 1 ≤ i by omega)]
  push_cast
  ring

theorem tailFirstQ_eq (q g i n : ℕ) :
    tailFirstQ q g i n = (-1 : ℝ) ^ (g + 1) *
      (headFirstQ q g i n +
        ∑ s ∈ range g, aFirst g i s * geoTailQ q s n -
        ((i + g).choose g : ℝ) * logTailQ q n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tailFirstQ, headFirstQ, geoTailQ, logTailQ]
  have hc := coeff_first i g n hn
  have hn0 : n ≠ 0 := by omega
  have hT : tailFirstQ q g i n =
      (if i + g < n then ((n - i - 1).choose g : ℝ) / n else 0) *
        (q : ℝ)⁻¹ ^ n := by
    unfold tailFirstQ
    split_ifs <;> simp
  have hH : headFirstQ q g i n =
      (if n ≤ i then ((i - n + g).choose g : ℝ) / n else 0) *
        (q : ℝ)⁻¹ ^ n := by
    by_cases h : n ≤ i
    · simp [headFirstQ, h, show 1 ≤ n by omega]
    · simp [headFirstQ, h]
  have hG : ∀ s, geoTailQ q s n = ((n + s).choose s : ℝ) * (q : ℝ)⁻¹ ^ n := by
    intro s
    simp [geoTailQ, hn0]
  have hL : logTailQ q n = (q : ℝ)⁻¹ ^ n / n := by
    simp [logTailQ, hn0]
  rw [hT, hc, hH, hL]
  simp only [hG, aFirst]
  rw [show (∑ s ∈ range g, (-1 : ℝ) ^ s / ((s : ℝ) + 1) *
      ((i + g).choose (g - (s + 1)) : ℝ) *
      (((n + s).choose s : ℝ) * (q : ℝ)⁻¹ ^ n)) =
      (∑ s ∈ range g, (-1 : ℝ) ^ s / ((s : ℝ) + 1) *
      ((i + g).choose (g - (s + 1)) : ℝ) * ((n + s).choose s : ℝ)) *
      (q : ℝ)⁻¹ ^ n by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  ring

theorem hasSum_tailFirstQ (q g i : ℕ) (hq : 2 ≤ q) :
    HasSum (tailFirstQ q g i) ((-1 : ℝ) ^ (g + 1) *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) /
          ((r : ℝ) + 1) * (q : ℝ)⁻¹ ^ (r + 1)) +
        ∑ s ∈ range g, aFirst g i s * (((q : ℝ) / ((q : ℝ) - 1)) ^ (s + 1) - 1) -
        ((i + g).choose g : ℝ) * Real.log ((q : ℝ) / ((q : ℝ) - 1)))) := by
  have hcomb := (((hasSum_headFirstQ q g i).add
      (hasSum_sum (s := range g) (fun s _ =>
        (hasSum_geoTailQ q s hq).mul_left (aFirst g i s)))).sub
      ((hasSum_logTailQ q hq).mul_left ((i + g).choose g : ℝ))).mul_left
        ((-1 : ℝ) ^ (g + 1))
  convert hcomb using 1
  funext n
  rw [tailFirstQ_eq]

def headSecondQ (q g i n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 *
    (q : ℝ)⁻¹ ^ n else 0

theorem hasSum_headSecondQ (q g i : ℕ) :
    HasSum (headSecondQ q g i)
      (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
        (q : ℝ)⁻¹ ^ (r + 1)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := range (i + 1)) (f := headSecondQ q g i) (by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [headSecondQ, show ¬ (1 ≤ n ∧ n ≤ i) by omega])
  convert h using 1
  rw [Finset.sum_range_succ']
  simp only [headSecondQ, show ¬ (1 ≤ 0 ∧ 0 ≤ i) by omega, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  rw [if_pos (show 1 ≤ r + 1 ∧ r + 1 ≤ i by omega)]
  push_cast
  ring

def tailSecondQ (q g i n : ℕ) : ℝ :=
  if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 *
    (q : ℝ)⁻¹ ^ n else 0

theorem tailSecondQ_eq (q g i n : ℕ) :
    tailSecondQ q g i n = (-1 : ℝ) ^ (g + 1) *
      (headSecondQ q g i n -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * geoTailQ q r n -
        ((i + g).choose g : ℝ) * li2TailQ q n +
        ((i + g).choose g : ℝ) * harm g i * logTailQ q n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tailSecondQ, headSecondQ, geoTailQ, logTailQ, li2TailQ]
  have hc := coeff_second i g n hn
  have hn0 : n ≠ 0 := by omega
  have hT : tailSecondQ q g i n =
      (if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 else 0) *
        (q : ℝ)⁻¹ ^ n := by
    unfold tailSecondQ
    split_ifs <;> simp
  have hH : headSecondQ q g i n =
      (if n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 else 0) *
        (q : ℝ)⁻¹ ^ n := by
    by_cases h : n ≤ i
    · simp [headSecondQ, h, show 1 ≤ n by omega]
    · simp [headSecondQ, h]
  have hG : ∀ s, geoTailQ q s n = ((n + s).choose s : ℝ) * (q : ℝ)⁻¹ ^ n := by
    intro s
    simp [geoTailQ, hn0, inv_pow]
  have hL : logTailQ q n = (q : ℝ)⁻¹ ^ n / n := by
    simp [logTailQ, hn0, inv_pow]
  have hL2 : li2TailQ q n = (q : ℝ)⁻¹ ^ n / (n : ℝ) ^ 2 := by
    simp [li2TailQ, hn0, inv_pow]
  rw [hT, hc, hH, hL, hL2]
  simp only [hG, bSecond, harm]
  have hin : ∀ s, (∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
      (((n + r).choose r : ℝ) * (q : ℝ)⁻¹ ^ n)) =
      (∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) *
      (q : ℝ)⁻¹ ^ n := by
    intro s
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [hin]
  rw [show (∑ s ∈ Icc 2 g, (-1 : ℝ) ^ s / (s : ℝ) *
      ((i + g).choose (g - s) : ℝ) *
      ((∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) *
        (q : ℝ)⁻¹ ^ n)) =
      (∑ s ∈ Icc 2 g, (-1 : ℝ) ^ s / (s : ℝ) *
      ((i + g).choose (g - s) : ℝ) *
      (∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1))) *
      (q : ℝ)⁻¹ ^ n by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  ring

theorem hasSum_tailSecondQ (q g i : ℕ) (hq : 2 ≤ q) :
    HasSum (tailSecondQ q g i) ((-1 : ℝ) ^ (g + 1) *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) /
          ((r : ℝ) + 1) ^ 2 * (q : ℝ)⁻¹ ^ (r + 1)) -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
            (((q : ℝ) / ((q : ℝ) - 1)) ^ (r + 1) - 1) -
        ((i + g).choose g : ℝ) * li2InvValue (q : ℤ) +
        ((i + g).choose g : ℝ) * harm g i *
          Real.log ((q : ℝ) / ((q : ℝ) - 1)))) := by
  have hinner : ∀ s, HasSum
      (fun n => ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * geoTailQ q r n)
      (∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
        (((q : ℝ) / ((q : ℝ) - 1)) ^ (r + 1) - 1)) := by
    intro s
    exact hasSum_sum (s := range (s - 1)) (fun r _ =>
      (hasSum_geoTailQ q r hq).mul_left (((r : ℝ) + 1)⁻¹))
  have hcomb := ((((hasSum_headSecondQ q g i).sub
      (hasSum_sum (s := Icc 2 g) (fun s _ =>
        (hinner s).mul_left (bSecond g i s)))).sub
      ((hasSum_li2TailQ q hq).mul_left ((i + g).choose g : ℝ))).add
      ((hasSum_logTailQ q hq).mul_left (((i + g).choose g : ℝ) * harm g i))).mul_left
        ((-1 : ℝ) ^ (g + 1))
  convert hcomb using 1
  funext n
  rw [tailSecondQ_eq]

theorem qpow_shift (q a b : ℕ) (hq : 2 ≤ q) (hab : b ≤ a) :
    (q : ℝ) ^ a * (q : ℝ)⁻¹ ^ b = (q : ℝ) ^ (a - b) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have ha : (q : ℝ) ^ a = (q : ℝ) ^ (a - b) * (q : ℝ) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hab]
  rw [ha, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]

@[simp] theorem p0UQ_cast_q (q g i : ℕ) :
    ((p0UQ (q : ℚ) g i : ℚ) : ℝ) =
      (q : ℝ) ^ i * ((i + g).choose g : ℝ) := by
  simp [p0UQ]

theorem p0Q_cast_q (q : ℕ) (hq : 2 ≤ q) (s : ℕ) :
    ((p0Q (q : ℚ) s : ℚ) : ℝ) =
      ((q : ℝ) / ((q : ℝ) - 1)) ^ s - 1 := by
  simp [p0Q]

theorem p0TQ_cast_q (q g i : ℕ) (hq : 2 ≤ q) :
    ((p0TQ (q : ℚ) g i : ℚ) : ℝ) = (q : ℝ) ^ i *
      ((∑ r ∈ range i,
          ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
            (q : ℝ)⁻¹ ^ (r + 1)) +
        ∑ s ∈ range g, aFirst g i s *
          (((q : ℝ) / ((q : ℝ) - 1)) ^ (s + 1) - 1)) := by
  have hsum : (∑ r ∈ range i,
      ((q : ℝ) ^ (i - (r + 1)) * ((i - (r + 1) + g).choose g : ℝ)) /
        ((r : ℝ) + 1)) =
      (q : ℝ) ^ i * ∑ r ∈ range i,
        ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
          (q : ℝ)⁻¹ ^ (r + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r + 1 ≤ i := by simp only [Finset.mem_range] at hr; omega
    rw [← qpow_shift q i (r + 1) hq hr']
    ring
  calc
    ((p0TQ (q : ℚ) g i : ℚ) : ℝ) =
        (∑ r ∈ range i,
          ((q : ℝ) ^ (i - (r + 1)) * ((i - (r + 1) + g).choose g : ℝ)) /
            ((r : ℝ) + 1)) +
          (q : ℝ) ^ i * ∑ s ∈ range g, aFirst g i s *
            (((q : ℝ) / ((q : ℝ) - 1)) ^ (s + 1) - 1) := by
      simp [p0TQ, p0UQ, p0Q, aFirst]
    _ = _ := by rw [hsum]; ring

theorem p0BQQ_cast_q (q g i : ℕ) (hq : 2 ≤ q) :
    ((p0BQQ (q : ℚ) g i : ℚ) : ℝ) = (q : ℝ) ^ i *
      ((∑ r ∈ range i,
          ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
            (q : ℝ)⁻¹ ^ (r + 1)) -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
            (((q : ℝ) / ((q : ℝ) - 1)) ^ (r + 1) - 1)) := by
  have hsum : (∑ r ∈ range i,
      ((q : ℝ) ^ (i - (r + 1)) * ((i - (r + 1) + g).choose g : ℝ)) /
        ((r : ℝ) + 1) ^ 2) =
      (q : ℝ) ^ i * ∑ r ∈ range i,
        ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
          (q : ℝ)⁻¹ ^ (r + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r + 1 ≤ i := by simp only [Finset.mem_range] at hr; omega
    rw [← qpow_shift q i (r + 1) hq hr']
    ring
  calc
    ((p0BQQ (q : ℚ) g i : ℚ) : ℝ) =
        (∑ r ∈ range i,
          ((q : ℝ) ^ (i - (r + 1)) * ((i - (r + 1) + g).choose g : ℝ)) /
            ((r : ℝ) + 1) ^ 2) -
          (q : ℝ) ^ i * ∑ s ∈ Icc 2 g, bSecond g i s *
            ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
              (((q : ℝ) / ((q : ℝ) - 1)) ^ (r + 1) - 1) := by
      simp [p0BQQ, p0UQ, p0Q, bSecond]
      apply Or.inl
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by rw [hsum]; ring

theorem p0CQ_diag_cast_q (q g i : ℕ) :
    ((p0CQ (q : ℚ) g i i : ℚ) : ℝ) =
      -((q : ℝ) ^ i * ((i + g).choose g : ℝ)) * harm g i := by
  simp only [p0CQ, if_true]
  push_cast
  rw [← p0UQ_cast_q]
  simp [harm, p0UQ]

theorem frequencyWeightRealQ_eq (q g r : ℕ) :
    frequencyWeightRealQ q g r = ((r - 1).choose g : ℝ) * (q : ℝ)⁻¹ ^ r := by
  simp [frequencyWeightRealQ, div_eq_mul_inv, inv_pow]

theorem tailFirstQ_shift (q g i r : ℕ) (hq : 2 ≤ q) :
    tailFirstQ q g i (r + i) = (q : ℝ)⁻¹ ^ i *
      (if g < r then frequencyWeightRealQ q g r / ((i : ℝ) + r) else 0) := by
  unfold tailFirstQ
  by_cases h : g < r
  · have hsub : r + i - i - 1 = r - 1 := by omega
    rw [if_pos (by omega), if_pos h, frequencyWeightRealQ_eq, hsub, pow_add]
    push_cast
    have hq : (q : ℝ) ≠ 0 := by
      exact_mod_cast (show q ≠ 0 by omega)
    field_simp
    ring
  · rw [if_neg (by omega), if_neg h]
    ring

theorem tailSecondQ_shift (q g i r : ℕ) (hq : 2 ≤ q) :
    tailSecondQ q g i (r + i) = (q : ℝ)⁻¹ ^ i *
      (if g < r then frequencyWeightRealQ q g r / (((i : ℝ) + r) ^ 2) else 0) := by
  unfold tailSecondQ
  by_cases h : g < r
  · have hsub : r + i - i - 1 = r - 1 := by omega
    rw [if_pos (by omega), if_pos h, frequencyWeightRealQ_eq, hsub, pow_add]
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by
      exact_mod_cast (show q ≠ 0 by omega)
    field_simp
    ring
  · rw [if_neg (by omega), if_neg h]
    ring

theorem qpow_inv_cancel (q n : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) ^ n * (q : ℝ)⁻¹ ^ n = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]

theorem hasSum_first_q (q g i : ℕ) (hq : 2 ≤ q) :
    HasSum (fun r : ℕ => if g < r then
      frequencyWeightRealQ q g r / ((i : ℝ) + r) else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0TQ (q : ℚ) g i : ℚ) : ℝ) -
          Real.log ((q : ℝ) / ((q : ℝ) - 1)) *
            ((p0UQ (q : ℚ) g i : ℚ) : ℝ))) := by
  have hshift := hasSum_shift_of_zero i (fun n hn => by
    unfold tailFirstQ
    rw [if_neg (by omega)]) (hasSum_tailFirstQ q g i hq)
  have h := hshift.mul_left ((q : ℝ) ^ i)
  convert h using 1
  · funext r
    rw [tailFirstQ_shift q g i r hq]
    by_cases hr : g < r
    · rw [if_pos hr, ← mul_assoc, qpow_inv_cancel q i hq, one_mul]
    · rw [if_neg hr]
      simp
  · rw [p0TQ_cast_q q g i hq, p0UQ_cast_q]
    ring

theorem hasSum_second_q (q g i : ℕ) (hq : 2 ≤ q) :
    HasSum (fun r : ℕ => if g < r then
      frequencyWeightRealQ q g r / ((i : ℝ) + r) ^ 2 else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0BQQ (q : ℚ) g i : ℚ) : ℝ) -
          li2InvValue (q : ℤ) * ((p0UQ (q : ℚ) g i : ℚ) : ℝ) -
          Real.log ((q : ℝ) / ((q : ℝ) - 1)) *
            ((p0CQ (q : ℚ) g i i : ℚ) : ℝ))) := by
  have hshift := hasSum_shift_of_zero i (fun n hn => by
    unfold tailSecondQ
    rw [if_neg (by omega)]) (hasSum_tailSecondQ q g i hq)
  have h := hshift.mul_left ((q : ℝ) ^ i)
  convert h using 1
  · funext r
    rw [tailSecondQ_shift q g i r hq]
    by_cases hr : g < r
    · rw [if_pos hr, ← mul_assoc, qpow_inv_cancel q i hq, one_mul]
    · rw [if_neg hr]
      simp
  · rw [p0BQQ_cast_q q g i hq, p0UQ_cast_q, p0CQ_diag_cast_q]
    ring

/-- The base-q source bank; it generalizes `bank_hasSum` with the correct
row coefficient `log(q/(q-1))` and diagonal pin `log q` encoded in `p0CQ`. -/
theorem bank_hasSum_q (q g i j : ℕ) (hq : 2 ≤ q) :
    HasSum (fun r : ℕ => if g < r then
      frequencyWeightRealQ q g r / (((i : ℝ) + r) * ((j : ℝ) + r)) else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0BQ (q : ℚ) g i j : ℚ) : ℝ) -
          li2InvValue (q : ℤ) * ((p0AQ (q : ℚ) g i j : ℚ) : ℝ) -
          qSourceRowOperationCoefficient (q : ℤ) *
            ((p0CQ (q : ℚ) g i j : ℚ) : ℝ))) := by
  by_cases hij : i = j
  · subst j
    convert hasSum_second_q q g i hq using 1
    · funext r
      split_ifs <;> ring
    · simp [p0BQ, p0AQ, qSourceRowOperationCoefficient]
  · have hji : (j : ℝ) - i ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hij))
    have h := ((hasSum_first_q q g i hq).sub
      (hasSum_first_q q g j hq)).div_const ((j : ℝ) - i)
    convert h using 1
    · funext r
      split_ifs with hr
      · have hjr : (j : ℝ) + r ≠ 0 := by
          have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
          positivity
        have hir : (i : ℝ) + r ≠ 0 := by
          have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
          positivity
        field_simp
        ring
      · simp
    · simp only [p0BQ, p0AQ, p0CQ, if_neg hij, qSourceRowOperationCoefficient]
      push_cast
      field_simp [hji]
      ring

end

end Li2Lean.P0.Env
