/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.EntryGoodness
import Li2Lean.P0.ScaledLucas.Entries

namespace Li2Lean.P0.PositiveTower.EntryGoodness

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Algebraic diagonal decomposition for the general-base C entry. -/
theorem qC_diag_decomp_generic (a : ℚ) (k g i : ℕ) :
    qRatP p k * p0CQ a g i i =
      -p0UQ a g i * ∑ s ∈ Finset.range g,
        qRatP p k / ((i + s + 1 : ℕ) : ℚ) := by
  unfold p0CQ
  rw [if_pos rfl]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  push_cast
  ring

/-- Algebraic off-diagonal divided-difference decomposition for the
general-base C entry. -/
theorem qC_off_decomp_generic (a : ℚ) (k g i j : ℕ) (hij : i ≠ j) :
    qRatP p k * p0CQ a g i j =
      (p0UQ a g i - p0UQ a g j) *
        (qRatP p k / ((j : ℚ) - (i : ℚ))) := by
  unfold p0CQ
  rw [if_neg hij]
  ring

/-- Finite sums of p-integral rationals commute with residue reduction. -/
theorem ratCast_sum_good {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ GoodP p) :
    ((∑ i ∈ s, f i : ℚ) : ZMod p) = ∑ i ∈ s, (f i : ZMod p) := by
  classical
  let g : ι → GoodP p := fun i => if h : f i ∈ GoodP p then ⟨f i, h⟩ else 0
  have hsum : (∑ i ∈ s, f i) = ((∑ i ∈ s, g i : GoodP p) : ℚ) := by
    rw [show ((∑ i ∈ s, g i : GoodP p) : ℚ) = (GoodP p).subtype (∑ i ∈ s, g i)
      from rfl, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, hf i hi]
  rw [hsum]
  change residueHomP p (∑ i ∈ s, g i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [g, hf i hi, ↓reduceDIte]
  rfl

/-- A denominator `c * p^k`, with `0 < c < p`, reduces the scaled quotient
to the inverse of `c`. -/
theorem qdiv_cast_unit_generic (k c : ℕ) (hc0 : 0 < c) (hcp : c < p) :
    ((qRatP p k / ((c * p ^ k : ℕ) : ℚ) : ℚ) : ZMod p) =
      (c : ZMod p)⁻¹ := by
  have hp : Nat.Prime p := Fact.out
  have hcp' : Nat.Coprime c p :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hc0) hcp hp).symm
  have hcne : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc0)
  have hpowne : ((p ^ k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp.ne_zero
  have hrat : qRatP p k / ((c * p ^ k : ℕ) : ℚ) = (c : ℚ)⁻¹ := by
    rw [qRatP, Nat.cast_mul, Nat.cast_pow]
    field_simp [hcne, hpowne]
    simp [hpowne]
  rw [hrat, Rat.cast_inv_nat]

/-- If a denominator below `p^(k+1)` is not divisible by `p^k`, the
prime-power scaled quotient has zero residue. -/
theorem qdiv_cast_zero_generic (k n : ℕ) (hn0 : 0 < n)
    (hnlt : n < p * p ^ k) (hnd : ¬ p ^ k ∣ n) :
    ((qRatP p k / (n : ℚ) : ℚ) : ZMod p) = 0 := by
  exact powP_div_den_residue_eq_zero k n hn0 hnlt hnd

/-- The M=4 diagonal C entry after reduction at the actual prime-power
scale. The two surviving reciprocal denominators are the carry positions. -/
theorem cast_qC_diag_generic (a : ℤ)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k A v : ℕ) (hA : A + 3 ≤ p) (hv : v < p ^ k) :
    ((qRatP p k * p0CQ (a : ℚ) (2 * p ^ k)
        (A * p ^ k + v) (A * p ^ k + v) : ℚ) : ZMod p) =
      -(a : ZMod p) ^ v *
        ((a : ZMod p) ^ A * (Nat.choose (A + 2) 2 : ZMod p)) *
          ∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ZMod p)⁻¹ := by
  let q := p ^ k
  have hq : 0 < q := by
    dsimp [q]
    exact pow_pos (Fact.out : Nat.Prime p).pos _
  have hvq : v < q := by simpa [q] using hv
  have hAq : A * q + v < p * q := by
    calc
      A * q + v < (A + 1) * q := by nlinarith
      _ ≤ p * q := Nat.mul_le_mul_right q (by omega)
  have hmax : A * q + v + 2 * q < p * q := by
    nlinarith
  rw [qC_diag_decomp_generic (a := (a : ℚ)) (k := k) (g := 2 * p ^ k)
    (i := A * p ^ k + v)]
  have hterms : ∀ s ∈ Finset.range (2 * q),
      qRatP p k / ((A * p ^ k + v + s + 1 : ℕ) : ℚ) ∈ GoodP p := by
    intro s hs
    have hs' : s < 2 * q := Finset.mem_range.mp hs
    have hd : 0 < A * p ^ k + v + s + 1 := by omega
    have hb : A * p ^ k + v + s + 1 < p * p ^ k := by
      have hh : A * p ^ k + v + 2 * p ^ k < p * p ^ k := by simpa [q] using hmax
      omega
    exact q_div_good k _ hd (by simpa [q] using hb)
  rw [show (2 * p ^ k : ℕ) = 2 * q by rfl]
  rw [Rat.cast_mul_of_ne_zero
    (natCast_ne_zero_of_coprime ((GoodP p).neg_mem
      (p0U_good_general (p := p) (a := a) (2 * q) (A * q + v))))
    (natCast_ne_zero_of_coprime ((GoodP p).sum_mem hterms))]
  rw [Rat.cast_neg, Li2Lean.P0.ScaledLucas.cast_U_generic p a 2 k A v
      (by simpa [q] using hv),
    ratCast_sum_good (Finset.range (2 * q)) _ hterms]
  have hsum :
      (∑ s ∈ Finset.range (2 * q),
        ((qRatP p k / ((A * q + v + s + 1 : ℕ) : ℚ) : ℚ) : ZMod p)) =
      ∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ZMod p)⁻¹ := by
    rw [Li2Lean.P0.ScaledLucas.block_sum_full q (q - 1 - v) _ (by omega) 2]
    · apply Finset.sum_congr rfl
      intro c hc
      have hc' : c < 2 := Finset.mem_range.mp hc
      have hhit : A * q + v + (c * q + (q - 1 - v)) + 1 =
          (A + c + 1) * q := by
        have hcarry : v + (q - 1 - v) + 1 = q := by omega
        calc
          A * q + v + (c * q + (q - 1 - v)) + 1 =
              (A * q + c * q) + (v + (q - 1 - v) + 1) := by omega
          _ = (A + c) * q + q := by rw [hcarry]; ring
          _ = (A + c + 1) * q := by ring
      rw [hhit, qdiv_cast_unit_generic k (A + c + 1)
        (by omega) (by omega)]
    · intro c hc t ht htt
      have hc' : c < 2 := hc
      have ht' : t < q := ht
      have hsplit : A * q + v + (c * q + t) + 1 =
          (A + c) * q + (v + t + 1) := by
        calc
          A * q + v + (c * q + t) + 1 = A * q + c * q + (v + t + 1) := by omega
          _ = (A + c) * q + (v + t + 1) := by ring
      have hr : 0 < v + t + 1 := by omega
      have hrlt : v + t + 1 < 2 * q := by omega
      have hnd : ¬ q ∣ A * q + v + (c * q + t) + 1 := by
        intro hd
        have hmod := Nat.mod_eq_zero_of_dvd hd
        have hmod' : (v + t + 1) % q = 0 := by
          simpa [hsplit, Nat.add_mod, Nat.mul_mod] using hmod
        have hmul : q ∣ v + t + 1 := Nat.dvd_of_mod_eq_zero hmod'
        obtain ⟨d, hd⟩ := hmul
        have hdq : d = 1 := by nlinarith
        apply htt
        rw [hdq] at hd
        omega
      have hApc : A + c + 2 ≤ p := by omega
      have hNlt : A * q + v + (c * q + t) + 1 < p * q := by
        rw [hsplit]
        calc
          (A + c) * q + (v + t + 1) < (A + c) * q + 2 * q :=
            Nat.add_lt_add_left hrlt _
          _ = (A + c + 2) * q := by ring
          _ ≤ p * q := Nat.mul_le_mul_right q hApc
      rw [qdiv_cast_zero_generic k _ (by omega)
        (by simpa [q] using hNlt) hnd]
  rw [hsum]
  ring

end
end Li2Lean.P0.PositiveTower.EntryGoodness
