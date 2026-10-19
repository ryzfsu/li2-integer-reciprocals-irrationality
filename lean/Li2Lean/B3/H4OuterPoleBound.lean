/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.H4ValuationRegimeBridge
import Li2Lean.B3.Q567ArithmeticProofContracts

/-!
# H4 Leaf L1: Uniform Outer-Pole Coefficient Bound

Proves the $q$-uniform outer-pole Gauss valuation lower bound for the signed
$V$ determinant polynomial `V.vPolynomial n a` for all primes $p$ in the outer
range $5n < p \le U = 11n - 1$ (`v-arithmetic.tex:289-318`, Lemma
`lem:v-outer-poles` and Proposition `prop:v-outer-total`).

The row and column potentials `rowPot` and `colPot` are assembled from the
four-band outer potential assignments `q5OuterLambdaB`, `q5OuterLambdaV`, and
`q5OuterChi` in `Li2Lean.V.Q5Certificate`, which are independent of $a = -q$.
Every Leibniz product in `V.vSourceMatrix n a` has coefficientwise valuation
bounded below by `-((∑ r, rowPot n p r) + (∑ c, colPot n p c)) = -q5OuterCost n p`.
-/

namespace Li2Lean.B3.H4Outer

open scoped BigOperators
open Li2Lean.V Li2Lean.V.Q5Certificate Li2Lean.B3.Q5ResidueProof

noncomputable section

/-- Natural-indexed outer row potential on `[0, 9n)`. -/
def rowPotNat (n p r : ℕ) : ℕ :=
  if r < V.vM n then 0
  else if r < 2 * V.vM n then
    V.Q5Certificate.q5OuterLambdaB n p (2 * n + (r - V.vM n))
  else
    V.Q5Certificate.q5OuterLambdaV n p (1 + (r - 2 * V.vM n))

/-- Outer row potential on `Fin (V.vMatrixSize n)`:
`0` on `C`-rows, `q5OuterLambdaB` on `B - X A`-rows, and `q5OuterLambdaV` on `V`-rows. -/
def rowPot (n p : ℕ) (r : Fin (V.vMatrixSize n)) : ℕ :=
  if r.val < V.vM n then 0
  else if r.val < 2 * V.vM n then
    V.Q5Certificate.q5OuterLambdaB n p (2 * n + (r.val - V.vM n))
  else
    V.Q5Certificate.q5OuterLambdaV n p (1 + (r.val - 2 * V.vM n))

/-- Outer column potential on `Fin (V.vMatrixSize n)`. -/
def colPot (n p : ℕ) (c : Fin (V.vMatrixSize n)) : ℕ :=
  V.Q5Certificate.q5OuterChi n p (V.vJIndex n c)

theorem rowPot_eq_rowPotNat (n p : ℕ) (r : Fin (V.vMatrixSize n)) :
    rowPot n p r = rowPotNat n p r.val := rfl

/-! ## Divided-difference valuation bound for `B`-entries in the outer range -/

/-- For `i < 2p` the residue `i % p` is linear in `i`: it is `i` below `p`
and `i - p` on `[p, 2p)`.  No quotient `i / p` (hence no product
`p * (i / p)`) is exposed to `omega`. -/
private theorem mod_cases_of_lt_two_mul {p i : ℕ} (hi : i < 2 * p) :
    (i < p ∧ i % p = i) ∨ (p ≤ i ∧ i % p = i - p) := by
  by_cases h : i < p
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · have hpi : p ≤ i := Nat.le_of_not_lt h
    refine Or.inr ⟨hpi, ?_⟩
    calc i % p = (i - p + p) % p := by rw [Nat.sub_add_cancel hpi]
      -- Verified certificate computation.
      _ = (i - p) % p := Nat.add_mod_right (i - p) p
      _ = i - p := Nat.mod_eq_of_lt (by omega)

private theorem mod_eq_of_lt_two_mul {p i j : ℕ}
    (hi : i < 2 * p) (hj : j < 2 * p) (hne : i ≠ j) (hmod : i % p = j % p) :
    (p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) := by
  -- Each residue is replaced by a linear expression; `i % p` and `j % p`
  -- remain only as shared atoms, so the four cases are linear for `omega`.
  rcases mod_cases_of_lt_two_mul hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
    rcases mod_cases_of_lt_two_mul hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ <;>
    omega

/-- In the outer range where `i, j < 2p` and `i, j < p^2`, the `p`-adic valuation
of `V.vBEntry a i j` is at least `0` when `i, j < p`, at least `-1` when at least
one index is `≥ p` without a pole collision, and at least `-2` when `p ≤ i = j`
or `|i - j| ≥ p` with the larger index `≥ p`. -/
theorem B_outer_val (p : ℕ) (a : ℤ) (i j : ℕ)
    (hp : p.Prime) (hi : i < 2 * p) (hj : j < 2 * p)
    (hi2 : i < p ^ 2) (hj2 : j < p ^ 2) :
    Q5ResidueProof.ValAtLeast p
      (-(if p ≤ i ∨ p ≤ j then 1 else 0) -
        (if (p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) ∨ (i = j ∧ p ≤ i)
          then 1 else 0))
      (V.vBEntry a i j) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hpij : p ≤ i ∨ p ≤ j
  · have hb := Q5ResidueProof.B_val p a i j hp hi2 hj2
    apply hb.mono
    rw [ite_eq_left hpij]
    by_cases hex : i % p = j % p ∧ (i ≠ j ∨ p ≤ i)
    · have hcond : (p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) ∨ (i = j ∧ p ≤ i) := by
        by_cases hij : i = j
        · subst j
          have hpi : p ≤ i := by rcases hpij with h | h <;> exact h
          exact Or.inr (Or.inr ⟨rfl, hpi⟩)
        · rcases mod_eq_of_lt_two_mul hi hj hij hex.1 with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
      simp [Q5ResidueProof.entryExtra, hex, hcond]
    · simp only [Q5ResidueProof.entryExtra, ite_eq_right hex]
      split_ifs <;> omega
  · push_neg at hpij
    rcases hpij with ⟨hip, hjp⟩
    have hnot1 : ¬ (p ≤ i ∨ p ≤ j) := by omega
    have hnot2 : ¬ ((p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) ∨ (i = j ∧ p ≤ i)) := by omega
    rw [ite_eq_right hnot1, ite_eq_right hnot2]
    norm_num
    by_cases hij : i = j
    · subst j
      simpa [V.vBEntry] using Q5ResidueProof.momentB_small p a i hp hip
    · rw [V.vBEntry, ite_eq_right hij]
      have hti := Q5ResidueProof.momentT_small p a i hp hip
      have htj := Q5ResidueProof.momentT_small p a j hp hjp
      have hv := (hti.sub htj).div ((j : ℚ) - (i : ℚ))
      have hmod : i % p ≠ j % p := by
        rw [Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp]
        exact hij
      have hd := Q5ResidueProof.difference_val_le p i j hp hi2 hj2 hij
      rw [ite_eq_right hmod] at hd
      exact hv.mono (by omega)

private theorem B_outer_polynomial_val (p : ℕ) (a : ℤ) (i j : ℕ) (L : ℤ)
    (hp : p.Prime) (hL : L ≤ 0)
    (hB : Q5ResidueProof.ValAtLeast p L (V.vBEntry a i j)) (k : ℕ) :
    Q5ResidueProof.ValAtLeast p L
      ((Polynomial.C (V.vBEntry a i j) -
        Polynomial.X * Polynomial.C (V.vAEntry a i j)).coeff k) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Polynomial.coeff_sub]
  apply Q5ResidueProof.ValAtLeast.sub
  · rw [Polynomial.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk]
      exact hB
    · rw [ite_eq_right hk]
      exact Q5ResidueProof.ValAtLeast.zero _ _
  · rw [mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    by_cases hk : 1 = k
    · rw [ite_eq_left hk, mul_one]
      exact (Q5ResidueProof.A_val p a i j).mono hL
    · rw [ite_eq_right hk, mul_zero]
      exact Q5ResidueProof.ValAtLeast.zero _ _

/-! ## Entrywise potential domination across all four outer bands -/

private theorem index_lt_sq_of_outer {n p m : ℕ}
    (hn : 0 < n) (h5 : 5 * n < p) (hm : m < 11 * n) :
    m < p ^ 2 := by
  have hp6 : 6 ≤ p := by omega
  have h11 : 11 * n < 2 * p + 2 * n := by omega
  have h2p : 2 * p + 2 * n < p * p := by
    nlinarith
  linarith

private theorem cRow_outer_budget {n p i j : ℕ}
    (hn : 0 < n) (h5 : 5 * n < p) (hU : p ≤ V.vU n)
    (hi : 2 * n ≤ i ∧ i < 6 * n) (hj : n ≤ j ∧ j < 10 * n)
    (hne : i ≠ j) (hmod : i % p = j % p) :
    1 ≤ V.Q5Certificate.q5OuterChi n p j := by
  have hi2p : i < 2 * p := by omega
  have hj2p : j < 2 * p := by omega
  have hrel := mod_eq_of_lt_two_mul hi2p hj2p hne hmod
  have hj_ge : p + 2 * n ≤ j := by omega
  have hp8 : p < 8 * n := by omega
  unfold V.Q5Certificate.q5OuterChi
  by_cases h6 : p < 6 * n
  · have hband1 : 5 * n < p ∧ p < 6 * n := ⟨h5, h6⟩
    rw [if_pos hband1, if_pos hj_ge]
  · have hband23 : 6 * n ≤ p ∧ p < 10 * n := ⟨by omega, by omega⟩
    have hnot1 : ¬ (5 * n < p ∧ p < 6 * n) := by omega
    have hjp : p ≤ j := by omega
    rw [if_neg hnot1, if_pos hband23, if_pos hjp]

private theorem bRow_outer_budget {n p i j : ℕ}
    (hn : 0 < n) (h5 : 5 * n < p) (hU : p ≤ V.vU n)
    (hi : 2 * n ≤ i ∧ i < 6 * n) (hj : n ≤ j ∧ j < 10 * n) :
    (if p ≤ i ∨ p ≤ j then 1 else 0) +
      (if (p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) ∨ (i = j ∧ p ≤ i)
        then 1 else 0) ≤
      V.Q5Certificate.q5OuterLambdaB n p i + V.Q5Certificate.q5OuterChi n p j := by
  have hpU : p < 11 * n := by
    dsimp [V.vU] at hU
    omega
  unfold V.Q5Certificate.q5OuterLambdaB V.Q5Certificate.q5OuterChi
  split_ifs <;> omega

/-- Integer form of `bRow_outer_budget`, stated with exactly the `ℤ`-valued
indicator `if`s produced by `B_outer_val`, so that the caller can close the
budget goal by `exact` instead of asking `omega` to identify an `ℤ`-valued
`if` with the cast of an `ℕ`-valued `if` (which it treats as distinct atoms). -/
private theorem bRow_outer_budget_int {n p i j : ℕ}
    (hn : 0 < n) (h5 : 5 * n < p) (hU : p ≤ V.vU n)
    (hi : 2 * n ≤ i ∧ i < 6 * n) (hj : n ≤ j ∧ j < 10 * n) :
    -(((V.Q5Certificate.q5OuterLambdaB n p i : ℕ) : ℤ) +
        ((V.Q5Certificate.q5OuterChi n p j : ℕ) : ℤ)) ≤
      -(if p ≤ i ∨ p ≤ j then (1 : ℤ) else 0) -
        (if (p ≤ i ∧ j + p ≤ i) ∨ (p ≤ j ∧ i + p ≤ j) ∨ (i = j ∧ p ≤ i)
          then (1 : ℤ) else 0) := by
  have hpU : p < 11 * n := by
    dsimp [V.vU] at hU
    omega
  unfold V.Q5Certificate.q5OuterLambdaB V.Q5Certificate.q5OuterChi
  -- Every branch is a closed linear statement about `n, p, i, j`; the casts
  -- `((1 + 1 : ℕ) : ℤ)` etc. are handled by `omega`'s cast preprocessing.
  split_ifs <;> omega

private theorem vRow_outer_budget {n p j ell : ℕ}
    (hn : 0 < n) (h5 : 5 * n < p) (hU : p ≤ V.vU n)
    (hj : n ≤ j ∧ j < 10 * n) (hell : 1 ≤ ell ∧ ell ≤ n)
    (hdvd : p ∣ j + ell) :
    1 ≤ V.Q5Certificate.q5OuterLambdaV n p ell + V.Q5Certificate.q5OuterChi n p j := by
  unfold V.Q5Certificate.q5OuterLambdaV
  by_cases h10 : p < 10 * n
  · have hband : 5 * n < p ∧ p < 10 * n := ⟨h5, h10⟩
    rw [if_pos hband]
    omega
  · have hnot10 : ¬ (5 * n < p ∧ p < 10 * n) := by omega
    have hband4 : 10 * n ≤ p ∧ p ≤ V.Q5Certificate.q5U n := by
      refine ⟨by omega, ?_⟩
      simpa [V.Q5Certificate.q5U, V.vU] using hU
    rcases hdvd with ⟨k, hk⟩
    have hk1 : k = 1 := by
      have hk0 : 0 < k := by
        by_contra hle
        have hk_zero : k = 0 := by omega
        rw [hk_zero, mul_zero] at hk
        omega
      have hk2 : k < 2 := by
        by_contra hge
        have hge2 : 2 ≤ k := Nat.le_of_not_lt hge
        have hmul : p * 2 ≤ p * k := Nat.mul_le_mul_left p hge2
        omega
      omega
    rw [hk1, mul_one] at hk
    have hcond : n ≤ p - ell ∧ p - ell < 10 * n := by omega
    rw [if_neg hnot10, if_pos hband4, if_pos hcond]
    omega

/-- Coefficientwise valuation lower bound for every entry of `V.vSourceMatrix n a`
in the outer range $5n < p \le 11n - 1$. -/
theorem outer_entry_val (n p : ℕ) (a : ℤ)
    (hn : 0 < n) (hp : p.Prime) (h5 : 5 * n < p) (hU : p ≤ V.vU n)
    (r c : Fin (V.vMatrixSize n)) (k : ℕ) :
    Q5ResidueProof.ValAtLeast p
      (-((rowPot n p r : ℤ) + (colPot n p c : ℤ)))
      ((V.vSourceMatrix n a r c).coeff k) := by
  letI : Fact p.Prime := ⟨hp⟩
  -- `V.vM n` occurs in later goals; this definitional equation lets `omega`
  -- treat `V.vM n` as an atom equal to `4 * n` in hypotheses and goals alike.
  have hM : V.vM n = 4 * n := rfl
  have hj := V.vJIndex_mem n c
  have hj2 : V.vJIndex n c < p ^ 2 :=
    index_lt_sq_of_outer hn h5 (by omega)
  have hr := r.isLt
  simp only [V.vMatrixSize, V.vM, V.vS] at hr
  by_cases hC : r.val < V.vM n
  · have hi_mem : 2 * n ≤ 2 * n + r.val ∧ 2 * n + r.val < 6 * n := by
      simp only [V.vM] at hC
      omega
    have hi2 : 2 * n + r.val < p ^ 2 :=
      index_lt_sq_of_outer hn h5 (by omega)
    have hrow : rowPot n p r = 0 := by simp [rowPot, hC]
    rw [V.vSourceMatrix, if_pos hC, hrow]
    by_cases hij : V.vIIndexNat n r.val = V.vJIndex n c
    · rw [V.vCEntry, if_pos hij, Polynomial.C_0, Polynomial.coeff_zero]
      exact Q5ResidueProof.ValAtLeast.zero _ _
    · have hc := Q5ResidueProof.C_polynomial_val p a (V.vIIndexNat n r.val)
        (V.vJIndex n c) hp hi2 hj2 k
      apply hc.mono
      by_cases hmod : V.vIIndexNat n r.val % p = V.vJIndex n c % p
      · have hchi := cRow_outer_budget hn h5 hU hi_mem hj hij hmod
        have hex : Q5ResidueProof.entryExtra p (V.vIIndexNat n r.val) (V.vJIndex n c) ≤ 1 :=
          Q5ResidueProof.entryExtra_le_one _ _ _
        dsimp [colPot]
        omega
      · have hex : Q5ResidueProof.entryExtra p (V.vIIndexNat n r.val) (V.vJIndex n c) = 0 := by
          simp [Q5ResidueProof.entryExtra, hmod]
        rw [hex]
        dsimp [colPot]
        omega
  · by_cases hB : r.val < 2 * V.vM n
    · have hi_mem : 2 * n ≤ 2 * n + (r.val - V.vM n) ∧ 2 * n + (r.val - V.vM n) < 6 * n := by
        -- uses `hM : V.vM n = 4 * n`, `hC`, `hB`, `hr`; the goal mentions `V.vM n`
        omega
      have hi2p : 2 * n + (r.val - V.vM n) < 2 * p := by omega
      have hj2p : V.vJIndex n c < 2 * p := by omega
      have hi2 : 2 * n + (r.val - V.vM n) < p ^ 2 :=
        index_lt_sq_of_outer hn h5 (by omega)
      have hrow : rowPot n p r = V.Q5Certificate.q5OuterLambdaB n p (2 * n + (r.val - V.vM n)) := by
        simp [rowPot, hC, hB]
      rw [V.vSourceMatrix, if_neg hC, if_pos hB, hrow]
      have hBval := B_outer_val p a (2 * n + (r.val - V.vM n)) (V.vJIndex n c)
        hp hi2p hj2p hi2 hj2
      have hpoly := B_outer_polynomial_val p a (2 * n + (r.val - V.vM n)) (V.vJIndex n c)
        (-(if p ≤ 2 * n + (r.val - V.vM n) ∨ p ≤ V.vJIndex n c then 1 else 0) -
          (if (p ≤ 2 * n + (r.val - V.vM n) ∧ V.vJIndex n c + p ≤ 2 * n + (r.val - V.vM n)) ∨
              (p ≤ V.vJIndex n c ∧ 2 * n + (r.val - V.vM n) + p ≤ V.vJIndex n c) ∨
              (2 * n + (r.val - V.vM n) = V.vJIndex n c ∧ p ≤ 2 * n + (r.val - V.vM n))
            then 1 else 0))
        hp (by split_ifs <;> omega) hBval k
      apply hpoly.mono
      -- `colPot n p c` is definitionally `q5OuterChi n p (V.vJIndex n c)`, and the
      -- two `ℤ`-valued indicators are literally those of `bRow_outer_budget_int`.
      first
        | exact bRow_outer_budget_int (i := 2 * n + (r.val - V.vM n))
            (j := V.vJIndex n c) hn h5 hU hi_mem hj
        | (have hbud := bRow_outer_budget_int (i := 2 * n + (r.val - V.vM n))
              (j := V.vJIndex n c) hn h5 hU hi_mem hj
           dsimp only [colPot]
           exact hbud)
    · have hell_mem : 1 ≤ 1 + (r.val - 2 * V.vM n) ∧ 1 + (r.val - 2 * V.vM n) ≤ n := by
        -- uses `hM : V.vM n = 4 * n`, `hC`, `hB`, `hr`; the goal mentions `V.vM n`
        omega
      have hpos : 0 < V.vJIndex n c + (1 + (r.val - 2 * V.vM n)) := by omega
      have hbound : V.vJIndex n c + (1 + (r.val - 2 * V.vM n)) < p ^ 2 :=
        index_lt_sq_of_outer hn h5 (by omega)
      have hrow : rowPot n p r = V.Q5Certificate.q5OuterLambdaV n p (1 + (r.val - 2 * V.vM n)) := by
        simp [rowPot, hC, hB]
      rw [V.vSourceMatrix, if_neg hC, if_neg hB, hrow]
      have hV := Q5ResidueProof.V_polynomial_val p (V.vJIndex n c)
        (1 + (r.val - 2 * V.vM n)) hp hpos hbound k
      apply hV.mono
      by_cases hdvd : p ∣ V.vJIndex n c + (1 + (r.val - 2 * V.vM n))
      · rw [if_pos hdvd]
        have hbud := vRow_outer_budget hn h5 hU hj hell_mem hdvd
        dsimp [colPot]
        omega
      · rw [if_neg hdvd]
        dsimp [colPot]
        omega

/-! ## Total potential sum across all four outer bands -/

private theorem sum_range_ite_ge (L a b : ℕ) (ha : a ≤ b) (hb : b ≤ a + L) :
    (∑ k ∈ Finset.range L, if b ≤ a + k then (1 : ℕ) else 0) = a + L - b := by
  have hsplit := Finset.sum_range_add
    (fun k => if b ≤ a + k then (1 : ℕ) else 0) (b - a) (a + L - b)
  have hL : (b - a) + (a + L - b) = L := by omega
  rw [hL] at hsplit
  rw [hsplit]
  have h1 : (∑ k ∈ Finset.range (b - a), if b ≤ a + k then (1 : ℕ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < b - a := Finset.mem_range.mp hk
    have hnot : ¬ b ≤ a + k := by omega
    simp [hnot]
  have h2 : (∑ k ∈ Finset.range (a + L - b),
      if b ≤ a + (b - a + k) then (1 : ℕ) else 0) = a + L - b := by
    trans (∑ _k ∈ Finset.range (a + L - b), (1 : ℕ))
    · apply Finset.sum_congr rfl
      intro k _hk
      have hge : b ≤ a + (b - a + k) := by omega
      simp [hge]
    · simp
  omega

private theorem sum_range_ite_lt (L a b : ℕ) (ha : a ≤ b) (hb : b ≤ a + L) :
    (∑ k ∈ Finset.range L, if a + k < b then (1 : ℕ) else 0) = b - a := by
  have hsplit := Finset.sum_range_add
    (fun k => if a + k < b then (1 : ℕ) else 0) (b - a) (a + L - b)
  have hL : (b - a) + (a + L - b) = L := by omega
  rw [hL] at hsplit
  rw [hsplit]
  have h1 : (∑ k ∈ Finset.range (b - a), if a + k < b then (1 : ℕ) else 0) = b - a := by
    trans (∑ _k ∈ Finset.range (b - a), (1 : ℕ))
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < b - a := Finset.mem_range.mp hk
      have hlt : a + k < b := by omega
      simp [hlt]
    · simp
  have h2 : (∑ k ∈ Finset.range (a + L - b),
      if a + (b - a + k) < b then (1 : ℕ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _hk
    have hnot : ¬ a + (b - a + k) < b := by omega
    simp [hnot]
  omega

private theorem sum_rowPot_eq (n p : ℕ) :
    (∑ r : Fin (V.vMatrixSize n), rowPot n p r) =
      (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) +
        (∑ r ∈ Finset.range n, V.Q5Certificate.q5OuterLambdaV n p (1 + r)) := by
  change (∑ r : Fin (V.vMatrixSize n), rowPotNat n p r.val) = _
  rw [Fin.sum_univ_eq_sum_range (rowPotNat n p) (V.vMatrixSize n)]
  have hsize : V.vMatrixSize n = (4 * n + 4 * n) + n := by
    simp [V.vMatrixSize, V.vM, V.vS]
    omega
  rw [hsize, Finset.sum_range_add (rowPotNat n p) (4 * n + 4 * n) n,
    Finset.sum_range_add (rowPotNat n p) (4 * n) (4 * n)]
  have hC : (∑ r ∈ Finset.range (4 * n), rowPotNat n p r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr' : r < V.vM n := by
      simp only [V.vM]
      exact Finset.mem_range.mp hr
    simp [rowPotNat, hr']
  have hB : (∑ r ∈ Finset.range (4 * n), rowPotNat n p (4 * n + r)) =
      ∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < 4 * n := Finset.mem_range.mp hr
    have hnotC : ¬ 4 * n + r < V.vM n := by simp [V.vM]
    have hltB : 4 * n + r < 2 * V.vM n := by simp [V.vM]; omega
    have hsub : 4 * n + r - V.vM n = r := by simp [V.vM]
    simp [rowPotNat, hnotC, hltB, hsub]
  have hV : (∑ r ∈ Finset.range n, rowPotNat n p ((4 * n + 4 * n) + r)) =
      ∑ r ∈ Finset.range n, V.Q5Certificate.q5OuterLambdaV n p (1 + r) := by
    apply Finset.sum_congr rfl
    intro r _hr
    have hnotC : ¬ (4 * n + 4 * n) + r < V.vM n := by simp [V.vM]; omega
    have hnotB : ¬ (4 * n + 4 * n) + r < 2 * V.vM n := by simp [V.vM]; omega
    have hsub : (4 * n + 4 * n) + r - 2 * V.vM n = r := by simp [V.vM]; omega
    simp [rowPotNat, hnotC, hnotB, hsub]
  rw [hC, zero_add, hB, hV]

private theorem sum_colPot_eq (n p : ℕ) :
    (∑ c : Fin (V.vMatrixSize n), colPot n p c) =
      ∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c) := by
  change (∑ c : Fin (V.vMatrixSize n), V.Q5Certificate.q5OuterChi n p (n + c.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun c => V.Q5Certificate.q5OuterChi n p (n + c)) (V.vMatrixSize n)]
  rw [V.vMatrixSize_eq]

private theorem sum_lambdaB_band1 {n p : ℕ} (h5 : 5 * n < p) (h6 : p < 6 * n) :
    (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) =
      10 * n - p := by
  have hband : 5 * n < p ∧ p < 6 * n := ⟨h5, h6⟩
  have hcongr :
      (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) =
        ∑ r ∈ Finset.range (4 * n), (1 + if p ≤ 2 * n + r then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro r _hr
    simp [V.Q5Certificate.q5OuterLambdaB, hband]
  rw [hcongr, Finset.sum_add_distrib]
  have h1 : (∑ _r ∈ Finset.range (4 * n), (1 : ℕ)) = 4 * n := by simp
  have h2 := sum_range_ite_ge (4 * n) (2 * n) p (by omega) (by omega)
  omega

private theorem sum_lambdaB_band2 {n p : ℕ} (h6 : 6 * n ≤ p) (h8 : p < 8 * n) :
    (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) =
      8 * n - p := by
  have hnot1 : ¬ (5 * n < p ∧ p < 6 * n) := by omega
  have hband2 : 6 * n ≤ p ∧ p < 8 * n := ⟨h6, h8⟩
  have hcongr :
      (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) =
        ∑ r ∈ Finset.range (4 * n), (if (2 * n + p) + r < 10 * n then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro r _hr
    have heq : (2 * n + r + p < 10 * n) ↔ ((2 * n + p) + r < 10 * n) := by omega
    simp [V.Q5Certificate.q5OuterLambdaB, hnot1, hband2, heq]
  rw [hcongr]
  have h := sum_range_ite_lt (4 * n) (2 * n + p) (10 * n) (by omega) (by omega)
  omega

private theorem sum_lambdaB_band34 {n p : ℕ} (h8 : 8 * n ≤ p) :
    (∑ r ∈ Finset.range (4 * n), V.Q5Certificate.q5OuterLambdaB n p (2 * n + r)) = 0 := by
  have hnot1 : ¬ (5 * n < p ∧ p < 6 * n) := by omega
  have hnot2 : ¬ (6 * n ≤ p ∧ p < 8 * n) := by omega
  apply Finset.sum_eq_zero
  intro r _hr
  simp [V.Q5Certificate.q5OuterLambdaB, hnot1, hnot2]

private theorem sum_lambdaV_band123 {n p : ℕ} (h5 : 5 * n < p) (h10 : p < 10 * n) :
    (∑ r ∈ Finset.range n, V.Q5Certificate.q5OuterLambdaV n p (1 + r)) = n := by
  have hband : 5 * n < p ∧ p < 10 * n := ⟨h5, h10⟩
  trans (∑ _r ∈ Finset.range n, (1 : ℕ))
  · apply Finset.sum_congr rfl
    intro r _hr
    simp [V.Q5Certificate.q5OuterLambdaV, hband]
  · simp

private theorem sum_lambdaV_band4 {n p : ℕ} (hn : 0 < n)
    (h10 : 10 * n ≤ p) (hU : p ≤ V.vU n) :
    (∑ r ∈ Finset.range n, V.Q5Certificate.q5OuterLambdaV n p (1 + r)) = 11 * n - p := by
  have hnot1 : ¬ (5 * n < p ∧ p < 10 * n) := by omega
  have hband4 : 10 * n ≤ p ∧ p ≤ V.Q5Certificate.q5U n := by
    refine ⟨h10, ?_⟩
    simpa [V.Q5Certificate.q5U, V.vU] using hU
  have hp11 : p < 11 * n := by
    dsimp [V.vU] at hU
    omega
  have hcongr :
      (∑ r ∈ Finset.range n, V.Q5Certificate.q5OuterLambdaV n p (1 + r)) =
        ∑ r ∈ Finset.range n, (if p - 10 * n ≤ 0 + r then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < n := Finset.mem_range.mp hr
    have heq : (n ≤ p - (1 + r) ∧ p - (1 + r) < 10 * n) ↔ (p - 10 * n ≤ 0 + r) := by omega
    simp [V.Q5Certificate.q5OuterLambdaV, hnot1, hband4, heq]
  rw [hcongr]
  have h := sum_range_ite_ge n 0 (p - 10 * n) (by omega) (by omega)
  omega

private theorem sum_chi_band1 {n p : ℕ} (h5 : 5 * n < p) (h6 : p < 6 * n) :
    (∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c)) = 8 * n - p := by
  have hband1 : 5 * n < p ∧ p < 6 * n := ⟨h5, h6⟩
  have hcongr :
      (∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c)) =
        ∑ c ∈ Finset.range (9 * n), (if p + 2 * n ≤ n + c then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro c _hc
    simp [V.Q5Certificate.q5OuterChi, hband1]
  rw [hcongr]
  have h := sum_range_ite_ge (9 * n) n (p + 2 * n) (by omega) (by omega)
  omega

private theorem sum_chi_band23 {n p : ℕ} (h6 : 6 * n ≤ p) (h10 : p < 10 * n) :
    (∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c)) = 10 * n - p := by
  have hnot1 : ¬ (5 * n < p ∧ p < 6 * n) := by omega
  have hband23 : 6 * n ≤ p ∧ p < 10 * n := ⟨h6, h10⟩
  have hcongr :
      (∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c)) =
        ∑ c ∈ Finset.range (9 * n), (if p ≤ n + c then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro c _hc
    simp [V.Q5Certificate.q5OuterChi, hnot1, hband23]
  rw [hcongr]
  have h := sum_range_ite_ge (9 * n) n p (by omega) (by omega)
  omega

private theorem sum_chi_band4 {n p : ℕ} (h10 : 10 * n ≤ p) :
    (∑ c ∈ Finset.range (9 * n), V.Q5Certificate.q5OuterChi n p (n + c)) = 0 := by
  have hnot1 : ¬ (5 * n < p ∧ p < 6 * n) := by omega
  have hnot23 : ¬ (6 * n ≤ p ∧ p < 10 * n) := by omega
  apply Finset.sum_eq_zero
  intro c _hc
  simp [V.Q5Certificate.q5OuterChi, hnot1, hnot23]

/-- Proposition `prop:v-outer-total` (`v-arithmetic.tex:305-318`): the sum of row
and column potentials equals `q5OuterCost n p` across all four outer bands. -/
theorem outer_pot_sum (n p : ℕ)
    (hn : 0 < n) (h5 : 5 * n < p) (hU : p ≤ V.vU n) :
    (∑ r : Fin (V.vMatrixSize n), (rowPot n p r : ℤ)) +
      (∑ c : Fin (V.vMatrixSize n), (colPot n p c : ℤ)) =
      V.Q5Certificate.q5OuterCost n p := by
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_rowPot_eq, sum_colPot_eq]
  have hpU' : p ≤ V.Q5Certificate.q5U n := by simpa [V.Q5Certificate.q5U, V.vU] using hU
  have hp11 : p < 11 * n := by
    dsimp [V.vU] at hU
    omega
  rcases V.Q5Certificate.q5_outer_partition hn h5 hpU' with
    ⟨_, h6⟩ | ⟨h6, h8⟩ | ⟨h8, h10⟩ | ⟨h10, _⟩
  · rw [sum_lambdaB_band1 h5 h6, sum_lambdaV_band123 h5 (by omega), sum_chi_band1 h5 h6]
    have hband : 5 * n < p ∧ p < 8 * n := ⟨h5, by omega⟩
    unfold V.Q5Certificate.q5OuterCost
    rw [if_pos hband]
    omega
  · rw [sum_lambdaB_band2 h6 h8, sum_lambdaV_band123 h5 (by omega), sum_chi_band23 h6 (by omega)]
    have hband : 5 * n < p ∧ p < 8 * n := ⟨h5, h8⟩
    unfold V.Q5Certificate.q5OuterCost
    rw [if_pos hband]
    omega
  · rw [sum_lambdaB_band34 h8, sum_lambdaV_band123 h5 h10, sum_chi_band23 (by omega) h10]
    have hnot1 : ¬ (5 * n < p ∧ p < 8 * n) := by omega
    have hband : 8 * n ≤ p ∧ p ≤ V.Q5Certificate.q5U n := ⟨h8, hpU'⟩
    unfold V.Q5Certificate.q5OuterCost
    rw [if_neg hnot1, if_pos hband]
    omega
  · rw [sum_lambdaB_band34 (by omega), sum_lambdaV_band4 hn h10 hU, sum_chi_band4 h10]
    have hnot1 : ¬ (5 * n < p ∧ p < 8 * n) := by omega
    have hband : 8 * n ≤ p ∧ p ≤ V.Q5Certificate.q5U n := ⟨by omega, hpU'⟩
    unfold V.Q5Certificate.q5OuterCost
    rw [if_neg hnot1, if_pos hband]
    omega

/-! ## Determinant coefficient and Gauss valuation lower bounds -/

theorem outer_det_coeff_val (n p : ℕ) (a : ℤ)
    (hn : 0 < n) (hp : p.Prime) (h5 : 5 * n < p) (hU : p ≤ V.vU n) (k : ℕ) :
    Q5ResidueProof.ValAtLeast p (-V.Q5Certificate.q5OuterCost n p)
      ((V.vPolynomial n a).coeff k) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Q5ResidueProof.det_coeff_valAtLeast (V.vSourceMatrix n a)
    (fun r c => -((rowPot n p r : ℤ) + (colPot n p c : ℤ)))
  · exact outer_entry_val n p a hn hp h5 hU
  · intro σ
    have hperm :
        (∑ c : Fin (V.vMatrixSize n), (rowPot n p (σ c) : ℤ)) =
          ∑ r : Fin (V.vMatrixSize n), (rowPot n p r : ℤ) :=
      Equiv.Perm.sum_comp σ Finset.univ (fun r => (rowPot n p r : ℤ)) (by simp)
    have hsum :
        (∑ c : Fin (V.vMatrixSize n), -((rowPot n p (σ c) : ℤ) + (colPot n p c : ℤ))) =
          -V.Q5Certificate.q5OuterCost n p := by
      rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hperm,
        outer_pot_sum n p hn h5 hU]
    exact hsum.ge

theorem q5OuterCost_nonneg (n p : ℕ) : 0 ≤ V.Q5Certificate.q5OuterCost n p := by
  unfold V.Q5Certificate.q5OuterCost V.Q5Certificate.q5U
  split_ifs <;> omega

/-- Uniform outer-pole Gauss valuation lower bound in `Li2Lean.B3.H4Outer`. -/
theorem v13_outer_pole_gauss_lower (a : ℤ) {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (h5 : 5 * n < p)
    (hU : p ≤ V.vU n) :
    V.actualGaussValuation p (V.vPolynomial n a) ≥
      -V.Q5Certificate.q5OuterCost n p := by
  classical
  unfold V.actualGaussValuation
  split_ifs with hsupport
  · apply Finset.le_inf'
    intro k hk
    exact (outer_det_coeff_val n p a hn hp h5 hU k).resolve_left
      (Polynomial.mem_support_iff.mp hk)
  · have hnonneg := q5OuterCost_nonneg n p
    omega

end
end Li2Lean.B3.H4Outer

namespace Li2Lean.B3

noncomputable section

/-- Uniform outer-pole coefficient estimate from v13 `v-arithmetic.tex:289-318`.
Re-exported in `Li2Lean.B3` to match `H4Regimes.lean`. -/
theorem v13_outer_pole_gauss_lower (a : ℤ) {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (h5 : 5 * n < p)
    (hU : p ≤ V.vU n) :
    V.actualGaussValuation p (V.vPolynomial n a) ≥
      -V.Q5Certificate.q5OuterCost n p :=
  H4Outer.v13_outer_pole_gauss_lower a hn hp h5 hU

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13_outer_pole_gauss_lower
