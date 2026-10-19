/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ISoundTab
import Li2Lean.V.EnergyCertI.ITrans
import Li2Lean.V.EnergyCertI.IEnergyEval

set_option maxRecDepth 100000

/-!
# Integer kit soundness, part 3: series tails, `logDy`, `logQ`, `atanLe`, `atanQ` (K-5 .. K-9)

Generated the release date (release source, elaborated).  Verification notes are retained for context.

Requires the patched `ITrans.lean` of this bundle (the `sorry` statement block
of the v2 source removed; the definitions are unchanged byte for byte).

Analytic inputs (all already proved, none new):
* Mathlib `Real.abs_log_sub_add_sum_range_le` (log series with remainder
  `|x|^(n+1)/(1-|x|)`), `Real.log_le_sub_one_of_pos`, `Real.log_le_log`,
  `Real.log_mul/log_div/log_pow/log_inv`, `Real.arctan_inv_of_pos`, `Real.arctan_neg`;
* P0 `arctan_series_bound` (remainder `|x|^(2n+1)/(2n+1)`), `arctan_shift`,
  `log_le_add_div` (`log b ≤ log a + (b-a)/a`).
-/

namespace Li2Lean.V.EnergyCertI.IK

open Li2Lean.P0.CA.Contour

/-! ## K-5 (a): `log (1 + u)` series -/

/-- Summand of `Σ (-1)^m u^(m+1)/(m+1)`. -/
noncomputable def lterm (u : ℝ) (m : ℕ) : ℝ := (-1) ^ m * u ^ (m + 1) / ((m : ℝ) + 1)

theorem logStep_val {un ud : ℕ} (hd : 0 < ud) (i : ℕ) :
    (((un : ℝ) / ud) ^ (i + 1) / ((i : ℝ) + 1)) * S =
      ((un ^ (i + 1) * S : ℕ) : ℝ) / (((i + 1) * ud ^ (i + 1) : ℕ) : ℝ) := by
  have hud : (ud : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [div_pow]
  first
    | (field_simp; ring)
    | field_simp

theorem logSerAux_mem {un ud : ℕ} (hd : 0 < ud) :
    ∀ (n i : ℕ) (acc : IV) (a : ℝ), IV.mem acc a →
      IV.mem (logSerAux un ud n i acc)
        (a + ∑ l ∈ Finset.range n, lterm ((un : ℝ) / ud) (i + l))
  | 0, i, acc, a, h => by simpa [logSerAux] using h
  | n + 1, i, acc, a, h => by
      have hden : 0 < (i + 1) * ud ^ (i + 1) := Nat.mul_pos (by omega) (pow_pos hd _)
      have hT := natTerm_mem (num := un ^ (i + 1) * S) hden (logStep_val hd i)
      have hstep : IV.mem
          (if i % 2 = 0 then
            ((acc.1 + Int.ofNat ((un ^ (i + 1) * S) / ((i + 1) * ud ^ (i + 1))),
              acc.2 + Int.ofNat (cdivN (un ^ (i + 1) * S) ((i + 1) * ud ^ (i + 1)))) : IV)
           else
            ((acc.1 - Int.ofNat (cdivN (un ^ (i + 1) * S) ((i + 1) * ud ^ (i + 1))),
              acc.2 - Int.ofNat ((un ^ (i + 1) * S) / ((i + 1) * ud ^ (i + 1)))) : IV))
          (a + lterm ((un : ℝ) / ud) i) := by
        split_ifs with hi
        · have e : lterm ((un : ℝ) / ud) i = ((un : ℝ) / ud) ^ (i + 1) / ((i : ℝ) + 1) := by
            unfold lterm; rw [Even.neg_one_pow (Nat.even_iff.mpr hi)]; ring
          rw [e]
          exact add_mem h hT
        · have e : lterm ((un : ℝ) / ud) i = -(((un : ℝ) / ud) ^ (i + 1) / ((i : ℝ) + 1)) := by
            unfold lterm; rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]; ring
          rw [e, ← sub_eq_add_neg]
          exact sub_mem h hT
      have ih := logSerAux_mem (un := un) hd n (i + 1) _ _ hstep
      have e2 : a + ∑ l ∈ Finset.range (n + 1), lterm ((un : ℝ) / ud) (i + l) =
          (a + lterm ((un : ℝ) / ud) i) +
            ∑ l ∈ Finset.range n, lterm ((un : ℝ) / ud) (i + 1 + l) := by
        rw [Finset.sum_range_succ']
        have hsum :
            (∑ k ∈ Finset.range n, lterm ((un : ℝ) / ud) (i + (k + 1))) =
              ∑ l ∈ Finset.range n, lterm ((un : ℝ) / ud) (i + 1 + l) := by
          apply Finset.sum_congr rfl
          intro l hl
          congr 1
          omega
        simp only [Nat.add_zero]
        rw [hsum]
        ring
      rw [e2]
      simp only [logSerAux]   -- one unfolding step; `exact ih` also works by defeq [Verified]
      exact ih

/-- K-5 -/
theorem logSer_mem (nt : Nat) {un ud : Nat} (hd : 0 < ud) (hu : 256 * un ≤ ud) :
    IV.mem (logSer nt un ud) (Real.log (1 + (un : ℝ) / ud)) := by
  have hud : (0 : ℝ) < ud := by exact_mod_cast hd
  have hlt : un < ud := by omega
  have hltR : (un : ℝ) < ud := by exact_mod_cast hlt
  have hu0 : (0 : ℝ) ≤ (un : ℝ) / ud := div_nonneg (Nat.cast_nonneg _) hud.le
  have hu1 : (un : ℝ) / ud < 1 := by rw [div_lt_one hud]; exact hltR
  have hS := S_pos
  -- the accumulated partial sum
  have hacc := logSerAux_mem (un := un) hd nt 0 zero 0 zero_mem
  simp only [zero_add] at hacc
  -- Mathlib remainder at `x = -u`
  have hM := Real.abs_log_sub_add_sum_range_le (x := -((un : ℝ) / ud))
    (by rw [abs_neg, abs_of_nonneg hu0]; exact hu1) nt
  rw [abs_neg, abs_of_nonneg hu0, sub_neg_eq_add] at hM
  have hsum : ∑ i ∈ Finset.range nt, (-((un : ℝ) / ud)) ^ (i + 1) / ((i : ℝ) + 1) =
      -∑ i ∈ Finset.range nt, lterm ((un : ℝ) / ud) i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold lterm
    rw [neg_pow ((un : ℝ) / ud)]
    ring
  rw [hsum] at hM
  have hb := abs_le.mp hM
  -- the remainder term
  have hden : 0 < ud ^ nt * (ud - un) := Nat.mul_pos (pow_pos hd _) (by omega)
  have hR : ((un : ℝ) / ud) ^ (nt + 1) / (1 - (un : ℝ) / ud) * S =
      ((un ^ (nt + 1) * S : ℕ) : ℝ) / ((ud ^ nt * (ud - un) : ℕ) : ℝ) := by
    have hne : (ud : ℝ) - un ≠ 0 := (sub_pos.mpr hltR).ne'
    have hud' : (ud : ℝ) ≠ 0 := hud.ne'
    have e1 : 1 - (un : ℝ) / ud = ((ud : ℝ) - un) / ud := by
      first
        | (field_simp; ring)
        | field_simp
    rw [e1, div_pow]
    push_cast [Nat.cast_sub hlt.le]
    first
      | (field_simp; ring)
      | field_simp
  have hrem := div_le_cdivN (un ^ (nt + 1) * S) hden
  rw [← hR] at hrem
  -- assemble
  show IV.mem (((logSerAux un ud nt 0 zero).1 -
      Int.ofNat (cdivN (un ^ (nt + 1) * S) (ud ^ nt * (ud - un))),
    (logSerAux un ud nt 0 zero).2 +
      Int.ofNat (cdivN (un ^ (nt + 1) * S) (ud ^ nt * (ud - un)))) : IV) _
  rw [mem_iff] at hacc ⊢
  simp only [Int.ofNat_eq_coe]
  push_cast
  set P := ∑ i ∈ Finset.range nt, lterm ((un : ℝ) / ud) i
  set R := ((un : ℝ) / ud) ^ (nt + 1) / (1 - (un : ℝ) / ud)
  set L := Real.log (1 + (un : ℝ) / ud)
  have m1 := mul_le_mul_of_nonneg_right (show P - R ≤ L by linarith [hb.1]) hS.le
  have m2 := mul_le_mul_of_nonneg_right (show L ≤ P + R by linarith [hb.2]) hS.le
  have e3 : (P - R) * S = P * S - R * S := by ring
  have e4 : (P + R) * S = P * S + R * S := by ring
  constructor <;> linarith [hacc.1, hacc.2, hrem, m1, m2, e3, e4]

/-! ## K-5 (b): `arctan v` series -/

/-- Summand of P0 `Sr`. -/
noncomputable def aterm (v : ℝ) (k : ℕ) : ℝ := (-1) ^ k * v ^ (2 * k + 1) / (2 * k + 1)

theorem Sr_eq_sum (n : ℕ) (v : ℝ) : Sr n v = ∑ k ∈ Finset.range n, aterm v k := rfl

theorem atanStep_val {vn vd : ℕ} (hd : 0 < vd) (k : ℕ) :
    (((vn : ℝ) / vd) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) * S =
      ((vn ^ (2 * k + 1) * S : ℕ) : ℝ) / (((2 * k + 1) * vd ^ (2 * k + 1) : ℕ) : ℝ) := by
  have hvd : (vd : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [div_pow]
  first
    | (field_simp; ring)
    | field_simp

theorem atanSerAux_mem {vn vd : ℕ} (hd : 0 < vd) :
    ∀ (n k : ℕ) (acc : IV) (a : ℝ), IV.mem acc a →
      IV.mem (atanSerAux vn vd n k acc)
        (a + ∑ l ∈ Finset.range n, aterm ((vn : ℝ) / vd) (k + l))
  | 0, k, acc, a, h => by simpa [atanSerAux] using h
  | n + 1, k, acc, a, h => by
      have hden : 0 < (2 * k + 1) * vd ^ (2 * k + 1) := Nat.mul_pos (by omega) (pow_pos hd _)
      have hT := natTerm_mem (num := vn ^ (2 * k + 1) * S) hden (atanStep_val hd k)
      have hstep : IV.mem
          (if k % 2 = 0 then
            ((acc.1 + Int.ofNat ((vn ^ (2 * k + 1) * S) / ((2 * k + 1) * vd ^ (2 * k + 1))),
              acc.2 + Int.ofNat (cdivN (vn ^ (2 * k + 1) * S) ((2 * k + 1) * vd ^ (2 * k + 1)))) : IV)
           else
            ((acc.1 - Int.ofNat (cdivN (vn ^ (2 * k + 1) * S) ((2 * k + 1) * vd ^ (2 * k + 1))),
              acc.2 - Int.ofNat ((vn ^ (2 * k + 1) * S) / ((2 * k + 1) * vd ^ (2 * k + 1)))) : IV))
          (a + aterm ((vn : ℝ) / vd) k) := by
        split_ifs with hk
        · have e : aterm ((vn : ℝ) / vd) k =
              ((vn : ℝ) / vd) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
            unfold aterm; rw [Even.neg_one_pow (Nat.even_iff.mpr hk)]; ring
          rw [e]
          exact add_mem h hT
        · have e : aterm ((vn : ℝ) / vd) k =
              -(((vn : ℝ) / vd) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) := by
            unfold aterm; rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]; ring
          rw [e, ← sub_eq_add_neg]
          exact sub_mem h hT
      have ih := atanSerAux_mem (vn := vn) hd n (k + 1) _ _ hstep
      have e2 : a + ∑ l ∈ Finset.range (n + 1), aterm ((vn : ℝ) / vd) (k + l) =
          (a + aterm ((vn : ℝ) / vd) k) +
            ∑ l ∈ Finset.range n, aterm ((vn : ℝ) / vd) (k + 1 + l) := by
        rw [Finset.sum_range_succ']
        have hsum :
            (∑ k_1 ∈ Finset.range n, aterm ((vn : ℝ) / vd) (k + (k_1 + 1))) =
              ∑ l ∈ Finset.range n, aterm ((vn : ℝ) / vd) (k + 1 + l) := by
          apply Finset.sum_congr rfl
          intro l hl
          congr 1
          omega
        simp only [Nat.add_zero]
        rw [hsum]
        ring
      rw [e2]
      simp only [atanSerAux]
      exact ih

/-- K-5.  (`hv` is not needed for soundness; kept for the Generated's signature.) -/
theorem atanSer_mem (nt : Nat) {vn vd : Nat} (hd : 0 < vd) (_hv : 256 * vn ≤ vd) :
    IV.mem (atanSer nt vn vd) (Real.arctan ((vn : ℝ) / vd)) := by
  have hvd : (0 : ℝ) < vd := by exact_mod_cast hd
  have hv0 : (0 : ℝ) ≤ (vn : ℝ) / vd := div_nonneg (Nat.cast_nonneg _) hvd.le
  have hS := S_pos
  have hacc := atanSerAux_mem (vn := vn) hd nt 0 zero 0 zero_mem
  simp only [zero_add] at hacc
  have hB := arctan_series_bound nt ((vn : ℝ) / vd)
  rw [Sr_eq_sum, abs_of_nonneg hv0] at hB
  have hb := abs_le.mp hB
  have hden : 0 < (2 * nt + 1) * vd ^ (2 * nt + 1) := Nat.mul_pos (by omega) (pow_pos hd _)
  have hrem := div_le_cdivN (vn ^ (2 * nt + 1) * S) hden
  rw [← atanStep_val hd nt] at hrem
  show IV.mem (((atanSerAux vn vd nt 0 zero).1 -
      Int.ofNat (cdivN (vn ^ (2 * nt + 1) * S) ((2 * nt + 1) * vd ^ (2 * nt + 1))),
    (atanSerAux vn vd nt 0 zero).2 +
      Int.ofNat (cdivN (vn ^ (2 * nt + 1) * S) ((2 * nt + 1) * vd ^ (2 * nt + 1)))) : IV) _
  rw [mem_iff] at hacc ⊢
  simp only [Int.ofNat_eq_coe]
  push_cast
  set P := ∑ i ∈ Finset.range nt, aterm ((vn : ℝ) / vd) i
  set R := ((vn : ℝ) / vd) ^ (2 * nt + 1) / (2 * (nt : ℝ) + 1)
  set L := Real.arctan ((vn : ℝ) / vd)
  have m1 := mul_le_mul_of_nonneg_right (show P - R ≤ L by linarith [hb.1]) hS.le
  have m2 := mul_le_mul_of_nonneg_right (show L ≤ P + R by linarith [hb.2]) hS.le
  have e3 : (P - R) * S = P * S - R * S := by ring
  have e4 : (P + R) * S = P * S + R * S := by ring
  constructor <;> linarith [hacc.1, hacc.2, hrem, m1, m2, e3, e4]

/-! ## K-6: `logDy` -/

theorem SL_real : (SL : ℝ) = 2 ^ 192 := by norm_num [SL]

theorem SL_pos : (0 : ℝ) < (SL : ℝ) := by rw [SL_real]; positivity

theorem SL_pos_nat : 0 < SL := by norm_num [SL]

/-- `log (m/2^192) ∈ [1 - 2^192/m, m/2^192 - 1]`. -/
theorem logFallback_mem {m : ℕ} (hm : 0 < m) :
    IV.mem (logFallback m) (Real.log ((m : ℝ) / SL)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hSL := SL_pos
  have hS := S_pos
  have hx : 0 < (m : ℝ) / SL := div_pos hmR hSL
  have hup := Real.log_le_sub_one_of_pos hx
  have hlo : 1 - (SL : ℝ) / m ≤ Real.log ((m : ℝ) / SL) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv, inv_div] at h
    linarith
  have c1 := div_le_cdivN (S * SL) hm
  have c2 := div_le_cdivN (m * S) SL_pos_nat
  push_cast at c1 c2
  have m1 := mul_le_mul_of_nonneg_right hlo hS.le
  have m2 := mul_le_mul_of_nonneg_right hup hS.le
  have e1 : (1 - (SL : ℝ) / m) * S = S - S * SL / m := by ring
  have e2 : ((m : ℝ) / SL - 1) * S = m * S / SL - S := by ring
  unfold logFallback
  rw [mem_iff]
  simp only [Int.ofNat_eq_coe]
  push_cast
  constructor <;> linarith [m1, m2, e1, e2, c1, c2]

theorem log_split {m e t : ℕ} (hm : 0 < m) (ht : 0 < t) :
    Real.log ((m : ℝ) / SL) = ((e : ℝ) - 192) * Real.log 2 + Real.log ((t : ℝ) / 256) +
      Real.log (256 * (m : ℝ) / ((t : ℝ) * 2 ^ e)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have h1 : (m : ℝ) / SL = (2 : ℝ) ^ e / 2 ^ 192 *
      ((t : ℝ) / 256 * (256 * (m : ℝ) / ((t : ℝ) * 2 ^ e))) := by
    rw [SL_real]
    have ht0 : (t : ℝ) ≠ 0 := htR.ne'
    have h2e0 : (2 : ℝ) ^ e ≠ 0 := h2e.ne'
    first
      | (field_simp; ring)
      | field_simp
  have hA : (2 : ℝ) ^ e / 2 ^ 192 ≠ 0 := by positivity
  have hB : (t : ℝ) / 256 ≠ 0 := div_ne_zero htR.ne' (by norm_num)
  have hC : 256 * (m : ℝ) / ((t : ℝ) * 2 ^ e) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hmR.ne') (mul_ne_zero htR.ne' h2e.ne')
  rw [h1, Real.log_mul hA (mul_ne_zero hB hC), Real.log_mul hB hC,
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- K-6 (no lemma about `bitlen` is used: the guard `p ≤ m < 2p` is tested at run time). -/
theorem logDy_mem (nt : Nat) {m : Nat} (hm : 0 < m) :
    IV.mem (logDy nt m) (Real.log ((m : ℝ) / (SL : ℝ))) := by
  unfold logDy
  dsimp only            -- zeta-reduce the `let`s  [Verified]
  generalize bitlen m - 1 = e
  split_ifs with hg
  · obtain ⟨_, hp1, hp2⟩ := hg
    have hp0 : 0 < 2 ^ e := pow_pos (by norm_num) e
    set t := 256 * m / 2 ^ e with ht_def
    have ht1 : 256 ≤ t := (Nat.le_div_iff_mul_le hp0).2 (Nat.mul_le_mul_left 256 hp1)
    have ht2 : t < 512 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
    have htp : t * 2 ^ e ≤ 256 * m := Nat.div_mul_le_self _ _
    have hdm : t * 2 ^ e + (256 * m) % 2 ^ e = 256 * m := by
      rw [Nat.mul_comm t]; exact Nat.div_add_mod (256 * m) (2 ^ e)
    have hmod := Nat.mod_lt (256 * m) hp0
    have hgt : 256 * 2 ^ e ≤ t * 2 ^ e := Nat.mul_le_mul_right (2 ^ e) ht1
    have hrem : 256 * (256 * m - t * 2 ^ e) ≤ t * 2 ^ e := by omega
    have hud : 0 < t * 2 ^ e := Nat.mul_pos (by omega) hp0
    have hj : t - 256 < 256 := by omega
    have hA := smulInt_mem (Int.ofNat e - Int.ofNat LB) L2I_mem
    have hB := logTab_mem hj
    have hC := logSer_mem nt hud hrem
    refine mem_of_eq (add_mem (add_mem hA hB) hC) ?_
    rw [log_split (e := e) hm (by omega : 0 < t)]
    have e1 : ((Int.ofNat e - Int.ofNat LB : ℤ) : ℝ) = (e : ℝ) - 192 := by
      simp [LB, Int.ofNat_eq_coe]
    have e2 : 1 + ((t - 256 : ℕ) : ℝ) / 256 = (t : ℝ) / 256 := by
      rw [Nat.cast_sub ht1]; push_cast; ring
    have e3 : 1 + ((256 * m - t * 2 ^ e : ℕ) : ℝ) / ((t * 2 ^ e : ℕ) : ℝ) =
        256 * (m : ℝ) / ((t : ℝ) * 2 ^ e) := by
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
      have h2e : (2 : ℝ) ^ e ≠ 0 := by positivity
      rw [Nat.cast_sub htp]
      push_cast
      first
        | (field_simp; ring)
        | field_simp
    rw [e1, e2, e3]
  · exact logFallback_mem hm

/-! ## K-7: `logQ` -/

private theorem logQ_mem_mlo_zero (nt : Nat) {a : QF} {n mhi : Nat}
    (h2 : 0 < a.2) (hn0 : 0 < n)
    (hxv : val a = (n : ℝ) / a.2) (hx : 0 < val a)
    (hmhi0 : 0 < mhi) (hxle : val a ≤ (mhi : ℝ) / SL) :
    IV.mem (Int.ofNat S - Int.ofNat (cdivN (S * a.2) n), (logDy nt mhi).2)
      (Real.log (val a)) := by
  have hS := S_pos
  have hSL := SL_pos
  have hD := logDy_mem nt hmhi0
  rw [mem_iff] at hD ⊢
  simp only [Int.ofNat_eq_coe]
  push_cast
  have hlog : 1 - (a.2 : ℝ) / n ≤ Real.log (val a) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv, hxv, inv_div] at h
    rw [hxv]
    linarith
  have c1 := div_le_cdivN (S * a.2) hn0
  push_cast at c1
  have m1 := mul_le_mul_of_nonneg_right hlog hS.le
  have e1 : (1 - (a.2 : ℝ) / n) * S = S - S * a.2 / n := by ring
  have hmono := Real.log_le_log hx hxle
  have m2 := mul_le_mul_of_nonneg_right hmono hS.le
  constructor <;> linarith [hD.1, hD.2, m1, m2, e1, c1]

private theorem logQ_mem_mlo_pos (nt : Nat) {a : QF} {mlo mhi : Nat}
    (hmlo0 : 0 < mlo) (hmloR : (mlo : ℝ) ≤ val a * SL)
    (hmhiR : val a * SL ≤ (mhi : ℝ)) :
    IV.mem ((logDy nt mlo).1,
      (logDy nt mlo).2 + Int.ofNat (cdivN ((mhi - mlo) * S) mlo))
      (Real.log (val a)) := by
  have hS := S_pos
  have hSL := SL_pos
  have hmloRpos : (0 : ℝ) < mlo := by exact_mod_cast hmlo0
  have hD := logDy_mem nt hmlo0
  have hA : (0 : ℝ) < (mlo : ℝ) / SL := div_pos hmloRpos hSL
  have hAx : (mlo : ℝ) / SL ≤ val a := by rw [div_le_iff₀ hSL]; exact hmloR
  have hle : mlo ≤ mhi := by
    have : (mlo : ℝ) ≤ mhi := hmloR.trans hmhiR
    exact_mod_cast this
  have hlow := Real.log_le_log hA hAx
  have hupp := log_le_add_div hA hAx
  have hq : (val a - (mlo : ℝ) / SL) / ((mlo : ℝ) / SL) ≤
      ((mhi : ℝ) - mlo) / mlo := by
    have e : (val a - (mlo : ℝ) / SL) / ((mlo : ℝ) / SL) =
        (val a * SL - mlo) / mlo := by
      have h0' : (mlo : ℝ) ≠ 0 := hmloRpos.ne'
      have h1' : (SL : ℝ) ≠ 0 := hSL.ne'
      first
        | (field_simp; ring)
        | field_simp
    rw [e]
    exact div_mono hmloRpos (by linarith)
  have c1 := div_le_cdivN ((mhi - mlo) * S) hmlo0
  push_cast [Nat.cast_sub hle] at c1
  rw [mem_iff] at hD ⊢
  simp only [Int.ofNat_eq_coe]
  push_cast
  set Lx := Real.log (val a)
  set LA := Real.log ((mlo : ℝ) / SL)
  set Q := (val a - (mlo : ℝ) / SL) / ((mlo : ℝ) / SL)
  have m1 := mul_le_mul_of_nonneg_right hlow hS.le
  have m2 := mul_le_mul_of_nonneg_right hupp hS.le
  have m3 := mul_le_mul_of_nonneg_right hq hS.le
  have e1 : (LA + Q) * S = LA * S + Q * S := by ring
  have e2 : ((mhi : ℝ) - mlo) / mlo * S =
      ((mhi : ℝ) - mlo) * S / mlo := by ring
  constructor <;> linarith [hD.1, hD.2, m1, m2, m3, e1, e2, c1]

/-- K-7 -/
theorem logQ_mem (nt : Nat) {a : QF} (h1 : 0 < a.1) (h2 : 0 < a.2) :
    IV.mem (logQ nt a) (Real.log (val a)) := by
  unfold logQ
  dsimp only
  have hSL := SL_pos
  have hd : (0 : ℝ) < a.2 := by exact_mod_cast h2
  have hn : ((a.1.natAbs : ℕ) : ℝ) = (a.1 : ℝ) := by
    rw [natAbs_cast, abs_of_pos (by exact_mod_cast h1)]
  have hn0 : 0 < a.1.natAbs := Int.natAbs_pos.mpr h1.ne'
  have hxv0 : val a = ((a.1.natAbs : ℕ) : ℝ) / a.2 := by unfold val; rw [hn]
  set n := a.1.natAbs with hn_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hxv : val a = (n : ℝ) / a.2 := by simpa [n] using hxv0
  have hx : 0 < val a := by rw [hxv]; exact div_pos hnR hd
  have hxS : val a * SL = ((n * SL : ℕ) : ℝ) / a.2 := by rw [hxv]; push_cast; ring
  set mlo := n * SL / a.2 with hmlo_def
  set mhi := cdivN (n * SL) a.2 with hmhi_def
  have hmloR : (mlo : ℝ) ≤ val a * SL := by rw [hxS]; exact natDiv_le _ _
  have hmhiR : val a * SL ≤ (mhi : ℝ) := by rw [hxS]; exact div_le_cdivN _ h2
  have hmhi0 : 0 < mhi := by
    have : (0 : ℝ) < mhi := lt_of_lt_of_le (mul_pos hx hSL) hmhiR
    exact_mod_cast this
  have hxle : val a ≤ (mhi : ℝ) / SL := by rw [le_div_iff₀ hSL]; exact hmhiR
  split_ifs with h0
  · exact logQ_mem_mlo_zero nt h2 (by simpa [n] using hn0) hxv hx hmhi0 hxle
  · exact logQ_mem_mlo_pos nt (Nat.pos_of_ne_zero h0) hmloR hmhiR

/-! ## K-8: `atanLe` -/

/-- K-8 -/
theorem atanLe_mem (nt : Nat) {a b : Nat} (hb : 0 < b) (hab : a ≤ b) :
    IV.mem (atanLe nt a b) (Real.arctan ((a : ℝ) / b)) := by
  unfold atanLe
  dsimp only
  set j := 256 * a / b with hj_def
  have hj : j ≤ 256 := Nat.div_le_of_le_mul (by omega)
  have hjb : j * b ≤ 256 * a := Nat.div_mul_le_self _ _
  have hdm : j * b + (256 * a) % b = 256 * a := by
    rw [Nat.mul_comm j]; exact Nat.div_add_mod (256 * a) b
  have hmod := Nat.mod_lt (256 * a) hb
  have hvd : 0 < 256 * b + j * a := by omega
  have hv : 256 * (256 * a - j * b) ≤ 256 * b + j * a := by omega
  have hT := atanTab_mem hj
  have hR := atanSer_mem nt hvd hv
  refine mem_of_eq (add_mem hT hR) ?_
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hw : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hc : (0 : ℝ) ≤ (j : ℝ) / 256 := by positivity
  rw [arctan_shift hw hc]
  congr 2
  rw [Nat.cast_sub hjb]
  push_cast
  have h1 : (256 * (b : ℝ) + j * a) ≠ 0 := by
    have hja : (0 : ℝ) ≤ (j : ℝ) * a := by positivity
    exact ne_of_gt (by linarith)
  have h2 : (1 + (a : ℝ) / b * ((j : ℝ) / 256)) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  have hb0 : (b : ℝ) ≠ 0 := hbR.ne'
  first
    | (field_simp; ring)
    | field_simp

/-! ## K-9: `atanQ` -/

/-- K-9 -/
theorem atanQ_mem (nt : Nat) {x : QF} (h2 : 0 < x.2) :
    IV.mem (atanQ nt x) (Real.arctan (val x)) := by
  unfold atanQ
  dsimp only
  have hd : (0 : ℝ) < x.2 := by exact_mod_cast h2
  have hr : IV.mem
      (if x.1.natAbs ≤ x.2 then atanLe nt x.1.natAbs x.2
        else IK.sub halfPiI (atanLe nt x.2 x.1.natAbs))
      (Real.arctan ((x.1.natAbs : ℝ) / x.2)) := by
    split_ifs with hle
    · exact atanLe_mem nt h2 hle
    · have hlt : x.2 < x.1.natAbs := lt_of_not_ge hle
      have hapos : 0 < x.1.natAbs := by omega
      have h := sub_mem halfPiI_mem (atanLe_mem nt hapos hlt.le)
      refine mem_of_eq h ?_
      have hpos : (0 : ℝ) < (x.2 : ℝ) / (x.1.natAbs : ℝ) :=
        div_pos hd (by exact_mod_cast hapos)
      have hinv := Real.arctan_inv_of_pos hpos
      rw [inv_div] at hinv
      linarith
  by_cases hneg : x.1 < 0
  · rw [if_pos hneg]
    refine mem_of_eq (neg_mem hr) ?_
    rw [← Real.arctan_neg]
    congr 1
    unfold val
    rw [natAbs_cast, abs_of_neg (by exact_mod_cast hneg)]
    ring
  · rw [if_neg hneg]
    refine mem_of_eq hr ?_
    congr 1
    unfold val
    rw [natAbs_cast, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

/-! ## E-a: the `hsI` and `aI` partial-sum enclosures

The integer evaluator is built from exact rational pairs and the K-5--K-9
transcendental enclosures.  These lemmas expose the corresponding real closed
forms before they are assembled into a shard.  Keeping the real functions
explicit is important: the later measure bridge must identify these closed
forms with the v13 integrals, rather than hiding that identification in the
interval proof.
-/

noncomputable def hsClosed (s : QF) : ℝ :=
  if s.1 = 0 then 0 else val s * Real.log |val s| - val s

noncomputable def aClosed (s Y : QF) : ℝ :=
  if Y.1 = 0 then hsClosed s else
    val (qhalf s) * Real.log (val (qsq s) + val (qsq Y)) - val s +
      val Y * Real.arctan (val s / val Y)

private theorem val_qabs {s : QF} : val (qabs s) = |val s| := by
  change (s.1.natAbs : ℝ) / (s.2 : ℝ) = |(s.1 : ℝ) / s.2|
  rw [natAbs_cast, abs_div]
  have hden : (0 : ℝ) ≤ (s.2 : ℝ) := by positivity
  rw [abs_of_nonneg hden]

private theorem val_qhalf {s : QF} : val (qhalf s) = val s / 2 := by
  unfold qhalf val
  push_cast
  ring

private theorem qsq_val {s : QF} : val (qsq s) = val s * val s := by
  exact val_qmul s s

private theorem qsq_pos_den {s : QF} (hs : 0 < s.2) : 0 < (qsq s).2 := by
  unfold qsq qmul
  exact Nat.mul_pos hs hs

private theorem qadd_sq_pos {s Y : QF} (hs : 0 < s.2) (hY : 0 < Y.2)
    (hYn : Y.1 ≠ 0) : 0 < (qadd (qsq s) (qsq Y)).1 := by
  have hs2 : 0 < (qsq s).2 := qsq_pos_den hs
  have hY2 : 0 < (qsq Y).2 := qsq_pos_den hY
  have hsqY : 0 < val (qsq Y) := by
    rw [qsq_val]
    have hY' : (val Y : ℝ) ≠ 0 := by
      unfold val
      exact div_ne_zero (by exact_mod_cast hYn) (by exact_mod_cast hY.ne')
    exact mul_self_pos.mpr hY'
  have hsum : 0 < val (qadd (qsq s) (qsq Y)) := by
    rw [val_qadd hs2 hY2]
    rw [qsq_val]
    nlinarith [sq_nonneg (val s)]
  have hden : (0 : ℝ) < (qadd (qsq s) (qsq Y)).2 := by
    unfold qadd
    exact_mod_cast (Nat.mul_pos hs2 hY2)
  have hnum : (0 : ℝ) < ((qadd (qsq s) (qsq Y)).1 : ℝ) := by
    have hp := (div_pos_iff.mp (by simpa [val] using hsum))
    rcases hp with hp | hp
    · exact hp.1
    · exact False.elim ((not_lt_of_ge hden.le) hp.2)
  exact_mod_cast hnum

theorem hsI_mem {md : Mode} {s : QF} (hs : 0 < s.2) :
    IV.mem (hsI md s) (hsClosed s) := by
  unfold hsI hsClosed
  split_ifs with hzero
  · exact zero_mem
  · have hsn : s.1 ≠ 0 := hzero
    have hqabs : 0 < (qabs s).1 := by
      unfold qabs
      change (0 : ℤ) < Int.ofNat s.1.natAbs
      have hn : 0 < s.1.natAbs := Int.natAbs_pos.mpr hsn
      rw [Int.ofNat_eq_coe]
      exact_mod_cast hn
    have hqa : 0 < (qabs s).2 := by simpa [qabs] using hs
    have hl := logQ_mem md.ntl hqabs hqa
    have hsq := smulQ_mem hs hl
    have hneg := ofQ_mem (a := qneg s) hs
    have hneg' := mem_of_eq hneg (val_qneg s)
    have hsum := add_mem hsq hneg'
    refine mem_of_eq hsum ?_
    rw [val_qabs]
    ring

theorem aI_mem {md : Mode} {s Y : QF} (hs : 0 < s.2) (hY : 0 < Y.2) :
    IV.mem (aI md s Y) (aClosed s Y) := by
  unfold aI aClosed
  split_ifs with hzero
  · exact hsI_mem hs
  · have hq : 0 < (qadd (qsq s) (qsq Y)).1 := qadd_sq_pos hs hY hzero
    have hs2 : 0 < (qsq s).2 := qsq_pos_den hs
    have hY2 : 0 < (qsq Y).2 := qsq_pos_den hY
    have hqd : 0 < (qadd (qsq s) (qsq Y)).2 := by
      unfold qadd
      exact_mod_cast (Nat.mul_pos hs2 hY2)
    have hlog := logQ_mem md.ntl hq hqd
    have hdiv : 0 < (qdiv s Y).2 := by
      unfold qdiv
      exact Nat.mul_pos hs (Int.natAbs_pos.mpr hzero)
    have hatan := atanQ_mem md.nta hdiv
    have hhalf : 0 < (qhalf s).2 := by
      unfold qhalf
      omega
    have hh := smulQ_mem hhalf hlog
    have hn := ofQ_mem (a := qneg s) hs
    have hn' := mem_of_eq hn (val_qneg s)
    have ha := add_mem (add_mem hh hn') (smulQ_mem hY hatan)
    refine mem_of_eq ha ?_
    rw [val_qhalf, val_qadd hs2 hY2,
      qsq_val, val_qdiv hs hY hzero]
    ring

theorem hsI_sum_mem {md : Mode} {xs : List QF}
    (h : ∀ s ∈ xs, 0 < s.2) :
    IV.mem (sumI (xs.map (hsI md)))
      (xs.map hsClosed).sum := by
  apply sumI_map_mem
  intro s hs'
  exact hsI_mem (h s hs')

theorem aI_sum_mem {md : Mode} {xs ys : List QF}
    (h : xs.length = ys.length)
    (hs : ∀ s ∈ xs, 0 < s.2) (hy : ∀ y ∈ ys, 0 < y.2) :
    IV.mem (sumI (List.zipWith (aI md) xs ys))
      (List.zipWith aClosed xs ys).sum := by
  apply sumI_mem
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hxy : IV.mem (aI md x y) (aClosed x y) :=
            aI_mem (hs x (by simp)) (hy y (by simp))
          have hrest := ih (ys := ys) (by simp at h; omega)
            (fun s hs' => hs s (by simp [hs']))
            (fun z hz' => hy z (by simp [hz']))
          exact List.Forall₂.cons hxy hrest

end Li2Lean.V.EnergyCertI.IK
