/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ISoundArith
import Li2Lean.V.EnergyCertI.IAtanTab

/-!
# Integer kit soundness, part 2: the two tables and `log 2`, `π/2` (K-4)

Generated the release date (release source, elaborated).  Verification notes are retained for context.

Route: row theorem (kernel `decide`) ⟹ `ivContains` for one entry ⟹ (K-2
`qle_spec`) the entry contains the exact rational bounds ⟹ (K-2/K-3 and the
closed-form identities below) those bounds are P0 `lpoly ∓ lrem` resp.
`atTab k + (spr ∓ srem)` ⟹ P0 `log_lower/log_upper`, `atan_lower/atan_upper`,
`atTab_mem`, `arctan_shift`.

The `let`-bodies of `logTabBounds` / `atanTabBounds` are given names below and
re-identified by `rfl` (`logTabBounds_eq`, `atanTabBounds_eq`), so no proof
step depends on how `let`s are zeta-reduced.
-/

namespace Li2Lean.V.EnergyCertI.IK

open Li2Lean.P0.CA.Contour Li2Lean.P0.ConfigLogTaylor

/-! ## From `ivContains` to membership -/

theorem ivContains_mem {I : IV} {b : QF × QF} {x : ℝ} (h1 : 0 < b.1.2) (h2 : 0 < b.2.2)
    (hlo : val b.1 ≤ x) (hhi : x ≤ val b.2) (h : ivContains I b = true) : IV.mem I x := by
  unfold ivContains at h
  rw [Bool.and_eq_true] at h
  have a := (qle_spec (a := (I.1, S)) (b := b.1) S_pos_nat h1).mp h.1
  have c := (qle_spec (a := b.2) (b := (I.2, S)) h2 S_pos_nat).mp h.2
  unfold IV.mem
  exact ⟨a.trans hlo, hhi.trans c⟩

/-! ## Row theorems ⟹ entries -/

theorem logTab_rows : ∀ r < 16, logTabRowOK r = true := by
  intro r hr
  interval_cases r
  exacts [logTab_row00, logTab_row01, logTab_row02, logTab_row03, logTab_row04,
    logTab_row05, logTab_row06, logTab_row07, logTab_row08, logTab_row09, logTab_row10,
    logTab_row11, logTab_row12, logTab_row13, logTab_row14, logTab_row15]

theorem logTab_entry {j : Nat} (hj : j < 256) :
    ivContains (tabGet logTab j) (logTabBounds j) = true := by
  have hrow := logTab_rows (j / 16) (by omega)
  unfold logTabRowOK at hrow
  rw [List.all_eq_true] at hrow
  have h := hrow (j % 16) (List.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have e : 16 * (j / 16) + j % 16 = j := Nat.div_add_mod j 16
  simp only [e] at h
  exact h

theorem atanTab_rows : ∀ r ≤ 16, atanTabRowOK r = true := by
  intro r hr
  interval_cases r
  exacts [atanTab_row00, atanTab_row01, atanTab_row02, atanTab_row03, atanTab_row04,
    atanTab_row05, atanTab_row06, atanTab_row07, atanTab_row08, atanTab_row09,
    atanTab_row10, atanTab_row11, atanTab_row12, atanTab_row13, atanTab_row14,
    atanTab_row15, atanTab_row16]

theorem atanTab_entry {j : Nat} (hj : j ≤ 256) :
    ivContains (tabGet atanTab j) (atanTabBounds j) = true := by
  have hrow := atanTab_rows (j / 16) (by omega)
  unfold atanTabRowOK at hrow
  rw [List.all_eq_true] at hrow
  have hc : j % 16 ∈ List.range (if j / 16 = 16 then 1 else 16) := by
    rw [List.mem_range]
    split_ifs with h16
    · omega
    · exact Nat.mod_lt _ (by norm_num)
  have h := hrow (j % 16) hc
  have e : 16 * (j / 16) + j % 16 = j := Nat.div_add_mod j 16
  simp only [e] at h
  exact h

/-! ## The log table -/

def tabH (j : ℕ) : Int × Nat := hornerQ (Int.ofNat (j * j)) ((512 + j) * (512 + j)) 0 NLT
def lpQ (j : ℕ) : QF := (2 * Int.ofNat j * (tabH j).1, (512 + j) * (tabH j).2)
def lrQ (j : ℕ) : QF :=
  (Int.ofNat (2 * j ^ (2 * NLT + 1)), (512 + j) ^ (2 * NLT - 1) * ((512 + j) * (512 + j) - j * j))

theorem logTabBounds_eq (j : ℕ) :
    logTabBounds j = (qsub (lpQ j) (lrQ j), qadd (lpQ j) (lrQ j)) := rfl

theorem tabH_den_pos (j : ℕ) : 0 < (tabH j).2 :=
  hornerQ_den_pos _ (Nat.mul_pos (by omega) (by omega)) 0 NLT

theorem lpQ_den_pos (j : ℕ) : 0 < (lpQ j).2 := Nat.mul_pos (by omega) (tabH_den_pos j)

theorem lrQ_den_pos (j : ℕ) : 0 < (lrQ j).2 := by
  have hlt : j * j < (512 + j) * (512 + j) := Nat.mul_self_lt_mul_self (by omega)
  exact Nat.mul_pos (pow_pos (by omega) _) (by omega)

theorem logCoord_tab (j : ℕ) :
    logCoordinate ((256 + (j : ℚ)) / 256) = (j : ℚ) / (512 + j) := by
  unfold logCoordinate
  have h1 : ((256 + (j : ℚ)) / 256 + 1) ≠ 0 := by positivity
  have h2 : (512 + (j : ℚ)) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

theorem logCoord_tab_sq (j : ℕ) :
    logCoordinate ((256 + (j : ℚ)) / 256) ^ 2 =
      ((Int.ofNat (j * j) : ℤ) : ℚ) / (((512 + j) * (512 + j) : ℕ) : ℚ) := by
  rw [logCoord_tab]
  simp only [Int.ofNat_eq_coe]
  push_cast
  field_simp

theorem lpQ_val (j : ℕ) : val (lpQ j) = ((lpoly ((256 + (j : ℚ)) / 256) NLT : ℚ) : ℝ) := by
  have hzd : 0 < (512 + j) * (512 + j) := Nat.mul_pos (by omega) (by omega)
  have hHv := hornerQ_val (Int.ofNat (j * j)) hzd 0 NLT
  have hl : lpoly ((256 + (j : ℚ)) / 256) NLT =
      2 * ((j : ℚ) / (512 + j) * (((tabH j).1 : ℚ) / ((tabH j).2 : ℚ))) := by
    rw [← lpolyF_eq]
    unfold lpolyF
    rw [logCoord_tab_sq, ← hHv, logCoord_tab]
    rfl
  rw [hl]
  have hH2' : ((tabH j).2 : ℝ) ≠ 0 := by exact_mod_cast (tabH_den_pos j).ne'
  have h5 : (512 + (j : ℝ)) ≠ 0 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  unfold val lpQ
  simp only [Int.ofNat_eq_coe]
  push_cast
  field_simp [hH2', h5]

theorem lr_identity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a < b) :
    2 * (|a / b| ^ (2 * NLT + 1) / (1 - (a / b) ^ 2)) =
      2 * a ^ (2 * NLT + 1) / (b ^ (2 * NLT - 1) * (b ^ 2 - a ^ 2)) := by
  rw [abs_of_nonneg (div_nonneg ha hb.le)]
  have hb0 : b ≠ 0 := hb.ne'
  have hd : b ^ 2 - a ^ 2 ≠ 0 := (by nlinarith : 0 < b ^ 2 - a ^ 2).ne'
  -- `NLT = 24` by `rfl`, so the exponents are the literals 49 and 47
  show 2 * ((a / b) ^ 49 / (1 - (a / b) ^ 2)) = 2 * a ^ 49 / (b ^ 47 * (b ^ 2 - a ^ 2))
  rw [div_pow, div_pow]
  first
    | (field_simp; ring)
    | field_simp

theorem lrQ_val (j : ℕ) : val (lrQ j) = ((lrem ((256 + (j : ℚ)) / 256) NLT : ℚ) : ℝ) := by
  have hle : j * j ≤ (512 + j) * (512 + j) := Nat.mul_le_mul (by omega) (by omega)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hb : (0 : ℝ) < 512 + j := by positivity
  have hab : (j : ℝ) < 512 + j := by linarith
  unfold lrem
  rw [logCoord_tab]
  push_cast
  rw [lr_identity hj0 hb hab]
  unfold val lrQ
  simp only [Int.ofNat_eq_coe]
  push_cast [Nat.cast_sub hle]
  ring

/-- K-4 -/
theorem logTab_mem {j : Nat} (hj : j < 256) :
    IV.mem (tabGet logTab j) (Real.log (1 + (j : ℝ) / 256)) := by
  have hq : (0 : ℚ) < (256 + (j : ℚ)) / 256 := by positivity
  have hlo := log_lower hq NLT
  have hhi := log_upper hq NLT
  have hqR : (((256 + (j : ℚ)) / 256 : ℚ) : ℝ) = 1 + (j : ℝ) / 256 := by push_cast; ring
  rw [hqR] at hlo hhi
  have hb := logTab_entry hj
  rw [logTabBounds_eq] at hb
  refine ivContains_mem (b := (qsub (lpQ j) (lrQ j), qadd (lpQ j) (lrQ j)))
    (qsub_den_pos (lpQ_den_pos j) (lrQ_den_pos j))
    (qadd_den_pos (lpQ_den_pos j) (lrQ_den_pos j)) ?_ ?_ hb
  · show val (qsub (lpQ j) (lrQ j)) ≤ _
    rw [val_qsub (lpQ_den_pos j) (lrQ_den_pos j), lpQ_val, lrQ_val]
    exact_mod_cast hlo
  · show _ ≤ val (qadd (lpQ j) (lrQ j))
    rw [val_qadd (lpQ_den_pos j) (lrQ_den_pos j), lpQ_val, lrQ_val]
    exact_mod_cast hhi

/-! ## The arctan table -/

def atK (j : ℕ) : ℕ := min 3 ((j + 32) / 64)
def atVn (j : ℕ) : ℤ := 4 * Int.ofNat j - 256 * Int.ofNat (atK j)
def atVd (j : ℕ) : ℕ := 1024 + j * atK j
def atH (j : ℕ) : Int × Nat := hornerQ (-(atVn j * atVn j)) (atVd j * atVd j) 0 NATN
def atSpr (j : ℕ) : QF := (atVn j * (atH j).1, atVd j * (atH j).2)
def atSrem (j : ℕ) : QF :=
  (Int.ofNat ((atVn j).natAbs ^ (2 * NATN + 1)), (2 * NATN + 1) * atVd j ^ (2 * NATN + 1))
def atLo (j : ℕ) : QF := ((atNum (atK j)).1, 1000000000000000000000)
def atHi (j : ℕ) : QF := ((atNum (atK j)).2, 1000000000000000000000)

theorem atanTabBounds_eq (j : ℕ) :
    atanTabBounds j = (qsub (qadd (atLo j) (atSpr j)) (atSrem j),
      qadd (qadd (atHi j) (atSpr j)) (atSrem j)) := rfl

theorem atVd_pos (j : ℕ) : 0 < atVd j := by unfold atVd; omega
theorem atH_den_pos (j : ℕ) : 0 < (atH j).2 :=
  hornerQ_den_pos _ (Nat.mul_pos (atVd_pos j) (atVd_pos j)) 0 NATN
theorem atSpr_den_pos (j : ℕ) : 0 < (atSpr j).2 := Nat.mul_pos (atVd_pos j) (atH_den_pos j)
theorem atSrem_den_pos (j : ℕ) : 0 < (atSrem j).2 :=
  Nat.mul_pos (by omega) (pow_pos (atVd_pos j) _)
theorem atLo_den_pos (j : ℕ) : 0 < (atLo j).2 := by unfold atLo; norm_num
theorem atHi_den_pos (j : ℕ) : 0 < (atHi j).2 := by unfold atHi; norm_num

/-- The table's series argument `v = vn / vd`, as a rational. -/
def atV (j : ℕ) : ℚ := ((atVn j : ℤ) : ℚ) / ((atVd j : ℕ) : ℚ)

theorem atSpr_val (j : ℕ) : val (atSpr j) = ((spr (atV j) NATN : ℚ) : ℝ) := by
  have hzd : 0 < atVd j * atVd j := Nat.mul_pos (atVd_pos j) (atVd_pos j)
  have hHv := hornerQ_val (-(atVn j * atVn j)) hzd 0 NATN
  have hvd : ((atVd j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (atVd_pos j).ne'
  have hs : spr (atV j) NATN =
      ((atVn j : ℤ) : ℚ) / (atVd j : ℚ) * (((atH j).1 : ℚ) / ((atH j).2 : ℚ)) := by
    rw [spr_hsum]
    unfold atV
    have e : -((((atVn j : ℤ) : ℚ) / (atVd j : ℚ)) ^ 2) =
        ((-(atVn j * atVn j) : ℤ) : ℚ) / ((atVd j * atVd j : ℕ) : ℚ) := by
      push_cast; ring
    rw [e, ← hHv]
    rfl
  rw [hs]
  have hH2 : ((atH j).2 : ℝ) ≠ 0 := by exact_mod_cast (atH_den_pos j).ne'
  have hvdR : ((atVd j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (atVd_pos j).ne'
  unfold val atSpr
  push_cast
  first
    | (field_simp; ring)
    | field_simp

theorem atSrem_val (j : ℕ) : val (atSrem j) = ((srem (atV j) NATN : ℚ) : ℝ) := by
  have hvdR : (0 : ℝ) < ((atVd j : ℕ) : ℝ) := by exact_mod_cast atVd_pos j
  have hden : (2 * (NATN : ℝ) + 1) ≠ 0 := by positivity
  unfold srem atV val atSrem
  simp only [Int.ofNat_eq_coe]
  rw [Int.cast_natCast, Nat.cast_pow, natAbs_cast]
  push_cast
  rw [abs_div, abs_of_pos hvdR, div_pow]
  first
    | (field_simp; ring)
    | field_simp

theorem atV_real (j : ℕ) :
    ((atV j : ℚ) : ℝ) = (4 * (j : ℝ) - 256 * (atK j : ℝ)) / (1024 + (j : ℝ) * (atK j : ℝ)) := by
  unfold atV atVn atVd
  simp only [Int.ofNat_eq_coe]
  first
    | (push_cast; ring)
    | push_cast

theorem atTab_three : atTab 3 =
    ⟨643501108793284386802 / 10 ^ 21, 643501108793284386803 / 10 ^ 21⟩ := rfl
theorem atNum_three : atNum 3 = (643501108793284386802, 643501108793284386803) := rfl

/-- `atNum k / 10^21` is P0 `atTab k` (the literals are copied). -/
theorem atNum_mem (k : ℕ) (hk : k ≤ 3) :
    ((atNum k).1 : ℝ) / 1000000000000000000000 ≤ Real.arctan ((k : ℝ) / 4) ∧
      Real.arctan ((k : ℝ) / 4) ≤ ((atNum k).2 : ℝ) / 1000000000000000000000 := by
  have h := atTab_mem k hk
  have e : ((((k : ℚ) / 4 : ℚ)) : ℝ) = (k : ℝ) / 4 := by
    push_cast
    ring
  rw [e] at h
  interval_cases k
  · simp [atTab, atNum, QI.mem, QI.pt] at h ⊢
  all_goals
    simp only [atTab_three, atNum_three, atTab, atNum, QI.mem] at h ⊢   -- [Verified]
    push_cast at h ⊢
    constructor <;> linarith [h.1, h.2]

theorem atanTab_shift (j k : ℕ) :
    Real.arctan ((j : ℝ) / 256) = Real.arctan ((k : ℝ) / 4) +
      Real.arctan ((4 * (j : ℝ) - 256 * k) / (1024 + (j : ℝ) * k)) := by
  have hw : (0 : ℝ) ≤ (j : ℝ) / 256 := by positivity
  have hc : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  rw [arctan_shift hw hc]
  congr 2
  have h1 : (1 + (j : ℝ) / 256 * ((k : ℝ) / 4)) ≠ 0 := by positivity
  have h2 : (1024 + (j : ℝ) * k) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

/-- K-4 -/
theorem atanTab_mem {j : Nat} (hj : j ≤ 256) :
    IV.mem (tabGet atanTab j) (Real.arctan ((j : ℝ) / 256)) := by
  have hk3 : atK j ≤ 3 := min_le_left _ _
  have hA := atNum_mem (atK j) hk3
  have hlo := atan_lower (atV j) NATN
  have hhi := atan_upper (atV j) NATN
  rw [atV_real] at hlo hhi
  have hsh := atanTab_shift j (atK j)
  have hb := atanTab_entry hj
  rw [atanTabBounds_eq] at hb
  have hd1 := qsub_den_pos (qadd_den_pos (atLo_den_pos j) (atSpr_den_pos j)) (atSrem_den_pos j)
  have hd2 := qadd_den_pos (qadd_den_pos (atHi_den_pos j) (atSpr_den_pos j)) (atSrem_den_pos j)
  refine ivContains_mem (b := (qsub (qadd (atLo j) (atSpr j)) (atSrem j),
      qadd (qadd (atHi j) (atSpr j)) (atSrem j))) hd1 hd2 ?_ ?_ hb
  · show val (qsub (qadd (atLo j) (atSpr j)) (atSrem j)) ≤ _
    rw [val_qsub (qadd_den_pos (atLo_den_pos j) (atSpr_den_pos j)) (atSrem_den_pos j),
      val_qadd (atLo_den_pos j) (atSpr_den_pos j), atSpr_val, atSrem_val, hsh]
    have hL : val (atLo j) = ((atNum (atK j)).1 : ℝ) / 1000000000000000000000 := by
      unfold val atLo; norm_num
    rw [hL]
    push_cast at hlo
    linarith [hA.1]
  · show _ ≤ val (qadd (qadd (atHi j) (atSpr j)) (atSrem j))
    rw [val_qadd (qadd_den_pos (atHi_den_pos j) (atSpr_den_pos j)) (atSrem_den_pos j),
      val_qadd (atHi_den_pos j) (atSpr_den_pos j), atSpr_val, atSrem_val, hsh]
    have hH : val (atHi j) = ((atNum (atK j)).2 : ℝ) / 1000000000000000000000 := by
      unfold val atHi; norm_num
    rw [hH]
    push_cast at hhi
    linarith [hA.2]

/-! ## `log 2` and `π/2` -/

/-- K-4 -/
theorem L2I_mem : IV.mem L2I (Real.log 2) := by
  have h := l2I_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_coe] at h
  have hL := L2_mem
  unfold QI.mem L2 at hL
  push_cast at hL
  have hS := S_pos
  have h1 : ((L2I.1 : ℤ) : ℝ) * 1000000000000000000000 ≤ 693147180559945309417 * (S : ℝ) := by
    exact_mod_cast h.1
  have h2 : 693147180559945309418 * (S : ℝ) ≤ ((L2I.2 : ℤ) : ℝ) * 1000000000000000000000 := by
    exact_mod_cast h.2
  have m1 := mul_le_mul_of_nonneg_right hL.1 hS.le
  have m2 := mul_le_mul_of_nonneg_right hL.2 hS.le
  rw [mem_iff]
  constructor <;> linarith [m1, m2, h1, h2]

/-- K-4 -/
theorem halfPiI_mem : IV.mem halfPiI (Real.pi / 2) := by
  have h := halfPiI_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_coe] at h
  have hP := PI_mem
  unfold QI.mem PI at hP
  push_cast at hP
  have hS := S_pos
  have h1 : ((halfPiI.1 : ℤ) : ℝ) * 200000000000000000000 ≤ 314159265358979323846 * (S : ℝ) := by
    exact_mod_cast h.1
  have h2 : 314159265358979323847 * (S : ℝ) ≤ ((halfPiI.2 : ℤ) : ℝ) * 200000000000000000000 := by
    exact_mod_cast h.2
  have m1 := mul_le_mul_of_nonneg_right hP.1 hS.le
  have m2 := mul_le_mul_of_nonneg_right hP.2 hS.le
  rw [mem_iff]
  constructor <;> linarith [m1, m2, h1, h2]

end Li2Lean.V.EnergyCertI.IK
