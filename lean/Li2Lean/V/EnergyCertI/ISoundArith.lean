/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.IKit

/-!
# Integer kit soundness, part 1: rounding, exact pairs, Horner (K-1, K-2, K-3)

Generated the release date (release source, elaborated: compiled in the release build).
Verification notes are retained for context.

Everything here is pure arithmetic.  The single bridge to the kernel-side
evaluator is the characterisation `mem_iff`:
`IV.mem I x ↔ I.1 ≤ x·2^64 ≤ I.2` (as reals).
-/

namespace Li2Lean.V.EnergyCertI.IK

/-! ## Casts and scale -/

theorem S_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]

theorem S_pos_nat : (0 : ℕ) < S := by norm_num [S]

theorem ofNat_real (n : ℕ) : ((Int.ofNat n : ℤ) : ℝ) = (n : ℝ) := by
  rw [Int.ofNat_eq_coe, Int.cast_natCast]

theorem natAbs_cast (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem mem_iff {I : IV} {x : ℝ} :
    IV.mem I x ↔ (I.1 : ℝ) ≤ x * S ∧ x * S ≤ (I.2 : ℝ) := by
  unfold IV.mem
  rw [div_le_iff₀ S_pos, le_div_iff₀ S_pos]

theorem mem_of_eq {I : IV} {x y : ℝ} (h : IV.mem I x) (e : x = y) : IV.mem I y := e ▸ h

theorem div_mono {a b d : ℝ} (hd : 0 < d) (h : a ≤ b) : a / d ≤ b / d := by
  rw [div_le_div_iff₀ hd hd]
  exact mul_le_mul_of_nonneg_right h hd.le

/-! ## Floor / ceiling of `n / d` -/

theorem fl_mul_le (n : ℤ) {d : ℕ} (hd : 0 < d) : ((fl n d : ℤ) : ℝ) * d ≤ (n : ℝ) := by
  unfold fl
  rw [Int.ofNat_eq_coe]
  have hd' : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  have h := Int.ediv_mul_le n hd'
  exact_mod_cast h

theorem fl_le_div (n : ℤ) {d : ℕ} (hd : 0 < d) : ((fl n d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact fl_mul_le n hd

theorem cl_eq (n : ℤ) (d : ℕ) : cl n d = -(fl (-n) d) := rfl

theorem div_le_cl (n : ℤ) {d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ ((cl n d : ℤ) : ℝ) := by
  have h := fl_mul_le (-n) hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [cl_eq, div_le_iff₀ hd']
  push_cast at h ⊢
  rw [neg_mul]
  linarith

/-! Natural-number floor and ceiling (`Nat.div`, `cdivN`) -/

theorem cdivN_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ b * cdivN a b := by
  unfold cdivN
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  -- omega treats `b * ((a + b - 1) / b)` and the `%` term as atoms  [Verified]
  omega

theorem div_le_cdivN (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdivN a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h : (a : ℝ) ≤ (b : ℝ) * (cdivN a b : ℝ) := by exact_mod_cast cdivN_ge a hb
  calc (a : ℝ) ≤ (b : ℝ) * (cdivN a b : ℝ) := h
    _ = (cdivN a b : ℝ) * b := mul_comm _ _

theorem natDiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- A rounded non-negative term `[⌊num/den⌋, ⌈num/den⌉]` encloses any `t` with
`t·2^64 = num/den`. -/
theorem natTerm_mem {num den : ℕ} (hd : 0 < den) {t : ℝ}
    (ht : t * S = (num : ℝ) / den) :
    IV.mem ((Int.ofNat (num / den), Int.ofNat (cdivN num den)) : IV) t := by
  rw [mem_iff]
  simp only [ofNat_real]
  rw [ht]
  exact ⟨natDiv_le num den, div_le_cdivN num hd⟩

/-! ## K-1: interval operations -/

theorem zero_mem : IV.mem zero 0 := by
  rw [mem_iff]; simp [zero]

/-- K-1 -/
theorem ofQ_mem {a : QF} (h : 0 < a.2) : IV.mem (ofQ a) (val a) := by
  rw [mem_iff]
  have e : val a * (S : ℝ) = ((a.1 * Int.ofNat S : ℤ) : ℝ) / (a.2 : ℝ) := by
    unfold val
    rw [Int.cast_mul, ofNat_real]
    ring
  rw [e]
  exact ⟨fl_le_div _ h, div_le_cl _ h⟩

/-- K-1 -/
theorem add_mem {I J : IV} {x y : ℝ} (hx : IV.mem I x) (hy : IV.mem J y) :
    IV.mem (IK.add I J) (x + y) := by
  rw [mem_iff] at hx hy ⊢
  have e : (x + y) * (S : ℝ) = x * S + y * S := by ring
  rw [e]
  unfold IK.add
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- K-1 -/
theorem neg_mem {I : IV} {x : ℝ} (hx : IV.mem I x) : IV.mem (IK.neg I) (-x) := by
  rw [mem_iff] at hx ⊢
  have e : (-x) * (S : ℝ) = -(x * S) := by ring
  rw [e]
  unfold IK.neg
  push_cast
  constructor <;> linarith [hx.1, hx.2]

/-- K-1 -/
theorem sub_mem {I J : IV} {x y : ℝ} (hx : IV.mem I x) (hy : IV.mem J y) :
    IV.mem (IK.sub I J) (x - y) := by
  rw [mem_iff] at hx hy ⊢
  have e : (x - y) * (S : ℝ) = x * S - y * S := by ring
  rw [e]
  unfold IK.sub
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- K-1 -/
theorem smulInt_mem (k : Int) {I : IV} {x : ℝ} (hx : IV.mem I x) :
    IV.mem (smulInt k I) ((k : ℝ) * x) := by
  rw [mem_iff] at hx ⊢
  have e : (k : ℝ) * x * S = (k : ℝ) * (x * S) := by ring
  rw [e]
  unfold smulInt
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hk', mul_le_mul_of_nonneg_left hx.2 hk'⟩
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hk', mul_le_mul_of_nonpos_left hx.1 hk'⟩

/-- K-1 -/
theorem smulQ_mem {c : QF} (hc : 0 < c.2) {I : IV} {x : ℝ} (hx : IV.mem I x) :
    IV.mem (smulQ c I) (val c * x) := by
  rw [mem_iff] at hx ⊢
  have hd : (0 : ℝ) < c.2 := by exact_mod_cast hc
  have e : val c * x * S = (c.1 : ℝ) * (x * S) / c.2 := by unfold val; ring
  rw [e]
  unfold smulQ
  split_ifs with h0
  · have h0' : (0 : ℝ) ≤ c.1 := by exact_mod_cast h0
    constructor
    · refine le_trans (fl_le_div _ hc) ?_
      push_cast
      exact div_mono hd (mul_le_mul_of_nonneg_left hx.1 h0')
    · refine le_trans ?_ (div_le_cl _ hc)
      push_cast
      exact div_mono hd (mul_le_mul_of_nonneg_left hx.2 h0')
  · have h0' : (c.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge h0))
    constructor
    · refine le_trans (fl_le_div _ hc) ?_
      push_cast
      exact div_mono hd (mul_le_mul_of_nonpos_left hx.2 h0')
    · refine le_trans ?_ (div_le_cl _ hc)
      push_cast
      exact div_mono hd (mul_le_mul_of_nonpos_left hx.1 h0')

private theorem lin_bounds' {k p q t : ℝ} (hp : p ≤ t) (hq : t ≤ q) :
    min (k * p) (k * q) ≤ k * t ∧ k * t ≤ max (k * p) (k * q) := by
  rcases le_total 0 k with hk | hk
  · constructor
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp hk)
    · exact (mul_le_mul_of_nonneg_left hq hk).trans (le_max_right _ _)
  · constructor
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hq hk)
    · exact (mul_le_mul_of_nonpos_left hp hk).trans (le_max_left _ _)

/-- Real four-corner product bound (the proof of P0 `QI.mem_mul`, on reals). -/
theorem minmax_mul {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hy := lin_bounds' (k := x) hy1 hy2
  have hxc := lin_bounds' (k := c) hx1 hx2
  have hxd := lin_bounds' (k := d) hx1 hx2
  have hca : c * a = a * c := mul_comm c a
  have hcb : c * b = b * c := mul_comm c b
  have hda : d * a = a * d := mul_comm d a
  have hdb : d * b = b * d := mul_comm d b
  have hxc' : x * c = c * x := mul_comm x c
  have hxd' : x * d = d * x := mul_comm x d
  constructor
  · have e1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * c := by
      rw [hxc']
      refine le_trans (le_min ?_ ?_) hxc.1
      · rw [hca]; exact (min_le_left _ _).trans (min_le_left _ _)
      · rw [hcb]; exact (min_le_right _ _).trans (min_le_left _ _)
    have e2 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * d := by
      rw [hxd']
      refine le_trans (le_min ?_ ?_) hxd.1
      · rw [hda]; exact (min_le_left _ _).trans (min_le_right _ _)
      · rw [hdb]; exact (min_le_right _ _).trans (min_le_right _ _)
    exact le_trans (le_min e1 e2) hy.1
  · have e1 : x * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
      rw [hxc']
      refine le_trans hxc.2 (max_le ?_ ?_)
      · rw [hca]; exact (le_max_left _ _).trans (le_max_left _ _)
      · rw [hcb]; exact (le_max_left _ _).trans (le_max_right _ _)
    have e2 : x * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
      rw [hxd']
      refine le_trans hxd.2 (max_le ?_ ?_)
      · rw [hda]; exact (le_max_right _ _).trans (le_max_left _ _)
      · rw [hdb]; exact (le_max_right _ _).trans (le_max_right _ _)
    exact le_trans hy.2 (max_le e1 e2)

/-- K-1 -/
theorem mulI_mem {I J : IV} {x y : ℝ} (hx : IV.mem I x) (hy : IV.mem J y) :
    IV.mem (mulI I J) (x * y) := by
  rw [mem_iff] at hx hy ⊢
  have hS := S_pos
  have hm := minmax_mul hx.1 hx.2 hy.1 hy.2
  have e : x * y * (S : ℝ) = (x * S) * (y * S) / S := by
    rw [eq_div_iff hS.ne']; ring
  rw [e]
  unfold mulI
  constructor
  · refine le_trans (fl_le_div _ S_pos_nat) ?_
    push_cast
    exact div_mono hS hm.1
  · refine le_trans ?_ (div_le_cl _ S_pos_nat)
    push_cast
    exact div_mono hS hm.2

theorem foldl_add_mem {l : List IV} {xs : List ℝ} (h : List.Forall₂ IV.mem l xs) :
    ∀ {acc : IV} {a : ℝ}, IV.mem acc a → IV.mem (l.foldl IK.add acc) (a + xs.sum) := by
  induction h with
  | nil => intro acc a ha; simpa using ha
  | cons hxy _ ih =>
      intro acc a ha
      rw [List.foldl_cons, List.sum_cons, ← add_assoc]
      exact ih (add_mem ha hxy)

/-- K-1 -/
theorem sumI_mem {l : List IV} {xs : List ℝ} (h : List.Forall₂ IV.mem l xs) :
    IV.mem (sumI l) xs.sum := by
  have h' := foldl_add_mem h zero_mem
  rw [zero_add] at h'
  exact h'

/-- K-1, the form every evaluator uses: `sumI (l.map f)`. -/
theorem sumI_map_mem {α : Type*} {l : List α} {f : α → IV} {g : α → ℝ}
    (h : ∀ i ∈ l, IV.mem (f i) (g i)) : IV.mem (sumI (l.map f)) (l.map g).sum := by
  apply sumI_mem
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
      rw [List.map_cons, List.map_cons]
      exact List.Forall₂.cons (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- K-1 -/
theorem hiLt_spec {I : IV} {K : QF} {x : ℝ} (hK : 0 < K.2) (hx : IV.mem I x)
    (h : hiLt I K = true) : x < val K := by
  rw [mem_iff] at hx
  unfold hiLt at h
  have h' := of_decide_eq_true h
  have hK' : (0 : ℝ) < K.2 := by exact_mod_cast hK
  have hS := S_pos
  have hc : (I.2 : ℝ) * K.2 < (K.1 : ℝ) * S := by
    simp only [Int.ofNat_eq_coe] at h'
    exact_mod_cast h'
  unfold val
  rw [lt_div_iff₀ hK']
  have h1 : x * S * K.2 ≤ (I.2 : ℝ) * K.2 := mul_le_mul_of_nonneg_right hx.2 hK'.le
  have e : x * (K.2 : ℝ) * S = x * S * K.2 := by ring
  exact lt_of_mul_lt_mul_right (by rw [e]; linarith) hS.le

/-- `hiLe` analogue (used by the endpoint checks). -/
theorem hiLe_spec {I : IV} {K : QF} {x : ℝ} (hK : 0 < K.2) (hx : IV.mem I x)
    (h : hiLe I K = true) : x ≤ val K := by
  rw [mem_iff] at hx
  unfold hiLe at h
  have h' := of_decide_eq_true h
  have hK' : (0 : ℝ) < K.2 := by exact_mod_cast hK
  have hS := S_pos
  have hc : (I.2 : ℝ) * K.2 ≤ (K.1 : ℝ) * S := by
    simp only [Int.ofNat_eq_coe] at h'
    exact_mod_cast h'
  unfold val
  rw [le_div_iff₀ hK']
  have h1 : x * S * K.2 ≤ (I.2 : ℝ) * K.2 := mul_le_mul_of_nonneg_right hx.2 hK'.le
  have e : x * (K.2 : ℝ) * S = x * S * K.2 := by ring
  exact le_of_mul_le_mul_right (by rw [e]; linarith) hS

/-! ## K-2: unnormalised exact pairs -/

/-- K-2 -/
theorem val_qadd {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    val (qadd a b) = val a + val b := by
  have ha' : (a.2 : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b.2 : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold val qadd
  simp only [Int.ofNat_eq_coe]
  push_cast
  rw [div_add_div _ _ ha' hb']
  ring

theorem val_qneg (a : QF) : val (qneg a) = -val a := by
  unfold val qneg; push_cast; ring

theorem val_qsub {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    val (qsub a b) = val a - val b := by
  unfold qsub
  calc
    val (qadd a (qneg b)) = val a + val (qneg b) :=
      val_qadd (a := a) (b := qneg b) ha (by simpa [qneg] using hb)
    _ = val a - val b := by rw [val_qneg]; ring

/-- K-2 -/
theorem val_qmul (a b : QF) : val (qmul a b) = val a * val b := by
  unfold val qmul
  push_cast
  exact mul_div_mul_comm _ _ _ _

/-- K-2.  STATEMENT CHANGE vs the v2 source: positive denominators added
(every caller has them; the Generated signature had only `b.1 ≠ 0`). -/
theorem val_qdiv {a b : QF} (ha : 0 < a.2) (hb2 : 0 < b.2) (hb : b.1 ≠ 0) :
    val (qdiv a b) = val a / val b := by
  have ha' : (a.2 : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb2' : (b.2 : ℝ) ≠ 0 := by exact_mod_cast hb2.ne'
  have hb' : (b.1 : ℝ) ≠ 0 := by exact_mod_cast hb
  unfold val qdiv
  simp only [Int.ofNat_eq_coe]
  split_ifs with hneg
  · have hn : (b.1 : ℝ) < 0 := by exact_mod_cast hneg
    rw [Nat.cast_mul, natAbs_cast, abs_of_neg hn]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  · have hn : (0 : ℝ) ≤ b.1 := by exact_mod_cast (not_lt.mp hneg)
    rw [Nat.cast_mul, natAbs_cast, abs_of_nonneg hn]
    push_cast
    first
      | (field_simp; ring)
      | field_simp

/-- K-2 -/
theorem qle_spec {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    qle a b = true ↔ val a ≤ val b := by
  have ha' : (0 : ℝ) < a.2 := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b.2 := by exact_mod_cast hb
  unfold qle val
  rw [decide_eq_true_iff, div_le_div_iff₀ ha' hb']
  simp only [Int.ofNat_eq_coe]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem qlt_spec {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) :
    qlt a b = true ↔ val a < val b := by
  have ha' : (0 : ℝ) < a.2 := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b.2 := by exact_mod_cast hb
  unfold qlt val
  rw [decide_eq_true_iff, div_lt_div_iff₀ ha' hb']
  simp only [Int.ofNat_eq_coe]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem qadd_den_pos {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (qadd a b).2 :=
  Nat.mul_pos ha hb

theorem qsub_den_pos {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) : 0 < (qsub a b).2 :=
  Nat.mul_pos ha hb

/-! ## K-3: `hornerQ` is P0 `hsum` -/

theorem hornerQ_den_pos (zn : Int) {zd : Nat} (hz : 0 < zd) :
    ∀ k n, 0 < (hornerQ zn zd k n).2
  | _, 0 => by simp [hornerQ]
  | k, n + 1 => by
      have ih := hornerQ_den_pos zn hz (k + 1) n
      simp only [hornerQ]
      exact Nat.mul_pos (Nat.mul_pos (by omega) hz) ih

/-- K-3 -/
theorem hornerQ_val (zn : Int) {zd : Nat} (hz : 0 < zd) (k n : Nat) :
    ((hornerQ zn zd k n).1 : ℚ) / (hornerQ zn zd k n).2 =
      Li2Lean.P0.CA.Contour.hsum ((zn : ℚ) / zd) k n := by
  induction n generalizing k with
  | zero => simp [hornerQ, Li2Lean.P0.CA.Contour.hsum]
  | succ n ih =>
      have hr := hornerQ_den_pos zn hz (k + 1) n
      have hr' : ((hornerQ zn zd (k + 1) n).2 : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
      have hz' : (zd : ℚ) ≠ 0 := by exact_mod_cast hz.ne'
      have hk' : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
      rw [Li2Lean.P0.CA.Contour.hsum, ← ih (k + 1)]
      simp only [hornerQ, Int.ofNat_eq_coe]
      push_cast
      first
        | (field_simp; ring)
        | field_simp

end Li2Lean.V.EnergyCertI.IK
