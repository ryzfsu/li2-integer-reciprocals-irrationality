/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

H4 leaf L2c: the v13 H4 profile built from the
committed slab table, its nonnegativity, its support bound, and its exact
integral.

This module is part of the release closure.

Profile pieces (rho = p / (4n)):
* 412 slab pieces `[s.lo, s.hi)`, value `s.slope * rho + s.icpt`
  (`= q5ResidueExponent (4n) p / (4n)` strictly inside the slab, master
  `VSlab.residueExponent_eq`);
* `[5/4, 2)`: `19/4 - 2 rho`  (= `q5OuterCost n p / (4n)` for `5n < p < 8n`);
* `[2, 11/4)`: `11/4 - rho`   (= `q5OuterCost n p / (4n)` for `8n ≤ p ≤ 11n-1`).
No strip piece: `p ≤ n/10` is paid by the theta term of the budget bridge.

Exact integral (the finite-data check): the nine shard integrals below
sum to the slab part, plus `45/32` for the two outer pieces, giving
`v13H4IntegralQ` (bit-exact with the plan constant).
-/

import Li2Lean.B3.H4SlabData
import Li2Lean.B3.H4L4LogBounds
import Li2Lean.Kit.L3WeightedPrime
import Li2Lean.P0.RateProfiles

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.P0.Integerization   -- note: namespace of `P0ProfileNonneg`

/-! ## Pieces -/

/-- A slab that passed `VSlab.ok` gives a profile piece. -/
def vSlabPiece (s : VSlab) (hs : s.ok = true) : PrimeAffinePiece where
  lo := s.lo
  hi := s.hi
  slope := s.slope
  intercept := s.icpt
  lo_pos := lt_of_lt_of_le (by norm_num) (H4Slab.ok_parts hs).1
  lo_lt_hi := (H4Slab.ok_parts hs).2.1

def v13H4OuterPiece1 : PrimeAffinePiece where
  lo := 5 / 4
  hi := 2
  slope := -2
  intercept := 19 / 4
  lo_pos := by norm_num
  lo_lt_hi := by norm_num

def v13H4OuterPiece2 : PrimeAffinePiece where
  lo := 2
  hi := 11 / 4
  slope := -1
  intercept := 11 / 4
  lo_pos := by norm_num
  lo_lt_hi := by norm_num

def v13H4SlabPieces : List PrimeAffinePiece :=
  v13SlabData.pmap vSlabPiece v13SlabData_ok

def v13H4Profile : PrimeAffineProfile :=
  ⟨v13H4SlabPieces ++ [v13H4OuterPiece1, v13H4OuterPiece2]⟩

/-! ## Nonnegativity and support -/

theorem mem_v13H4SlabPieces {q : PrimeAffinePiece} (hq : q ∈ v13H4SlabPieces) :
    ∃ s, ∃ hs : s.ok = true, q = vSlabPiece s hs := by
  unfold v13H4SlabPieces at hq
  obtain ⟨s, hsmem, rfl⟩ := List.mem_pmap.mp hq   -- note: `List.mem_pmap` shape
  exact ⟨s, v13SlabData_ok s hsmem, rfl⟩

theorem v13H4Profile_nonneg : P0ProfileNonneg v13H4Profile := by
  intro q hq y hlo hhi
  simp only [v13H4Profile, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with hq | rfl | rfl
  · obtain ⟨s, hs, rfl⟩ := mem_v13H4SlabPieces hq
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h0lo, h0hi⟩ := H4Slab.ok_parts hs
    -- affine on [lo, hi], nonnegative at both endpoints
    simp only [vSlabPiece] at hlo hhi ⊢
    have h0lo' : (0 : ℝ) ≤ (s.icpt : ℝ) + (s.slope : ℝ) * (s.lo : ℝ) := by
      exact_mod_cast h0lo
    have h0hi' : (0 : ℝ) ≤ (s.icpt : ℝ) + (s.slope : ℝ) * (s.hi : ℝ) := by
      exact_mod_cast h0hi
    have hlohi : (s.lo : ℝ) < (s.hi : ℝ) := by
      exact_mod_cast (H4Slab.ok_parts hs).2.1
    -- y = (1-t) lo + t hi with t ∈ [0,1]
    set t : ℝ := (y - s.lo) / (s.hi - s.lo) with ht
    have hden : (0 : ℝ) < (s.hi : ℝ) - s.lo := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have ht1 : t ≤ 1 := (div_le_one hden).2 (by linarith)
    have hy : y = (1 - t) * s.lo + t * s.hi := by
      rw [ht]; field_simp [hden.ne']; ring   -- note: field_simp normal form
    rw [hy]
    nlinarith [mul_nonneg ht0 h0hi', mul_nonneg (sub_nonneg.2 ht1) h0lo']
  · simp only [v13H4OuterPiece1] at hlo hhi ⊢
    push_cast at hlo hhi ⊢
    linarith
  · simp only [v13H4OuterPiece2] at hlo hhi ⊢
    push_cast at hlo hhi ⊢
    linarith

theorem v13H4Profile_hi_le : ∀ q ∈ v13H4Profile.pieces, (q.hi : ℝ) ≤ 11 / 4 := by
  intro q hq
  simp only [v13H4Profile, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with hq | rfl | rfl
  · obtain ⟨s, hs, rfl⟩ := mem_v13H4SlabPieces hq
    have h := (H4Slab.ok_parts hs).2.2.1
    simp only [vSlabPiece]
    have h' : (s.hi : ℝ) ≤ ((5 / 4 : ℚ) : ℝ) := by
      exact_mod_cast h
    have : (s.hi : ℝ) ≤ 5 / 4 := by
      norm_num at h' ⊢
      exact h'
    linarith
  · norm_num [v13H4OuterPiece1]
  · norm_num [v13H4OuterPiece2]

/-! ## Exact integral -/

/-- Exact integral of one slab piece, over ℚ (products, not `^`, to keep the
kernel evaluation on plain `Rat.mul`). -/
def vSlabPieceIntegral (s : VSlab) : ℚ :=
  s.slope * ((s.hi * s.hi - s.lo * s.lo) / 2) + s.icpt * (s.hi - s.lo)

def vSlabIntegral (l : List VSlab) : ℚ :=
  (l.map vSlabPieceIntegral).sum

theorem vSlabIntegral_append (l₁ l₂ : List VSlab) :
    vSlabIntegral (l₁ ++ l₂) = vSlabIntegral l₁ + vSlabIntegral l₂ := by
  simp [vSlabIntegral, List.map_append, List.sum_append]

theorem pmap_slab_integral (l : List VSlab) (h : ∀ s ∈ l, s.ok = true) :
    ((l.pmap vSlabPiece h).map
        (fun q => ∫ t : ℝ, (singletonPrimeAffineProfile q).eval t)).sum =
      ((vSlabIntegral l : ℚ) : ℝ) := by
  induction l with
  | nil => simp [vSlabIntegral]
  | cons s rest ih =>
    have hrest : ∀ s ∈ rest, s.ok = true := by
      intro t ht
      exact h t (List.mem_cons_of_mem s ht)
    simp only [List.pmap, List.map_cons, List.sum_cons]
    rw [singletonPrimeAffineProfile_integral, ih hrest]
    simp only [vSlabIntegral, List.map_cons, List.sum_cons, vSlabPieceIntegral,
      vSlabPiece]
    push_cast
    ring

/-! Shard integrals, each a kernel-checked ℚ identity (same evaluation regime as
the `VSlab.ok` shards).  Constants from the finite-data check. -/
theorem vSlabIntegral_00 : vSlabIntegral v13SlabData00 =
    (230470539206093913916449989478405454549 : ℚ) /
      22443839635269744723240885063988049049600 := by decide +kernel
theorem vSlabIntegral_01 : vSlabIntegral v13SlabData01 =
    (166204669157982497160519054648996512801 : ℚ) /
      13218863557951417529186109953097175526400 := by decide +kernel
theorem vSlabIntegral_02 : vSlabIntegral v13SlabData02 =
    (66540953806063644382950529881210437 : ℚ) /
      3965806641081054262560881620097491200 := by decide +kernel
theorem vSlabIntegral_03 : vSlabIntegral v13SlabData03 =
    (5190779077045092030213126423037 : ℚ) / 222593724362799915577198075929600 := by
  decide +kernel
theorem vSlabIntegral_04 : vSlabIntegral v13SlabData04 =
    (24850463254913034481041989 : ℚ) / 728669882343804171039360000 := by decide +kernel
theorem vSlabIntegral_05 : vSlabIntegral v13SlabData05 =
    (35842923081372975572353 : ℚ) / 619808900849199341280000 := by decide +kernel
theorem vSlabIntegral_06 : vSlabIntegral v13SlabData06 =
    (1779213603614947 : ℚ) / 16173197924083200 := by decide +kernel
theorem vSlabIntegral_07 : vSlabIntegral v13SlabData07 =
    (8037640139 : ℚ) / 27134553600 := by decide +kernel
theorem vSlabIntegral_08 : vSlabIntegral v13SlabData08 =
    (1121513 : ℚ) / 369600 := by decide +kernel

theorem vSlabIntegral_all :
    vSlabIntegral v13SlabData + 45 / 32 = v13H4IntegralQ := by
  simp only [v13SlabData, vSlabIntegral_append, vSlabIntegral_00, vSlabIntegral_01,
    vSlabIntegral_02, vSlabIntegral_03, vSlabIntegral_04, vSlabIntegral_05,
    vSlabIntegral_06, vSlabIntegral_07, vSlabIntegral_08]
  -- note: `norm_num [v13H4IntegralQ]` on a 9-term ℚ literal sum; alternative
  -- `unfold v13H4IntegralQ; decide +kernel` (closed ℚ equality).
  norm_num [v13H4IntegralQ]

theorem v13H4Profile_integral :
    (∫ t : ℝ, v13H4Profile.eval t) = ((v13H4IntegralQ : ℚ) : ℝ) := by
  rw [show v13H4Profile = PrimeAffineProfile.mk
      (v13H4SlabPieces ++ [v13H4OuterPiece1, v13H4OuterPiece2]) from rfl,
    primeAffineProfile_integral_eq_sum_singletons, List.map_append, List.sum_append]
  unfold v13H4SlabPieces
  rw [pmap_slab_integral, ← vSlabIntegral_all]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    singletonPrimeAffineProfile_integral, v13H4OuterPiece1, v13H4OuterPiece2]
  push_cast
  norm_num

/-- L4 hint specialised to the actual profile: the `hint` argument of
`qv13PrimeSumRate_of_budget`. -/
theorem v13H4_rate_hint {q : ℕ} (hq : SignedVBaseRange q) :
    (∫ t : ℝ, v13H4Profile.eval t) + 13 / 160 - (53 / 48) * Real.log (q : ℝ) <
      vTau q :=
  v13H4_rate_hint_of_integral hq v13H4Profile_integral

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13H4Profile_nonneg
#print axioms Li2Lean.B3.v13H4Profile_integral
#print axioms Li2Lean.B3.v13H4_rate_hint
