/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.Q11Certificate
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.Tube

open Set

namespace Li2Lean.P0.Q11Data

noncomputable section

/-!
The q = 11 contour leaf is kept separate from the already proved q = 2
receipt. A row carries rational endpoints and an integer numerator/denominator
lower bound. The Boolean layer is deliberately independent of the analytic
row inequality: it checks only the finite exact input, while the latter is an
explicit field of `Q11GammaContourCertificate`.

This avoids treating the printed q = 11 masses as a proof of the shifted field
bound. The missing continuous certificate remains visible to downstream code.
-/

structure Q11GammaRow where
  lo : ℚ
  hi : ℚ
  lower : IntRatio
  deriving DecidableEq, Repr

def q11GammaRowCheck (r : Q11GammaRow) : Bool :=
  decide (0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ 1) &&
    ratioLeBool etaFloor r.lower && decide (0 < r.lower.den)

def q11GammaRowsCheck : List Q11GammaRow → Bool
  | [] => true
  | r :: rs => q11GammaRowCheck r && q11GammaRowsCheck rs

theorem ratioLeBool_sound {x y : IntRatio}
    (h : ratioLeBool x y = true) (hx : 0 < x.den) (hy : 0 < y.den) :
    ratioToReal x ≤ ratioToReal y := by
  have hxy : x.num * (y.den : ℤ) ≤ y.num * (x.den : ℤ) :=
    of_decide_eq_true h
  have hxr : (0 : ℝ) < (x.den : ℝ) := by exact_mod_cast hx
  have hyr : (0 : ℝ) < (y.den : ℝ) := by exact_mod_cast hy
  unfold ratioToReal
  apply (div_le_div_iff₀ hxr hyr).2
  exact_mod_cast hxy

theorem q11GammaRowCheck_floor
    {r : Q11GammaRow} (h : q11GammaRowCheck r = true) :
    ratioToReal etaFloor ≤ ratioToReal r.lower := by
  have hparts :
      (decide (0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ 1) = true ∧
        ratioLeBool etaFloor r.lower = true) ∧
          decide (0 < r.lower.den) = true := by
    simpa [q11GammaRowCheck] using h
  have hden : 0 < r.lower.den := of_decide_eq_true hparts.2
  exact ratioLeBool_sound hparts.1.2 eta_floor_den_pos hden

theorem q11GammaRowsCheck_mem
    {rs : List Q11GammaRow} (h : q11GammaRowsCheck rs = true)
    {r : Q11GammaRow} (hr : r ∈ rs) : q11GammaRowCheck r = true := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
      simp only [q11GammaRowsCheck, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h.1
      · exact ih h.2 hr

theorem q11GammaRowsCheck_floor
    {rs : List Q11GammaRow} (h : q11GammaRowsCheck rs = true)
    {r : Q11GammaRow} (hr : r ∈ rs) :
    ratioToReal etaFloor ≤ ratioToReal r.lower :=
  q11GammaRowCheck_floor (q11GammaRowsCheck_mem h hr)

/-! A finite exact numeric skeleton matching the 64 q = 11 contour nodes.
It is intentionally only a numeric leaf; no analytic row bound is inferred
from it. -/

def q11GammaNumericRows : List Q11GammaRow :=
  (List.range contourNodeCount).map (fun (j : ℕ) =>
    { lo := (j : ℚ) / (contourNodeCount : ℚ)
      hi := ((j + 1 : ℕ) : ℚ) / (contourNodeCount : ℚ)
      lower := etaFloor })

theorem q11GammaNumericRows_length :
    q11GammaNumericRows.length = contourNodeCount := by
  simp [q11GammaNumericRows]

theorem q11GammaNumericRows_check :
    q11GammaRowsCheck q11GammaNumericRows = true := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-! `gammaPoint` takes radians. Normalize every angle to one full turn
before applying the finite row cover. -/

theorem gammaPoint_normalize_period (u : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      gammaPoint u = gammaPoint (2 * Real.pi * t) := by
  let n : ℤ := ⌊u / (2 * Real.pi)⌋
  let t : ℝ := u / (2 * Real.pi) - n
  have hden : 0 < 2 * Real.pi := by positivity
  have hnlo : (n : ℝ) ≤ u / (2 * Real.pi) := by
    dsimp [n]
    exact Int.floor_le _
  have hnhi : u / (2 * Real.pi) < (n : ℝ) + 1 := by
    dsimp [n]
    exact Int.lt_floor_add_one _
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    linarith
  refine ⟨t, ht0, ht1, ?_⟩
  have hangle : u = (2 * Real.pi * t) + (n : ℝ) * (2 * Real.pi) := by
    dsimp [t]
    field_simp [ne_of_gt hden]
    ring
  unfold gammaPoint
  rw [hangle, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! The semantic part of the leaf is local to each normalized row. The finite
row endpoints cover `[0,1]`, while `row_lower` remains the analytic input. -/

structure Q11GammaContourCertificate where
  rows : List Q11GammaRow
  numeric : q11GammaRowsCheck rows = true
  cover : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
    ∃ r ∈ rows, (r.lo : ℝ) ≤ u ∧ u ≤ (r.hi : ℝ)
  row_lower : ∀ r ∈ rows, ∀ u : ℝ,
    (r.lo : ℝ) ≤ u → u ≤ (r.hi : ℝ) →
      ratioToReal r.lower ≤ q11Weta (gammaPoint (2 * Real.pi * u))

theorem q11GammaContourFloor_of_certificate
    (C : Q11GammaContourCertificate) :
    ∀ z ∈ Gamma, ratioToReal etaFloor ≤ q11Weta z := by
  intro z hz
  rcases hz with ⟨θ, rfl⟩
  obtain ⟨u, hu0, hu1, hnormalize⟩ := gammaPoint_normalize_period θ
  obtain ⟨r, hr, hlo, hhi⟩ := C.cover u hu0 hu1
  have hfloor : ratioToReal etaFloor ≤ ratioToReal r.lower :=
    q11GammaRowsCheck_floor C.numeric hr
  have hrow := C.row_lower r hr u hlo hhi
  rw [hnormalize]
  exact hfloor.trans hrow

end

end Li2Lean.P0.Q11Data
