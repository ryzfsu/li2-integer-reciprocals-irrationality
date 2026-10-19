/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
Phase B front-end statement from v13 `main.tex:97-103`. The challenge is a
theorem with the exact all-n signature; conditional bridge scaffolding lives
in a separate development file and is not part of this interface.
-/

theorem li2_inv_irrational (n : ℤ) (hn : n ≠ 0) :
    Irrational
      (∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) /
        ((k : ℝ) + 1) ^ 2) := by
  sorry
