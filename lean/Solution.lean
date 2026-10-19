/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.Producers

/-!
The theorem keeps the Challenge signature.  Its named producer obligations
are isolated in `Li2Lean.AllN.Producers`; replacing those obligations
does not alter this interface.
-/

theorem li2_inv_irrational (n : ℤ) (hn : n ≠ 0) :
    Irrational
      (∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) /
        ((k : ℝ) + 1) ^ 2) :=
  Li2Lean.AllNAssembly.li2_inv_irrational_of_producers'
    Li2Lean.AllNAssembly.allNProducers n hn
