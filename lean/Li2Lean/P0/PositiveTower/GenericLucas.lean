/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Data.Nat.Choose.Lucas

/-!
  Prime-parametric Lucas reduction for the `2Q` binomial appearing in the
  P0 scaled pencil.  This is deliberately a one-lemma adapter around the
  Mathlib Lucas theorem already used by the 1/2 development; no q-specific
  facts or new obligations are introduced.
-/
namespace Li2Lean.P0.PositiveTower

theorem choose_pow_add_two_mul_modEq {p k u r : ℕ} [Fact (Nat.Prime p)]
    (hr : r < p ^ k) :
    Nat.choose ((u + 2) * p ^ k + r) (2 * p ^ k) ≡
      Nat.choose (u + 2) 2 [MOD p] := by
  induction k generalizing u r with
  | zero =>
      have hr0 : r = 0 := by simpa using hr
      subst r
      simpa using (Nat.ModEq.refl (Nat.choose (u + 2) 2))
  | succ k ih =>
      have hpP : Nat.Prime p := Fact.out
      have hp : 0 < p := hpP.pos
      have hmod : ((u + 2) * p ^ k.succ + r) % p = r % p := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod]
      have hkm : (2 * p ^ k.succ) % p = 0 := by
        simp [pow_succ, Nat.mul_mod]
      have hdiv : ((u + 2) * p ^ k.succ + r) / p =
          (u + 2) * p ^ k + r / p := by
        calc
          ((u + 2) * p ^ k.succ + r) / p =
              (r + p * ((u + 2) * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = r / p + (u + 2) * p ^ k :=
            Nat.add_mul_div_left r ((u + 2) * p ^ k) hp
          _ = (u + 2) * p ^ k + r / p := Nat.add_comm _ _
      have hdivk : (2 * p ^ k.succ) / p = 2 * p ^ k := by
        calc
          (2 * p ^ k.succ) / p = (p * (2 * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = 2 * p ^ k := Nat.mul_div_right _ hp
      have hrdiv : r / p < p ^ k :=
        (Nat.div_lt_iff_lt_mul hp).2 (by
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hr)
      have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := (u + 2) * p ^ k.succ + r) (k := 2 * p ^ k.succ) (p := p)
      have hLucas' :
          Nat.choose ((u + 2) * p ^ k.succ + r) (2 * p ^ k.succ) ≡
            Nat.choose (((u + 2) * p ^ k.succ + r) / p)
              ((2 * p ^ k.succ) / p) [MOD p] := by
        rw [hmod, hkm] at hLucas
        simpa using hLucas
      rw [hdiv, hdivk] at hLucas'
      exact hLucas'.trans (ih hrdiv)

end Li2Lean.P0.PositiveTower
