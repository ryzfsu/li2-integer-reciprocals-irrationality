/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFormalMoments
import Li2Lean.P0.Pole.DerivativeFormB
import Li2Lean.P0.Pole.DivDiff
import Li2Lean.P0.Pole.BinomialPoly

/-!
# Pole coefficient interfaces

This file fixes the L4 names and exact coefficient targets used by the
matrix/order layers.  The algebraic proofs remain separate obligations while
L3 is being integrated; the statements are deliberately coefficient-level and
do not assert the uniform pole divisor.
-/

namespace Li2Lean.P0.Pole

open Polynomial Finset
open Li2Lean.P0.Integerization

noncomputable section

abbrev shiftB : BivPoly →+* BivPoly := Polynomial.compRingHom (Polynomial.X + 1)
abbrev unshiftB : BivPoly →+* BivPoly := Polynomial.compRingHom (Polynomial.X - 1)
abbrev cq (r : ℚ) : Polynomial ℚ := Polynomial.C r

def cpoly (g s : ℕ) : ℚ[X] := C ((-1 : ℚ) ^ (s - 1) / s) * bp g (g - s)
def epoly (t k : ℕ) : ℚ[X] := bp k (k - t)
def piPoly (g t : ℕ) : ℚ[X] := ∑ k ∈ Icc t g, cpoly g k * epoly t k
def psiPoly (g t : ℕ) : ℚ[X] :=
  ∑ k ∈ Icc t g, C ((k : ℚ)⁻¹) * (∑ s ∈ Ioc k g, cpoly g s) * epoly t k

theorem piPoly_natDegree_le (g t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    (piPoly g t).natDegree ≤ g - t := by
  unfold piPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rcases Finset.mem_Icc.mp hk with ⟨hkt, hkg⟩
  have hc : (cpoly g k).natDegree ≤ g - k := by
    unfold cpoly
    exact (natDegree_C_mul_le _ _).trans (bp_natDegree_le _ _)
  have he : (epoly t k).natDegree ≤ k - t := by
    unfold epoly
    exact bp_natDegree_le _ _
  calc
    (cpoly g k * epoly t k).natDegree ≤
        (cpoly g k).natDegree + (epoly t k).natDegree := natDegree_mul_le
    _ ≤ (g - k) + (k - t) := Nat.add_le_add hc he
    _ = g - t := by omega

theorem unshiftB_shiftB (f : BivPoly) : unshiftB (shiftB f) = f := by
  simp [Polynomial.comp_assoc]

theorem shiftB_aVar : shiftB aVar = Polynomial.X + 1 := by simp [aVar]
theorem shiftB_ratConst (r : ℚ) : shiftB (ratConst r) = ratConst r := by
  simp [ratConst]
theorem shiftB_aVar_sub_one : shiftB (aVar - ratConst 1) = Polynomial.X := by
  simp [aVar, ratConst]

theorem coeff_shift_aVar_pow_mul_formalQNum
    (g s i k : ℕ) (hsg : s ≤ g) (hk : k < g) :
    (shiftB (aVar ^ i * formalQNum g s)).coeff k =
      cq (if g - s ≤ k then ((i + s).choose (k - (g - s)) : ℕ) else 0) := by
  have hrw : shiftB (aVar ^ i * formalQNum g s) =
      (X : BivPoly) ^ (g - s) *
        (((X : BivPoly) + 1) ^ (i + s) - ((X : BivPoly) + 1) ^ i * (X : BivPoly) ^ s) := by
    simp only [formalQNum, map_mul, map_pow, map_sub, shiftB_aVar, shiftB_ratConst]
    simp only [ratConst, Polynomial.C_1]
    ring
  rw [hrw, Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_mul_X_pow',
      if_neg (by omega), sub_zero]
    simp [cq, h]
  · simp [cq, h]

theorem coeff_shift_formalTScaled
    (g i t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    (shiftB (formalTScaled g i)).coeff (g - t) =
      cq ((piPoly g t).eval (i : ℚ)) := by
  classical

  let w : ℕ → ℚ := fun s =>
    ((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
      (Nat.choose (i + g) (g - (s + 1)) : ℚ)

  let F : BivPoly :=
    (aVar - ratConst 1) ^ g *
      (∑ r ∈ range i,
        formalU g (i - (r + 1)) *
          ratConst ((r + 1 : ℚ)⁻¹))

  let S : BivPoly :=
    aVar ^ i *
      (∑ s ∈ range g,
        ratConst (w s) * formalQNum g (s + 1))

  have hform : formalTScaled g i = F + S := by
    rfl

  have hk : g - t < g := by omega

  have hX : shiftB aVar = aVar + 1 := by
    change
      (X : BivPoly).comp (X + 1) =
        (X : BivPoly) + 1
    simp

  have hC (r : ℚ) :
      shiftB (ratConst r) = ratConst r := by
    change
      (C (C r) : BivPoly).comp (X + 1) =
        C (C r)
    simp

  have hone : ratConst (1 : ℚ) = (1 : BivPoly) := by
    simp [ratConst, Polynomial.C_1]

  have hsub : shiftB (aVar - ratConst 1) = aVar := by
    calc
      shiftB (aVar - ratConst 1) =
          shiftB aVar - shiftB (ratConst 1) := by
            rw [map_sub]
      _ = aVar + 1 - 1 := by
            rw [hX, hone, map_one]
      _ = aVar := by ring

  -- The first summand is divisible by X^g after shifting.
  have hfirst :
      (shiftB F).coeff (g - t) = 0 := by
    dsimp only [F]
    rw [map_mul, map_pow, hsub]
    change
      ((X : BivPoly) ^ g *
        shiftB
          (∑ r ∈ range i,
            formalU g (i - (r + 1)) *
              ratConst ((r + 1 : ℚ)⁻¹))).coeff
                (g - t) = 0
    rw [Polynomial.coeff_X_pow_mul']
    simp [show ¬ g ≤ g - t by omega]

  -- Each summand of the second part is evaluated using
  -- coeff_shift_aVar_pow_mul_formalQNum.
  have hentry (s : ℕ) (hs : s < g) :
      (shiftB
        (aVar ^ i *
          (ratConst (w s) *
            formalQNum g (s + 1)))).coeff (g - t) =
        cq (w s) *
          cq (if t ≤ s + 1 then
            ((i + s + 1).choose (s + 1 - t) : ℕ)
            else 0) := by

    have hsle : s + 1 ≤ g := by omega

    calc
      (shiftB
        (aVar ^ i *
          (ratConst (w s) *
            formalQNum g (s + 1)))).coeff (g - t) =
          (ratConst (w s) *
            shiftB
              (aVar ^ i *
                formalQNum g (s + 1))).coeff (g - t) := by
                  rw [mul_left_comm, map_mul, hC]

      _ = cq (w s) *
          cq (if g - (s + 1) ≤ g - t then
            ((i + (s + 1)).choose
              ((g - t) - (g - (s + 1))) : ℕ)
            else 0) := by
              have hrat : ratConst (w s) =
                  Polynomial.C (cq (w s)) := rfl
              rw [hrat, Polynomial.coeff_C_mul,
                coeff_shift_aVar_pow_mul_formalQNum
                  g (s + 1) i (g - t) hsle hk]

      _ = cq (w s) *
          cq (if t ≤ s + 1 then
            ((i + s + 1).choose (s + 1 - t) : ℕ)
            else 0) := by
              by_cases hst : t ≤ s + 1
              · have hc :
                    g - (s + 1) ≤ g - t := by omega
                have hd :
                    (g - t) - (g - (s + 1)) =
                      (s + 1) - t := by omega
                simp [hc, hst, hd, Nat.add_assoc]
              · have hc :
                    ¬ g - (s + 1) ≤ g - t := by omega
                simp [hc, hst]

  -- Rewrite the shifted second summand as a sum of constants.
  have hS :
      (shiftB S).coeff (g - t) =
        ∑ s ∈ range g,
          cq (if t ≤ s + 1 then
            w s *
              (Nat.choose (i + s + 1) (s + 1 - t) : ℚ)
            else 0) := by

    dsimp only [S]
    rw [Finset.mul_sum, map_sum,
      Polynomial.finsetSum_coeff]

    apply Finset.sum_congr rfl
    intro s hs

    rw [hentry s (Finset.mem_range.mp hs)]

    by_cases hst : t ≤ s + 1
    · simp only [if_pos hst]
      simpa only [cq] using
        ((C : ℚ →+* ℚ[X]).map_mul
          (w s)
          (Nat.choose (i + s + 1) (s + 1 - t) : ℚ)).symm
    · simp [hst, cq, Polynomial.C_0]

  -- Reindex k = s + 1, discarding the terms k < t.
  have hRange (n : ℕ) (f : ℕ → ℚ) :
      (∑ s ∈ range n,
        if t ≤ s + 1 then f (s + 1) else 0) =
        ∑ k ∈ Icc t n, f k := by

    induction n with
    | zero =>
        have h0 : Icc t 0 = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty_of_lt (by omega)
        simp [h0]

    | succ n ih =>
        rw [Finset.sum_range_succ, ih]

        by_cases htn : t ≤ n + 1
        · rw [Finset.sum_Icc_succ_top htn f]
          simp [htn]

        · have hn : Icc t n = (∅ : Finset ℕ) :=
            Finset.Icc_eq_empty_of_lt (by omega)

          have hn' :
              Icc t (n + 1) = (∅ : Finset ℕ) :=
            Finset.Icc_eq_empty_of_lt (by omega)

          simp [hn, hn', htn]

  -- Evaluate piPoly and express it in the same range-g form.
  have heval :
      (piPoly g t).eval (i : ℚ) =
        ∑ s ∈ range g,
          if t ≤ s + 1 then
            w s *
              (Nat.choose (i + s + 1) (s + 1 - t) : ℚ)
          else 0 := by

    rw [piPoly, Polynomial.eval_finsetSum]

    rw [← hRange g
      (fun k =>
        (cpoly g k * epoly t k).eval (i : ℚ))]

    apply Finset.sum_congr rfl
    intro s hs

    by_cases hst : t ≤ s + 1
    · simp only [if_pos hst]

      have hpred : s + 1 - 1 = s := by omega

      have hbp :
          (bp ((s + 1 : ℕ) : ℤ) (s + 1 - t)).eval (i : ℚ) =
            (((i + (s + 1)).choose (s + 1 - t) : ℕ) : ℚ) := by
        simpa using bp_eval_nat (s + 1) (s + 1 - t) i
      have hbg :
          (bp (g : ℤ) (g - (s + 1))).eval (i : ℚ) =
            (((i + g).choose (g - (s + 1)) : ℕ) : ℚ) := by
        simpa using bp_eval_nat g (g - (s + 1)) i
      simp only [cpoly, epoly, eval_mul, eval_C]
      rw [hbp, hbg]
      simp [w, hpred, Nat.cast_add, Nat.add_assoc, mul_assoc]

    · simp [hst]

  -- Combine the two pieces and map the scalar sum through C.
  calc
    (shiftB (formalTScaled g i)).coeff (g - t) =
        (shiftB S).coeff (g - t) := by
          rw [hform, map_add, Polynomial.coeff_add,
            hfirst, zero_add]

    _ = ∑ s ∈ range g,
          cq (if t ≤ s + 1 then
            w s *
              (Nat.choose (i + s + 1) (s + 1 - t) : ℚ)
            else 0) := hS

    _ = cq
          (∑ s ∈ range g,
            if t ≤ s + 1 then
              w s *
                (Nat.choose (i + s + 1) (s + 1 - t) : ℚ)
            else 0) := by
              simp only [cq, map_sum]

    _ = cq ((piPoly g t).eval (i : ℚ)) := by
          rw [heval]
theorem coeff_shift_formalBScaled
    (g i t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    (shiftB (formalBScaled g i)).coeff (g - t) =
      cq ((psiPoly g t).eval (i : ℚ)) := by
  classical

  let u : ℕ → ℚ := fun s =>
    ((-1 : ℚ) ^ s / (s : ℚ)) *
      (Nat.choose (i + g) (g - s) : ℚ)

  let F : BivPoly :=
    (aVar - ratConst 1) ^ g *
      (∑ r ∈ range i,
        formalU g (i - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹ ^ 2))

  let S : BivPoly :=
    aVar ^ i *
      (∑ s ∈ Icc 2 g,
        ratConst (u s) *
          (∑ r ∈ range (s - 1),
            ratConst ((r + 1 : ℚ)⁻¹) * formalQNum g (r + 1)))

  have hform : formalBScaled g i = F - S := by
    rfl

  have hk : g - t < g := by omega

  have hX : shiftB aVar = aVar + 1 := by
    change
      (X : BivPoly).comp (X + 1) =
        (X : BivPoly) + 1
    simp

  have hC (r : ℚ) :
      shiftB (ratConst r) = ratConst r := by
    change
      (C (C r) : BivPoly).comp (X + 1) =
        C (C r)
    simp

  have hone : ratConst (1 : ℚ) = (1 : BivPoly) := by
    simp [ratConst, Polynomial.C_1]

  have hsub : shiftB (aVar - ratConst 1) = aVar := by
    calc
      shiftB (aVar - ratConst 1) =
          shiftB aVar - shiftB (ratConst 1) := by
            rw [map_sub]
      _ = aVar + 1 - 1 := by
            rw [hX, hone, map_one]
      _ = aVar := by ring

  have hfirst :
      (shiftB F).coeff (g - t) = 0 := by
    dsimp only [F]
    rw [map_mul, map_pow, hsub]
    change
      ((X : BivPoly) ^ g *
        shiftB
          (∑ r ∈ range i,
            formalU g (i - (r + 1)) *
              ratConst ((r + 1 : ℚ)⁻¹ ^ 2))).coeff
                (g - t) = 0
    rw [Polynomial.coeff_X_pow_mul']
    simp [show ¬ g ≤ g - t by omega]

  have hentry (s r : ℕ) (hs : s ∈ Icc 2 g)
      (hr : r ∈ range (s - 1)) :
      (shiftB
        (aVar ^ i *
          (ratConst (u s) *
            (ratConst ((r + 1 : ℚ)⁻¹) *
              formalQNum g (r + 1))))).coeff (g - t) =
        cq (u s * (r + 1 : ℚ)⁻¹ *
          (if t ≤ r + 1 then
            (Nat.choose (i + r + 1) (r + 1 - t) : ℚ)
            else 0)) := by
    have hsg : r + 1 ≤ g := by
      have hrs : r < s - 1 := Finset.mem_range.mp hr
      have hsg' : s ≤ g := Finset.mem_Icc.mp hs |>.2
      omega
    calc
      (shiftB
        (aVar ^ i *
          (ratConst (u s) *
            (ratConst ((r + 1 : ℚ)⁻¹) *
              formalQNum g (r + 1))))).coeff (g - t) =
          (ratConst (u s) *
            (ratConst ((r + 1 : ℚ)⁻¹) *
              shiftB (aVar ^ i * formalQNum g (r + 1)))).coeff
                (g - t) := by
                  simp only [map_mul, hC]
                  apply congrArg (fun z : BivPoly => z.coeff (g - t))
                  ring
      _ = cq (u s * (r + 1 : ℚ)⁻¹) *
          cq (if g - (r + 1) ≤ g - t then
            ((i + (r + 1)).choose
              ((g - t) - (g - (r + 1))) : ℕ)
            else 0) := by
              have hrat1 : ratConst (u s) =
                  Polynomial.C (cq (u s)) := rfl
              have hrat2 : ratConst ((r + 1 : ℚ)⁻¹) =
                  Polynomial.C (cq ((r + 1 : ℚ)⁻¹)) := rfl
              rw [hrat1, hrat2, Polynomial.coeff_C_mul,
                Polynomial.coeff_C_mul,
                coeff_shift_aVar_pow_mul_formalQNum
                  g (r + 1) i (g - t) hsg hk]
              simp [cq, Polynomial.C_mul, mul_assoc]

      _ = cq (u s * (r + 1 : ℚ)⁻¹ *
          (if t ≤ r + 1 then
            (Nat.choose (i + r + 1) (r + 1 - t) : ℚ)
            else 0)) := by
              by_cases hrt : t ≤ r + 1
              · have hc : g - (r + 1) ≤ g - t := by omega
                have hd : (g - t) - (g - (r + 1)) = r + 1 - t := by omega
                simp [hc, hrt, hd, Nat.add_assoc, mul_assoc, cq]
              · have hc : ¬ g - (r + 1) ≤ g - t := by omega
                simp [hc, hrt, cq]

  have hRange (n : ℕ) (f : ℕ → ℚ[X]) :
      (∑ r ∈ range n,
        if t ≤ r + 1 then f (r + 1) else 0) =
        ∑ k ∈ Icc t n, f k := by
    induction n with
    | zero =>
        have h0 : Icc t 0 = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty_of_lt (by omega)
        simp [h0]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        by_cases htn : t ≤ n + 1
        · rw [Finset.sum_Icc_succ_top htn f]
          simp [htn]
        · have hn : Icc t n = (∅ : Finset ℕ) :=
            Finset.Icc_eq_empty_of_lt (by omega)
          have hn' : Icc t (n + 1) = (∅ : Finset ℕ) :=
            Finset.Icc_eq_empty_of_lt (by omega)
          simp [hn, hn', htn]

  have hS0 :
      (shiftB S).coeff (g - t) =
        ∑ s ∈ Icc 2 g, ∑ r ∈ range (s - 1),
          cq (u s * (r + 1 : ℚ)⁻¹ *
            (if t ≤ r + 1 then
              (Nat.choose (i + r + 1) (r + 1 - t) : ℚ)
              else 0)) := by
    dsimp only [S]
    simp only [Finset.mul_sum, map_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro r hr
    simpa [mul_assoc] using hentry s r hs hr

  have hS :
      (shiftB S).coeff (g - t) =
        ∑ s ∈ Icc 2 g, ∑ k ∈ Icc t (s - 1),
          cq (u s * (k : ℚ)⁻¹ *
            (Nat.choose (i + k) (k - t) : ℚ)) := by
    rw [hS0]
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ r ∈ range (s - 1),
          cq (u s * (r + 1 : ℚ)⁻¹ *
            (if t ≤ r + 1 then
              (Nat.choose (i + r + 1) (r + 1 - t) : ℚ)
              else 0))) =
          ∑ r ∈ range (s - 1),
            if t ≤ r + 1 then
              cq (u s * ((r + 1 : ℕ) : ℚ)⁻¹ *
                (Nat.choose (i + (r + 1)) ((r + 1) - t) : ℚ))
            else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              by_cases hrt : t ≤ r + 1
              · simp [hrt, Nat.cast_add, Nat.add_assoc]
              · simp [hrt]
      _ = ∑ k ∈ Icc t (s - 1),
          cq (u s * (k : ℚ)⁻¹ *
            (Nat.choose (i + k) (k - t) : ℚ)) :=
          hRange (s - 1) (fun k =>
            cq (u s * (k : ℚ)⁻¹ *
              (Nat.choose (i + k) (k - t) : ℚ)))

  let f : ℕ → ℕ → ℚ[X] := fun s k =>
    cq (u s * (k : ℚ)⁻¹ *
      (Nat.choose (i + k) (k - t) : ℚ))

  have hS' :
      (shiftB S).coeff (g - t) =
        ∑ s ∈ Icc 2 g, ∑ k ∈ Icc t (s - 1), f s k := by
    simpa [f] using hS

  have hinner (s : ℕ) (hs : s ≤ g) :
      (∑ k ∈ Icc t (s - 1), f s k) =
        ∑ k ∈ Icc t g, if k < s then f s k else 0 := by
    calc
      (∑ k ∈ Icc t (s - 1), f s k) =
          ∑ k ∈ Icc t (s - 1), if k < s then f s k else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hks : k ≤ s - 1 := Finset.mem_Icc.mp hk |>.2
            have hkt : t ≤ k := Finset.mem_Icc.mp hk |>.1
            have hspos : 0 < s := by omega
            have hss : s - 1 < s := Nat.sub_lt hspos (by norm_num)
            rw [if_pos (lt_of_le_of_lt hks hss)]
      _ = ∑ k ∈ Icc t g, if k < s then f s k else 0 := by
            apply Finset.sum_subset
            · intro k hk
              have hkupper : k ≤ g := by
                exact le_trans (Finset.mem_Icc.mp hk |>.2)
                  (le_trans (Nat.sub_le s 1) hs)
              exact Finset.mem_Icc.mpr
                ⟨Finset.mem_Icc.mp hk |>.1, hkupper⟩
            · intro k hk hkn
              have hnot : ¬ k < s := by
                intro hks
                apply hkn
                exact Finset.mem_Icc.mpr ⟨Finset.mem_Icc.mp hk |>.1, by omega⟩
              rw [if_neg hnot]

  have hinner' (k : ℕ) (hk : k ∈ Icc t g) :
      (∑ s ∈ Icc 2 g, if k < s then f s k else 0) =
        ∑ s ∈ Ioc k g, f s k := by
    have hsub : Ioc k g ⊆ Icc 2 g := by
      intro s hs
      have hsk : k < s := Finset.mem_Ioc.mp hs |>.1
      have hsg : s ≤ g := Finset.mem_Ioc.mp hs |>.2
      have htk : 1 ≤ k := le_trans ht (Finset.mem_Icc.mp hk |>.1)
      exact Finset.mem_Icc.mpr ⟨by omega, hsg⟩
    calc
      (∑ s ∈ Icc 2 g, if k < s then f s k else 0) =
          ∑ s ∈ Ioc k g, if k < s then f s k else 0 := by
            symm
            apply Finset.sum_subset hsub
            intro s hs hsn
            have hnot : ¬ k < s := by
              intro hks
              apply hsn
              exact Finset.mem_Ioc.mpr ⟨hks, Finset.mem_Icc.mp hs |>.2⟩
            rw [if_neg hnot]
      _ = ∑ s ∈ Ioc k g, f s k := by
            apply Finset.sum_congr rfl
            intro s hs
            simp [Finset.mem_Ioc.mp hs |>.1]

  have hswap :
      (∑ s ∈ Icc 2 g, ∑ k ∈ Icc t (s - 1), f s k) =
        ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g, f s k := by
    calc
      (∑ s ∈ Icc 2 g, ∑ k ∈ Icc t (s - 1), f s k) =
          ∑ s ∈ Icc 2 g, ∑ k ∈ Icc t g,
            if k < s then f s k else 0 := by
              apply Finset.sum_congr rfl
              intro s hs
              exact hinner s (Finset.mem_Icc.mp hs |>.2)
      _ = ∑ k ∈ Icc t g, ∑ s ∈ Icc 2 g,
            if k < s then f s k else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g, f s k := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hinner' k hk

  have hpsi_scalar :
      (psiPoly g t).eval (i : ℚ) =
        ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g,
          (k : ℚ)⁻¹ *
            (((-1 : ℚ) ^ (s - 1) / (s : ℚ)) *
              (Nat.choose (i + g) (g - s) : ℚ)) *
            (Nat.choose (i + k) (k - t) : ℚ) := by
    rw [psiPoly, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finsetSum]
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hbp_g :
        (bp (g : ℤ) (g - s)).eval (i : ℚ) =
          (((i + g).choose (g - s) : ℕ) : ℚ) := by
      simpa using bp_eval_nat g (g - s) i
    have hbp_k :
        (bp (k : ℤ) (k - t)).eval (i : ℚ) =
          (((i + k).choose (k - t) : ℕ) : ℚ) := by
      simpa using bp_eval_nat k (k - t) i
    simp only [cpoly, epoly, eval_mul, eval_C]
    rw [hbp_g, hbp_k]
    ring

  have hsign (s : ℕ) (hs : 1 ≤ s) :
      (-1 : ℚ) ^ (s - 1) = - (-1 : ℚ) ^ s := by
    cases s with
    | zero => omega
    | succ n => simp [pow_succ]

  have hpsi :
      cq ((psiPoly g t).eval (i : ℚ)) =
        - ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g, f s k := by
    rw [hpsi_scalar]
    simp only [cq, map_sum]
    have hneg :
        (∑ k ∈ Icc t g, - (∑ s ∈ Ioc k g, f s k)) =
          - ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g, f s k :=
      Finset.sum_neg_distrib _
    rw [← hneg]
    apply Finset.sum_congr rfl
    intro k hk
    have hnegk :
        (∑ s ∈ Ioc k g, - f s k) =
          - ∑ s ∈ Ioc k g, f s k :=
      Finset.sum_neg_distrib _
    rw [← hnegk]
    apply Finset.sum_congr rfl
    intro s hs
    have hsk : k < s := Finset.mem_Ioc.mp hs |>.1
    have hss : 1 ≤ s := by
      have htk : 1 ≤ k := le_trans ht (Finset.mem_Icc.mp hk |>.1)
      omega
    simp only [f, u, cq]
    rw [hsign s hss]
    have hscalar :
        (k : ℚ)⁻¹ * (-(-1 : ℚ) ^ s / (s : ℚ) *
          (Nat.choose (i + g) (g - s) : ℚ)) *
          (Nat.choose (i + k) (k - t) : ℚ) =
        - (((-1 : ℚ) ^ s / (s : ℚ) *
          (Nat.choose (i + g) (g - s) : ℚ)) *
          (k : ℚ)⁻¹ * (Nat.choose (i + k) (k - t) : ℚ)) := by
      ring
    rw [hscalar, map_neg]

  calc
    (shiftB (formalBScaled g i)).coeff (g - t) =
        - (shiftB S).coeff (g - t) := by
          rw [hform, map_sub, Polynomial.coeff_sub, hfirst]
          simp
    _ = - ∑ s ∈ Icc 2 g, ∑ k ∈ Icc t (s - 1), f s k := by
          rw [hS']
    _ = - ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g, f s k := by
          rw [hswap]
    _ = cq ((psiPoly g t).eval (i : ℚ)) := by
          symm
          exact hpsi

private theorem derivative_epoly
    (t s : ℕ) (hts : t ≤ s) :
    derivative (epoly t s) =
      ∑ k ∈ Ico t s,
        C (((s - k : ℕ) : ℚ)⁻¹) * epoly t k := by
  unfold epoly
  rw [derivative_bp_formB]
  apply Finset.sum_bij (fun r _ => s - r)
  · intro r hr
    simp only [mem_Icc] at hr
    simp only [mem_Ico]
    omega
  · intro r₁ hr₁ r₂ hr₂ he
    simp only [mem_Icc] at hr₁ hr₂
    omega
  · intro k hk
    simp only [mem_Ico] at hk
    refine ⟨s - k, ?_, ?_⟩
    · simp only [mem_Icc]
      omega
    · omega
  · intro r hr
    simp only [mem_Icc] at hr
    have hrle : r ≤ s - t := hr.2
    have hsub : s - (s - r) = r := by omega
    have hN : (s : ℤ) - (r : ℤ) = ((s - r : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    have hnt : s - t - r = s - r - t := by omega
    rw [hN, hnt, hsub]

private theorem derivative_cpoly
    (g k : ℕ) (hk : 1 ≤ k) (hkg : k ≤ g) :
    derivative (cpoly g k) =
      -∑ s ∈ Ioc k g,
        C ((s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ))) * cpoly g s := by
  unfold cpoly
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_bp_formA]
  rw [mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_bij (fun r _ => k + r)
  · intro r hr
    simp only [mem_Icc] at hr
    simp only [mem_Ioc]
    omega
  · intro r₁ hr₁ r₂ hr₂ he
    omega
  · intro s hs
    simp only [mem_Ioc] at hs
    refine ⟨s - k, ?_, ?_⟩
    · simp only [mem_Icc]
      omega
    · omega
  · intro r hr
    simp only [mem_Icc] at hr
    have hrpos : 1 ≤ r := hr.1
    have hrle : r ≤ g - k := hr.2
    have hkr : k + r ≤ g := by omega
    have hsk : k + r - k = r := by omega
    have hkn : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    have hrn : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrpos)
    have hsum : ((k + r : ℕ) : ℚ) = (k : ℚ) + (r : ℚ) := by norm_num
    rw [hsk]
    calc
      C ((-1 : ℚ) ^ (k - 1) / k) *
          (C ((-1 : ℚ) ^ (r - 1) / r) * bp (g : ℤ) (g - k - r)) =
          C (((-1 : ℚ) ^ (k - 1) / k) *
            ((-1 : ℚ) ^ (r - 1) / r)) *
            bp (g : ℤ) (g - k - r) := by
              calc
                _ = (C ((-1 : ℚ) ^ (k - 1) / k) *
                  C ((-1 : ℚ) ^ (r - 1) / r)) *
                    bp (g : ℤ) (g - k - r) := by ring
                _ = _ := by rw [Polynomial.C_mul]
      _ = -(C (((k + r : ℕ) : ℚ) /
            ((k : ℚ) * (r : ℚ))) *
            (C ((-1 : ℚ) ^ (k + r - 1) /
              ((k + r : ℕ) : ℚ)) * bp (g : ℤ) (g - (k + r)))) := by
              have hgdiff : g - k - r = g - (k + r) := by omega
              rw [hgdiff]
              have hpow : (-1 : ℚ) ^ (k - 1) * (-1 : ℚ) ^ (r - 1) =
                  -(-1 : ℚ) ^ (k + r - 1) := by
                have hkrpow : (k - 1) + (r - 1) = k + r - 2 := by omega
                rw [← pow_add, hkrpow]
                have hkrsucc : k + r - 1 = (k + r - 2) + 1 := by omega
                rw [hkrsucc, pow_succ]
                ring
              have hscalar :
                  ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
                      ((-1 : ℚ) ^ (r - 1) / (r : ℚ)) =
                    -(((k + r : ℕ) : ℚ) /
                      ((k : ℚ) * (r : ℚ)) *
                      ((-1 : ℚ) ^ (k + r - 1) /
                        ((k + r : ℕ) : ℚ))) := by
                rw [div_mul_div_comm]
                rw [hpow]
                rw [hsum]
                field_simp
              rw [hscalar]
              have hc :
                  C (((k + r : ℕ) : ℚ) /
                    ((k : ℚ) * (r : ℚ)) *
                    ((-1 : ℚ) ^ (k + r - 1) /
                      ((k + r : ℕ) : ℚ))) =
                    C (((k + r : ℕ) : ℚ) /
                      ((k : ℚ) * (r : ℚ))) *
                      C ((-1 : ℚ) ^ (k + r - 1) /
                        ((k + r : ℕ) : ℚ)) := by
                rw [Polynomial.C_mul]
              have hneg : C (-( ((k + r : ℕ) : ℚ) /
                    ((k : ℚ) * (r : ℚ)) *
                    ((-1 : ℚ) ^ (k + r - 1) /
                      ((k + r : ℕ) : ℚ)))) =
                  -C (((k + r : ℕ) : ℚ) /
                    ((k : ℚ) * (r : ℚ)) *
                    ((-1 : ℚ) ^ (k + r - 1) /
                      ((k + r : ℕ) : ℚ))) := by rw [map_neg]
              rw [hneg, hc]
              ring

private theorem psiPoly_eq_neg_derivative_piPoly
    (g t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    psiPoly g t = -derivative (piPoly g t) := by
  classical
  unfold psiPoly piPoly
  have hder :
      derivative (∑ k ∈ Icc t g, cpoly g k * epoly t k) =
        ∑ k ∈ Icc t g,
          ((-∑ s ∈ Ioc k g,
              C ((s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ))) *
                cpoly g s) * epoly t k +
            cpoly g k *
              (∑ l ∈ Ico t k,
                C (((k - l : ℕ) : ℚ)⁻¹) * epoly t l)) := by
    rw [derivative_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := le_trans ht hk'.1
    rw [derivative_mul, derivative_cpoly g k hk1 hk'.2,
      derivative_epoly t k hk'.1]
  have hswap (f : ℕ → ℕ → ℚ[X]) :
      (∑ x ∈ Icc t g, ∑ l ∈ Ico t x, f x l) =
        ∑ l ∈ Icc t g, ∑ x ∈ Ioc l g, f x l := by
    have hleft (x : ℕ) (hx : x ∈ Icc t g) :
        (∑ l ∈ Ico t x, f x l) =
          ∑ l ∈ Icc t g, if l < x then f x l else 0 := by
      have hf : (Icc t g).filter (fun l => l < x) = Ico t x := by
        ext l
        simp only [mem_filter, mem_Icc, mem_Ico]
        have hx' := mem_Icc.mp hx
        omega
      rw [← hf, Finset.sum_filter]
    have hright (l : ℕ) (hl : l ∈ Icc t g) :
        (∑ x ∈ Ioc l g, f x l) =
          ∑ x ∈ Icc t g, if l < x then f x l else 0 := by
      have hf : (Icc t g).filter (fun x => l < x) = Ioc l g := by
        ext x
        simp only [mem_filter, mem_Icc, mem_Ioc]
        have hl' := mem_Icc.mp hl
        omega
      rw [← hf, Finset.sum_filter]
    calc
      _ = ∑ x ∈ Icc t g, ∑ l ∈ Icc t g, if l < x then f x l else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hleft x hx
      _ = ∑ l ∈ Icc t g, ∑ x ∈ Icc t g, if l < x then f x l else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        exact (hright l hl).symm
  rw [hder]
  rw [← Finset.sum_neg_distrib]
  simp only [neg_add, neg_neg, neg_mul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hB :
      (∑ x ∈ Icc t g, cpoly g x *
          ∑ l ∈ Ico t x, C (((x - l : ℕ) : ℚ)⁻¹) * epoly t l) =
        ∑ l ∈ Icc t g, ∑ x ∈ Ioc l g,
          cpoly g x * (C (((x - l : ℕ) : ℚ)⁻¹) * epoly t l) := by
    calc
      _ = ∑ x ∈ Icc t g, ∑ l ∈ Ico t x,
          cpoly g x * (C (((x - l : ℕ) : ℚ)⁻¹) * epoly t l) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ = _ := hswap (fun x l =>
          cpoly g x * (C (((x - l : ℕ) : ℚ)⁻¹) * epoly t l))
  rw [hB]
  have hL :
      (∑ k ∈ Icc t g, (C ((k : ℚ)⁻¹) * ∑ s ∈ Ioc k g, cpoly g s) * epoly t k) =
        ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g,
          (C ((k : ℚ)⁻¹) * cpoly g s) * epoly t k := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (C ((k : ℚ)⁻¹) * ∑ s ∈ Ioc k g, cpoly g s) * epoly t k =
          C ((k : ℚ)⁻¹) * ((∑ s ∈ Ioc k g, cpoly g s) * epoly t k) := by ring
      _ = C ((k : ℚ)⁻¹) *
          (∑ s ∈ Ioc k g, cpoly g s * epoly t k) := by rw [Finset.sum_mul]
      _ = ∑ s ∈ Ioc k g, (C ((k : ℚ)⁻¹) * cpoly g s) * epoly t k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  have hA :
      (∑ k ∈ Icc t g,
        (∑ s ∈ Ioc k g,
          C ((s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ))) * cpoly g s) *
            epoly t k) =
        ∑ k ∈ Icc t g, ∑ s ∈ Ioc k g,
          (C ((s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ))) * cpoly g s) * epoly t k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
  rw [hL, hA]
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro s hs
  have hk' := Finset.mem_Icc.mp hk
  have hs' := Finset.mem_Ioc.mp hs
  have hkn : (k : ℚ) ≠ 0 := by
    have : 0 < k := by omega
    exact_mod_cast (Nat.ne_of_gt this)
  have hskn : ((s - k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hs'.1))
  have hcoef :
      (k : ℚ)⁻¹ = (s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ)) -
        ((s - k : ℕ) : ℚ)⁻¹ := by
    field_simp
    have hcast : (s : ℚ) = (k : ℚ) + ((s - k : ℕ) : ℚ) := by
      exact_mod_cast (Nat.add_sub_of_le (Nat.le_of_lt hs'.1)).symm
    rw [hcast]
    ring
  rw [show C (k : ℚ)⁻¹ =
      C ((s : ℚ) / ((k : ℚ) * ((s - k : ℕ) : ℚ)) -
        ((s - k : ℕ) : ℚ)⁻¹) from congrArg C hcoef]
  rw [Polynomial.C_sub]
  ring

theorem coeff_shift_formalB
    (g i j t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    (shiftB (formalB g i j)).coeff (g - t) =
      cq (dd (piPoly g t) (i : ℚ) (j : ℚ)) := by
  classical
  by_cases hij : i = j
  · subst j
    calc
      (shiftB (formalB g i i)).coeff (g - t) =
          cq ((psiPoly g t).eval (i : ℚ)) := by
        simpa [formalB] using coeff_shift_formalBScaled g i t ht htg
      _ = cq (dd (piPoly g t) (i : ℚ) (i : ℚ)) := by
        rw [psiPoly_eq_neg_derivative_piPoly g t ht htg,
          Polynomial.eval_neg, dd_diag]
  · have hxy : (i : ℚ) ≠ (j : ℚ) := by exact_mod_cast hij
    calc
      (shiftB (formalB g i j)).coeff (g - t) =
          ((shiftB (formalTScaled g i)).coeff (g - t) -
           (shiftB (formalTScaled g j)).coeff (g - t)) *
            cq (((j : ℚ) - (i : ℚ))⁻¹) := by
        rw [formalB]
        simp only [if_neg hij, map_mul, map_sub, shiftB_ratConst]
        change ((shiftB (formalTScaled g i) -
          shiftB (formalTScaled g j)) *
            Polynomial.C (cq (((j : ℚ) - (i : ℚ))⁻¹))).coeff (g - t) = _
        rw [Polynomial.coeff_mul_C, Polynomial.coeff_sub]
      _ = (cq ((piPoly g t).eval (i : ℚ)) -
           cq ((piPoly g t).eval (j : ℚ))) *
            cq (((j : ℚ) - (i : ℚ))⁻¹) := by
        rw [coeff_shift_formalTScaled g i t ht htg,
          coeff_shift_formalTScaled g j t ht htg]
      _ = cq (dd (piPoly g t) (i : ℚ) (j : ℚ)) := by
        rw [dd_of_ne (piPoly g t) hxy]
        simp [cq, div_eq_mul_inv]

theorem coeff_shift_pencilA
    (g i j k : ℕ) (hk : k < g) :
    (shiftB (Polynomial.C Polynomial.X * (aVar - ratConst 1) ^ g *
      formalA g i j)).coeff k = 0 := by
  simp only [map_mul, map_pow, shiftB_aVar_sub_one]
  rw [Polynomial.X_pow_mul_assoc, Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hk]

theorem coeff_zero_shift_formalC (g i j : ℕ) :
    (shiftB (formalC g i j)).coeff 0 =
      cq (dd (bp g g) (i : ℚ) (j : ℚ)) := by
  let P (n : ℕ) : ℚ[X] :=
    (ascPochhammer ℚ n).comp (X + 1)

  have hbp (n : ℕ) :
      bp (n : ℤ) n = C ((n.factorial : ℚ)⁻¹) * P n := by
    apply Polynomial.funext
    intro x
    have hx : x + ((n : ℤ) : ℚ) - (n : ℚ) + 1 = x + 1 := by
      push_cast
      ring
    simp only [bp, P, eval_mul, eval_C, eval_comp, eval_add,
      eval_X, eval_one]
    rw [descPochhammer_eval_eq_ascPochhammer, hx]

  have hder (n i : ℕ) :
      (derivative (ascPochhammer ℚ n)).eval ((i + 1 : ℕ) : ℚ) =
        (ascPochhammer ℚ n).eval ((i + 1 : ℕ) : ℚ) *
          (∑ s ∈ range n, (((i + s + 1 : ℕ) : ℚ)⁻¹)) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        let x : ℚ := ((i + 1 : ℕ) : ℚ)
        let t : ℚ := ((i + n + 1 : ℕ) : ℚ)
        let A : ℚ := (ascPochhammer ℚ n).eval x
        let H : ℚ :=
          ∑ s ∈ range n, (((i + s + 1 : ℕ) : ℚ)⁻¹)

        have hxt : x + (n : ℚ) = t := by
          dsimp [x, t]
          push_cast
          ring

        have ht : t ≠ 0 := by
          dsimp [t]
          positivity

        have hu : t * t⁻¹ = (1 : ℚ) :=
          mul_inv_cancel₀ ht

        rw [sum_range_succ]

        calc
          (derivative (ascPochhammer ℚ (n + 1))).eval x =
              (derivative (ascPochhammer ℚ n)).eval x * t + A := by
                rw [ascPochhammer_succ_right ℚ n]
                simp only [derivative_mul, derivative_add,
                  derivative_X, derivative_natCast, add_zero,
                  eval_add, eval_mul, eval_X, eval_natCast,
                  eval_one, mul_one]
                rw [hxt]
          _ = (A * H) * t + A := by
            rw [ih]
          _ = (A * t) * (H + t⁻¹) := by
            calc
              (A * H) * t + A =
                  (A * t) * H + A * (t * t⁻¹) := by
                    rw [hu]
                    ring
              _ = _ := by ring
          _ = (ascPochhammer ℚ (n + 1)).eval x *
                (H + t⁻¹) := by
            have hval :
                (ascPochhammer ℚ (n + 1)).eval x = A * t := by
              rw [ascPochhammer_succ_right ℚ n]
              simp only [eval_mul, eval_add, eval_X, eval_natCast]
              rw [hxt]
            rw [hval]

  have hPder (n i : ℕ) :
      (derivative (P n)).eval (i : ℚ) =
        (P n).eval (i : ℚ) *
          (∑ s ∈ range n, (((i + s + 1 : ℕ) : ℚ)⁻¹)) := by
    simpa [P, Polynomial.derivative_comp, Nat.cast_add]
      using hder n i

  have hdiag (n i : ℕ) :
      (derivative (bp (n : ℤ) n)).eval (i : ℚ) =
        (((i + n).choose n : ℕ) : ℚ) *
          (∑ s ∈ range n, (((i + s + 1 : ℕ) : ℚ)⁻¹)) := by
    have hev :
        (n.factorial : ℚ)⁻¹ * (P n).eval (i : ℚ) =
          (((i + n).choose n : ℕ) : ℚ) := by
      calc
        _ = (bp (n : ℤ) n).eval (i : ℚ) := by
          rw [hbp n]
          simp
        _ = _ := bp_eval_nat n n i

    rw [hbp n, derivative_mul]
    simp only [derivative_C, derivative_comp, eval_add, eval_X, eval_one,
      eval_C, eval_mul, eval_zero, zero_mul, add_zero, one_mul]
    rw [hPder n i]
    rw [← mul_assoc, hev]
    simp

  have hcoeff (p : BivPoly) :
      (shiftB p).coeff 0 = p.eval (1 : Polynomial ℚ) := by
    rw [coeff_zero_eq_eval_zero]
    change ((Polynomial.compRingHom (X + 1 : BivPoly)) p).eval
      (0 : Polynomial ℚ) = p.eval 1
    rw [Polynomial.coe_compRingHom_apply]
    simp

  have hU (n : ℕ) :
      (formalU g n).eval (1 : Polynomial ℚ) =
        cq (((n + g).choose g : ℕ) : ℚ) := by
    simp [formalU, aVar, ratConst, cq]

  rw [hcoeff]

  by_cases hij : i = j
  · subst j
    rw [dd_diag, hdiag g i]
    unfold formalC
    rw [if_pos rfl]
    rw [eval_mul, eval_neg]
    rw [hU]
    simp [ratConst, cq, Polynomial.eval_finsetSum]

  · have hq : (i : ℚ) ≠ (j : ℚ) := by
      exact_mod_cast hij

    rw [dd_of_ne (bp (g : ℤ) g) hq]
    simp only [formalC, if_neg hij, eval_mul, eval_sub,
      hU, ratConst, eval_C, cq, bp_eval_nat]
    rw [← Polynomial.C_sub, ← Polynomial.C_mul]
    simp only [div_eq_mul_inv]

end

end Li2Lean.P0.Pole
