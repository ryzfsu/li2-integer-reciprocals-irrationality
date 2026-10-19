/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyPenaltyRowsAgy
import Li2Lean.P0.Q11FrequencyIntCert

open MeasureTheory Set

namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.CA.Receipt

/-! Boolean checker for the tight q=11 frequency row lower bound. -/

def q11ActualRowLowerQ (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℚ :=
  ((termsLowM ln ld hn hd q11FrequencyTermsIWeighted : ℤ) : ℚ) / (twoE : ℚ) +
    (-1 / 2 - l2hi / 2 + (ln : ℚ) / ld * (2397895272 / 1000000000) -
      q11NuHiF ((hn : ℚ) / hd))

theorem q11ActualRowLowerQ_cast (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) :
    ((q11ActualRowLowerQ ln ld hn hd : ℚ) : ℝ) =
      q11RowLowerRealWeightedTight ln ld hn hd := by
  unfold q11ActualRowLowerQ q11RowLowerRealWeightedTight
  push_cast
  ring

def q11PieceCheck (p q low : ℚ) : Bool :=
  decide ((1 : ℚ) / 2 ≤ p) && decide (q ≤ 81 / 10) &&
    decide (low ≤ q11ActualRowLowerQ p.num p.den q.num q.den)

theorem q11PieceCheck_sound {p q low : ℚ}
    (h : q11PieceCheck p q low = true) {t : ℝ}
    (hpt : (p : ℝ) ≤ t) (htq : t ≤ (q : ℝ)) :
    (low : ℝ) ≤ q11Wmu t := by
  simp only [q11PieceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hq⟩, hlow⟩ := h
  have hpR : (p : ℝ) = (p.num : ℝ) / (p.den : ℝ) := Rat.cast_def p
  have hqR : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have h0 : (1 / 2 : ℝ) ≤ (p.num : ℝ) / p.den := by
    have hp0 : ((1 / 2 : ℚ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    norm_num at hp0
    simpa only [hpR] using hp0
  have hend : (q.num : ℝ) / q.den ≤ (81 / 10 : ℝ) := by
    have hq0 : (q : ℝ) ≤ ((81 / 10 : ℚ) : ℝ) := by exact_mod_cast hq
    norm_num at hq0
    simpa only [hqR] using hq0
  have hloR : (p.num : ℝ) / p.den ≤ t := by
    simpa only [hpR] using hpt
  have hhiR : t ≤ (q.num : ℝ) / q.den := by
    simpa only [hqR] using htq
  have hb := q11RowLowerRealWeightedTight_le (ln := p.num) (ld := p.den)
    (hn := q.num) (hd := q.den) p.den_pos q.den_pos h0 hend
    hloR hhiR
  have hl : (low : ℝ) ≤ ((q11ActualRowLowerQ p.num p.den q.num q.den : ℚ) : ℝ) := by
    exact_mod_cast hlow
  rw [q11ActualRowLowerQ_cast] at hl
  exact hl.trans hb

def q11Split3Check (c : ReceiptCell) : Bool :=
  q11PieceCheck c.lo (c.lo + (c.hi - c.lo) / 3) c.lower &&
    q11PieceCheck (c.lo + (c.hi - c.lo) / 3)
      (c.lo + 2 * ((c.hi - c.lo) / 3)) c.lower &&
    q11PieceCheck (c.lo + 2 * ((c.hi - c.lo) / 3)) c.hi c.lower

theorem q11Split3Check_sound {c : ReceiptCell}
    (h : q11Split3Check c = true) {t : ℝ}
    (hlo : (c.lo : ℝ) ≤ t) (hhi : t ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ q11Wmu t := by
  simp only [q11Split3Check, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rcases le_total t (((c.lo + (c.hi - c.lo) / 3 : ℚ)) : ℝ) with ht1 | ht1
  · exact q11PieceCheck_sound h1 hlo ht1
  · rcases le_total t (((c.lo + 2 * ((c.hi - c.lo) / 3) : ℚ)) : ℝ) with ht2 | ht2
    · exact q11PieceCheck_sound h2 ht1 ht2
    · exact q11PieceCheck_sound h3 ht2 hhi

def q11CellCheck (c : ReceiptCell) : Bool :=
  q11PieceCheck c.lo c.hi c.lower

theorem q11CellCheck_sound {c : ReceiptCell}
    (h : q11CellCheck c = true) {t : ℝ}
    (hlo : (c.lo : ℝ) ≤ t) (hhi : t ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ q11Wmu t := by
  exact q11PieceCheck_sound h hlo hhi

def q11TermsPairZ (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℤ × ℕ :=
  (termsLowM ln ld hn hd q11FrequencyTermsIWeighted, twoE)

theorem q11TermsPairZ_den_pos (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) :
    0 < (q11TermsPairZ ln ld hn hd).2 := by
  simp [q11TermsPairZ]
  decide

def q11ConstPairZ : ℤ × ℕ :=
  pairSubZ (-1, 2) (pairMulZ (ratPairOfRat l2hi) (1, 2))

theorem q11ConstPairZ_den_pos : 0 < q11ConstPairZ.2 := by
  unfold q11ConstPairZ
  exact pairSubZ_den_pos (by norm_num)
    (pairMulZ_den_pos (ratPairOfRat_den_pos l2hi) (by norm_num))

def q11LinPairZ (ln : ℤ) (ld : ℕ) : ℤ × ℕ :=
  pairMulZ (ln, ld) (2397895272, 1000000000)

theorem q11LinPairZ_den_pos (ln : ℤ) {ld : ℕ} (hld : 0 < ld) :
    0 < (q11LinPairZ ln ld).2 :=
  pairMulZ_den_pos hld (by decide)

def q11NuPairZ (hn : ℤ) (hd : ℕ) : ℤ × ℕ :=
  ratPairOfRat (q11NuHiF ((hn : ℚ) / hd))

theorem q11NuPairZ_den_pos (hn : ℤ) (hd : ℕ) :
    0 < (q11NuPairZ hn hd).2 :=
  ratPairOfRat_den_pos (q11NuHiF ((hn : ℚ) / hd))

/-- Unnormalized `(num, den)` integer evaluation of `q11ActualRowLowerQ`. -/
def q11ActualRowLowerZ (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℤ × ℕ :=
  pairAddZ (q11TermsPairZ ln ld hn hd)
    (pairSubZ (pairAddZ q11ConstPairZ (q11LinPairZ ln ld)) (q11NuPairZ hn hd))

theorem q11ActualRowLowerZ_den_pos (ln : ℤ) {ld : ℕ} (hld : 0 < ld) (hn : ℤ) (hd : ℕ) :
    0 < (q11ActualRowLowerZ ln ld hn hd).2 := by
  unfold q11ActualRowLowerZ
  exact pairAddZ_den_pos (q11TermsPairZ_den_pos ln ld hn hd)
    (pairSubZ_den_pos
      (pairAddZ_den_pos q11ConstPairZ_den_pos (q11LinPairZ_den_pos ln hld))
      (q11NuPairZ_den_pos hn hd))

theorem valZ_q11ActualRowLowerZ (ln : ℤ) {ld : ℕ} (hld : 0 < ld) (hn : ℤ) (hd : ℕ) :
    valZ (q11ActualRowLowerZ ln ld hn hd) = q11ActualRowLowerQ ln ld hn hd := by
  unfold q11ActualRowLowerZ q11ActualRowLowerQ
  rw [valZ_pairAddZ (q11TermsPairZ_den_pos ln ld hn hd)
        (pairSubZ_den_pos
          (pairAddZ_den_pos q11ConstPairZ_den_pos (q11LinPairZ_den_pos ln hld))
          (q11NuPairZ_den_pos hn hd)),
      valZ_pairSubZ
        (pairAddZ_den_pos q11ConstPairZ_den_pos (q11LinPairZ_den_pos ln hld))
        (q11NuPairZ_den_pos hn hd),
      valZ_pairAddZ q11ConstPairZ_den_pos (q11LinPairZ_den_pos ln hld)]
  unfold q11TermsPairZ q11ConstPairZ q11LinPairZ q11NuPairZ
  rw [valZ_pairSubZ (by decide) (pairMulZ_den_pos (ratPairOfRat_den_pos l2hi) (by decide)),
      valZ_pairMulZ, valZ_pairMulZ, valZ_ratPairOfRat, valZ_ratPairOfRat]
  unfold valZ
  push_cast
  ring

/-- Integer cross-multiplied Boolean certificate for `q11PieceCheck`. -/
def q11PieceCheckZ (p q low : ℚ) : Bool :=
  pairLeZ (1, 2) (ratPairOfRat p) &&
  pairLeZ (ratPairOfRat q) (81, 10) &&
  pairLeZ (ratPairOfRat low) (q11ActualRowLowerZ p.num p.den q.num q.den)

theorem q11PieceCheck_eq_true_of_q11PieceCheckZ {p q low : ℚ}
    (h : q11PieceCheckZ p q low = true) :
    q11PieceCheck p q low = true := by
  unfold q11PieceCheckZ at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨hp, hq⟩, hlow⟩
  have hp' := pairLeZ_sound (by decide) (ratPairOfRat_den_pos p) hp
  have hq' := pairLeZ_sound (ratPairOfRat_den_pos q) (by decide) hq
  have hlow' := pairLeZ_sound (ratPairOfRat_den_pos low)
    (q11ActualRowLowerZ_den_pos p.num p.den_pos q.num q.den) hlow
  rw [valZ_ratPairOfRat] at hp' hq' hlow'
  rw [valZ_q11ActualRowLowerZ p.num p.den_pos q.num q.den] at hlow'
  unfold valZ at hp' hq'
  simp only [q11PieceCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, hlow'⟩
  · norm_num at hp' ⊢
    exact hp'
  · norm_num at hq' ⊢
    exact hq'

def q11CellCheckZ (c : ReceiptCell) : Bool :=
  q11PieceCheckZ c.lo c.hi c.lower

theorem q11CellCheck_eq_true_of_q11CellCheckZ {c : ReceiptCell}
    (h : q11CellCheckZ c = true) :
    q11CellCheck c = true :=
  q11PieceCheck_eq_true_of_q11PieceCheckZ h

theorem all_q11CellCheck_of_all_q11CellCheckZ {cells : List ReceiptCell}
    (h : cells.all q11CellCheckZ = true) :
    cells.all q11CellCheck = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  exact q11CellCheck_eq_true_of_q11CellCheckZ (h c hc)

theorem q11ActualPieceSmoke :
    q11PieceCheck (1 / 2 : ℚ) (20481 / 40960 : ℚ)
      (27435768107 / 10000000000 : ℚ) = true :=
  q11PieceCheck_eq_true_of_q11PieceCheckZ (by decide +kernel)

end Li2Lean.P0.Q11Data
