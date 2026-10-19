/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.CA.Contour.LogAtan

/-!
# Integer fixed-point interval kit for the signed-V certificates (v2)

Generated certificate data; compiled in the release.

Kernel-cost design rules (see README §1 for the v1 diagnosis):

* every value reduced by `decide +kernel` is an `Int`/`Nat` built only from
  `Nat.add/sub/mul/div/pow/ble/beq` (GMP-accelerated in the Lean kernel and in
  nanoda); no `Rat`, no `Nat.gcd`, no `Nat.log2`, no `Int` power, no
  well-founded recursion (all recursion is structural on a list or a `Nat`);
* no structure with a proof field is built during evaluation;
* an interval `IV = (lo, hi)` means `[lo / 2^64, hi / 2^64]`; exact rationals
  are unnormalised pairs `QF = (n, d)` meaning `n / d` (`d > 0`), so no gcd is
  ever taken; every rounding is `floor`/`ceil` of an exact rational value;
* transcendental values come from two 2^-8-spaced tables (`ILogTab`,
  `IAtanTab`, each checked once) plus a short Taylor tail with an explicit
  remainder; the evaluator re-checks its own range invariants at run time and
  falls back to a trivially valid bound, so no lemma about `bitlen` is needed.
-/

namespace Li2Lean.V.EnergyCertI.IK

/-- Fixed-point scale `2^64`. -/
def S : Nat := 18446744073709551616

/-- Extra scale for log arguments: `log (n/d) = log (m / 2^192)`, `m = ⌊n 2^192 / d⌋`. -/
def LB : Nat := 192
def SL : Nat := 6277101735386680763835789423207666416102355444464034512896

/-- `(lo, hi)` encodes the real interval `[lo / 2^64, hi / 2^64]`. -/
abbrev IV := Int × Int

/-- Unnormalised exact rational `n / d`. -/
abbrev QF := Int × Nat

def IV.mem (I : IV) (x : ℝ) : Prop := (I.1 : ℝ) / (S : ℝ) ≤ x ∧ x ≤ (I.2 : ℝ) / (S : ℝ)

noncomputable def val (a : QF) : ℝ := (a.1 : ℝ) / (a.2 : ℝ)

/-! ## Exact rational pairs (no normalisation) -/

def qadd (a b : QF) : QF := (a.1 * Int.ofNat b.2 + b.1 * Int.ofNat a.2, a.2 * b.2)
def qneg (a : QF) : QF := (-a.1, a.2)
def qsub (a b : QF) : QF := qadd a (qneg b)
def qmul (a b : QF) : QF := (a.1 * b.1, a.2 * b.2)
def qsq (a : QF) : QF := qmul a a
def qabs (a : QF) : QF := (Int.ofNat a.1.natAbs, a.2)
def qhalf (a : QF) : QF := (a.1, 2 * a.2)
/-- `a / b` for `b.1 ≠ 0` (the sign of `b` is moved to the numerator). -/
def qdiv (a b : QF) : QF :=
  (if b.1 < 0 then -(a.1 * Int.ofNat b.2) else a.1 * Int.ofNat b.2, a.2 * b.1.natAbs)
/-- `a^n` through `Nat.pow` on the absolute value (no `Int` power). -/
def qpow (a : QF) (n : Nat) : QF :=
  (if a.1 < 0 ∧ n % 2 = 1 then -Int.ofNat (a.1.natAbs ^ n) else Int.ofNat (a.1.natAbs ^ n), a.2 ^ n)
def qle (a b : QF) : Bool := decide (a.1 * Int.ofNat b.2 ≤ b.1 * Int.ofNat a.2)
def qlt (a b : QF) : Bool := decide (a.1 * Int.ofNat b.2 < b.1 * Int.ofNat a.2)

/-! ## Outward rounding -/

/-- `⌊n / d⌋` (`Int` `/` is `Int.ediv`; `d > 0`). -/
def fl (n : Int) (d : Nat) : Int := n / Int.ofNat d
def cl (n : Int) (d : Nat) : Int := -((-n) / Int.ofNat d)
def cdivN (a b : Nat) : Nat := (a + b - 1) / b

def zero : IV := (0, 0)
def ofQ (a : QF) : IV := (fl (a.1 * Int.ofNat S) a.2, cl (a.1 * Int.ofNat S) a.2)
def add (I J : IV) : IV := (I.1 + J.1, I.2 + J.2)
def neg (I : IV) : IV := (-I.2, -I.1)
def sub (I J : IV) : IV := (I.1 - J.2, I.2 - J.1)
def smulInt (k : Int) (I : IV) : IV := if 0 ≤ k then (k * I.1, k * I.2) else (k * I.2, k * I.1)
def smulQ (c : QF) (I : IV) : IV :=
  if 0 ≤ c.1 then (fl (c.1 * I.1) c.2, cl (c.1 * I.2) c.2)
  else (fl (c.1 * I.2) c.2, cl (c.1 * I.1) c.2)
def mulI (I J : IV) : IV :=
  (fl (min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2))) S,
   cl (max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2))) S)
def sumI (l : List IV) : IV := l.foldl add zero
/-- `I.hi / 2^64 < K`. -/
def hiLt (I : IV) (K : QF) : Bool := decide (I.2 * Int.ofNat K.2 < K.1 * Int.ofNat S)
def hiLe (I : IV) (K : QF) : Bool := decide (I.2 * Int.ofNat K.2 ≤ K.1 * Int.ofNat S)

/-! ## Tables (data and their one-time checks live in `ILogTab` / `IAtanTab`) -/

/-- Row-major 16-wide table lookup (`Nat.div`/`Nat.mod`, ≤ 32 list steps). -/
def tabGet (t : List (List IV)) (j : Nat) : IV := (t.getD (j / 16) []).getD (j % 16) zero

/-- Exact Horner `Σ_{i<n} z^i / (2(k+i)+1)`, `z = zn / zd`, as an unnormalised
pair: the integer form of P0 `hsum`. -/
def hornerQ (zn : Int) (zd : Nat) : Nat → Nat → Int × Nat
  | _, 0 => (0, 1)
  | k, n + 1 =>
      let r := hornerQ zn zd (k + 1) n
      (Int.ofNat (zd * r.2) + Int.ofNat (2 * k + 1) * zn * r.1, (2 * k + 1) * zd * r.2)

/-! ## Logarithm -/

/-- Binary length for `m < 2^256` by a fixed 8-step search (no `Nat.log2`). -/
def blAux : List Nat → Nat → Nat → Nat
  | [], m, acc => acc + m
  | s :: ss, m, acc => if 2 ^ s ≤ m then blAux ss (m / 2 ^ s) (acc + s) else blAux ss m acc

def bitlen (m : Nat) : Nat := blAux [128, 64, 32, 16, 8, 4, 2, 1] m 0

def logSerAux (un ud : Nat) : Nat → Nat → IV → IV
  | 0, _, acc => acc
  | n + 1, i, acc =>
      let num := un ^ (i + 1) * S
      let den := (i + 1) * ud ^ (i + 1)
      logSerAux un ud n (i + 1)
        (if i % 2 = 0 then (acc.1 + Int.ofNat (num / den), acc.2 + Int.ofNat (cdivN num den))
         else (acc.1 - Int.ofNat (cdivN num den), acc.2 - Int.ofNat (num / den)))

/-- `log (1 + un/ud)` for `0 ≤ un/ud ≤ 1/256`:
`Σ_{i<nt} (-1)^i u^(i+1)/(i+1) ± u^(nt+1)/(1-u)`. -/
def logSer (nt un ud : Nat) : IV :=
  let acc := logSerAux un ud nt 0 zero
  let rem : Int := Int.ofNat (cdivN (un ^ (nt + 1) * S) (ud ^ nt * (ud - un)))
  (acc.1 - rem, acc.2 + rem)

/-- `log (m / 2^192) ∈ [1 - 2^192/m, m/2^192 - 1]` (valid for every `m ≥ 1`). -/
def logFallback (m : Nat) : IV :=
  (Int.ofNat S - Int.ofNat (cdivN (S * SL) m), Int.ofNat (cdivN (m * S) SL) - Int.ofNat S)

end Li2Lean.V.EnergyCertI.IK
