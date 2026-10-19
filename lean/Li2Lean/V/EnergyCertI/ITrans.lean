/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ILogTab
import Li2Lean.V.EnergyCertI.IAtanTab

/-!
# Integer kit: `log` and `arctan` evaluators + the soundness statements

Generated certificate data; compiled in the release.

`logQ nt a` encloses `Real.log (val a)` for `a.1 > 0`, `a.2 > 0`;
`atanQ nt a` encloses `Real.arctan (val a)` for `a.2 > 0`.
Field mode uses `nt = 3` (log) / `2` (arctan), energy mode `7` / `4`.
-/

namespace Li2Lean.V.EnergyCertI.IK

/-- `log (m / 2^192)` for `m ≥ 1`.  With `e = bitlen m - 1`, `p = 2^e`, the
run-time test `p ≤ m < 2p` makes `t = ⌊256 m / p⌋ ∈ [256, 511]`, `j = t - 256`,
`u = (256 m - t p)/(t p) ∈ [0, 1/256)` and
`log (m/2^192) = (e - 192) log 2 + log (1 + j/256) + log (1 + u)`.
If the test fails (never for `m < 2^256`) the trivial bound is used. -/
def logDy (nt m : Nat) : IV :=
  let e := bitlen m - 1
  let p := 2 ^ e
  if 0 < m ∧ p ≤ m ∧ m < 2 * p then
    let t := 256 * m / p
    add (add (smulInt (Int.ofNat e - Int.ofNat LB) L2I) (tabGet logTab (t - 256)))
      (logSer nt (256 * m - t * p) (t * p))
  else logFallback m

/-- `log (a.1 / a.2)` with one table evaluation: `mlo = ⌊a 2^192⌋`, `mhi = ⌈a 2^192⌉`,
lower end `log (mlo/2^192)`, upper end `log (mlo/2^192) + (mhi - mlo)/mlo`
(`log (1 + t) ≤ t`); below `2^-192` the lower end is `1 - 1/x`. -/
def logQ (nt : Nat) (a : QF) : IV :=
  let n := a.1.natAbs
  let mlo := n * SL / a.2
  let mhi := cdivN (n * SL) a.2
  if mlo = 0 then (Int.ofNat S - Int.ofNat (cdivN (S * a.2) n), (logDy nt mhi).2)
  else ((logDy nt mlo).1, (logDy nt mlo).2 + Int.ofNat (cdivN ((mhi - mlo) * S) mlo))

def atanSerAux (vn vd : Nat) : Nat → Nat → IV → IV
  | 0, _, acc => acc
  | n + 1, k, acc =>
      let num := vn ^ (2 * k + 1) * S
      let den := (2 * k + 1) * vd ^ (2 * k + 1)
      atanSerAux vn vd n (k + 1)
        (if k % 2 = 0 then (acc.1 + Int.ofNat (num / den), acc.2 + Int.ofNat (cdivN num den))
         else (acc.1 - Int.ofNat (cdivN num den), acc.2 - Int.ofNat (num / den)))

/-- `arctan (vn/vd)` for `0 ≤ vn/vd ≤ 1/256`: P0 `Sr nt v ± v^(2nt+1)/(2nt+1)`. -/
def atanSer (nt vn vd : Nat) : IV :=
  let acc := atanSerAux vn vd nt 0 zero
  let rem : Int := Int.ofNat (cdivN (vn ^ (2 * nt + 1) * S) ((2 * nt + 1) * vd ^ (2 * nt + 1)))
  (acc.1 - rem, acc.2 + rem)

/-- `arctan (a/b)` for `0 ≤ a ≤ b`, `b > 0`: `j = ⌊256 a / b⌋ ∈ [0, 256]`,
`arctan (a/b) = arctan (j/256) + arctan ((256a - jb)/(256b + ja))` (P0 `arctan_shift`). -/
def atanLe (nt a b : Nat) : IV :=
  let j := 256 * a / b
  add (tabGet atanTab j) (atanSer nt (256 * a - j * b) (256 * b + j * a))

/-- `arctan (x.1 / x.2)` for every `x.1`, `x.2 > 0` (`arctan w = π/2 - arctan (1/w)`
for `w > 1`, oddness for `w < 0`). -/
def atanQ (nt : Nat) (x : QF) : IV :=
  let a := x.1.natAbs
  let r := if a ≤ x.2 then atanLe nt a x.2 else sub halfPiI (atanLe nt x.2 a)
  if x.1 < 0 then neg r else r

/-! ## Soundness

The statements K-1 .. K-9 that the v2 source carried here with `sorry` are
proved in `ISoundArith` (K-1..K-3), `ISoundTab` (K-4) and `ISoundTrans`
(K-5..K-9); this file now holds definitions only (patched the release date,
definitions unchanged). -/

end Li2Lean.V.EnergyCertI.IK
