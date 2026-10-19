/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ITrans
import Li2Lean.V.Q2Certificate

/-!
# Integer reference data for the v2 certificates

Generated certificate data; compiled in the release.

The printed rows are decoded by the master `Int` decoder
`Q2Certificate.decodeChain` / `decodePoisson` (units `1/(5·10^13)`), never
through `ℚ`.  A chain becomes its endpoint/jump list `(e_k, J_k)` with
`e_k = C_k / U` and `J_k = h_k - h_{k-1}`, `h_i = M_i / (C_i - C_{i-1})`
(the unit cancels), kept as unnormalised `QF` pairs.  The decoding runs inside
each shard's kernel check (a few hundred `Int` operations) so there is no
separate transcription bridge to prove: obligation E-a reads the same
`decodeChain` output.
-/

namespace Li2Lean.V.EnergyCertI

open Li2Lean.V.Q2Certificate
open IK

/-- Decoder unit `5·10^13`. -/
def U : Nat := 50000000000000

structure CP where
  e : QF
  J : QF

structure PR where
  cx : QF
  cy : QF
  w : QF
  mult : Nat

structure IData where
  xp : List CP
  vp : List CP
  zp : List CP
  pre : List PR
  full : List PR
  mx : QF
  mv : QF
  pm : QF

def chainCoords (h : ChainHeader) (es : List ChainEntry) : List Int :=
  h.startUnits :: (decodeChain h es).map ChainPoint.coordinateUnits

def chainMassU (h : ChainHeader) (es : List ChainEntry) : List Int :=
  (decodeChain h es).map ChainPoint.massUnits

/-- Row densities `M_i / (C_i - C_{i-1})` (structural on the first list). -/
def densI : List Int → List Int → List QF
  | [], _ => []
  | a :: tl, ms =>
      match tl, ms with
      | b :: _, m :: ms' => (m, (b - a).natAbs) :: densI tl ms'
      | _, _ => []

/-- `[h_0 - 0, h_1 - h_0, …, -h_{n-1}]`. -/
def jumpsI : QF → List QF → List QF
  | prev, [] => [qneg prev]
  | prev, h :: hs => qsub h prev :: jumpsI h hs

def chainCP (h : ChainHeader) (es : List ChainEntry) : List CP :=
  ((chainCoords h es).zip (jumpsI (0, 1) (densI (chainCoords h es) (chainMassU h es)))).map
    fun p => ⟨(p.1, U), p.2⟩

def prow (mult : Nat) (p : PoissonPoint) : PR :=
  ⟨(p.xUnits, U), (p.yUnits, U), (p.massUnits, U), mult⟩

/-- Prefix rows: multiplicity 2 (row + conjugate) except the final real row. -/
def preRowsI : List PoissonPoint → List PR
  | [] => []
  | p :: tl =>
      match tl with
      | [] => [prow 1 p]
      | _ :: _ => prow 2 p :: preRowsI tl

def sumU (l : List Int) : QF := (l.foldl (· + ·) 0, U)

def mkIData (hx : ChainHeader) (ex : List ChainEntry) (hv : ChainHeader) (ev : List ChainEntry)
    (hz : ChainHeader) (ez : List ChainEntry) (pp : List PoissonEntry) : IData :=
  { xp := chainCP hx ex, vp := chainCP hv ev, zp := chainCP hz ez,
    pre := preRowsI (decodePoisson pp),
    full := (poissonFull (decodePoisson pp)).map (prow 1),
    mx := sumU (chainMassU hx ex), mv := sumU (chainMassU hv ev),
    pm := sumU ((poissonFull (decodePoisson pp)).map PoissonPoint.massUnits) }

/-- Data sanity used by the soundness proofs (all widths positive), checked once per `q`. -/
def widthsPos (h : ChainHeader) (es : List ChainEntry) : Bool :=
  (densI (chainCoords h es) (chainMassU h es)).all fun d => decide (0 < d.2)

end Li2Lean.V.EnergyCertI
