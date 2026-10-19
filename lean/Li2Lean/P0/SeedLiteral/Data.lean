import Mathlib
namespace Li2Lean.P0.SeedLiteral

open Matrix

instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

abbrev F83 := ZMod 83
abbrev Mat64 := Matrix (Fin 64) (Fin 64) F83
end Li2Lean.P0.SeedLiteral
