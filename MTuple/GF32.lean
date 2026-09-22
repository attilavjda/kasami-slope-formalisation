import Mathlib

/-!
# A concrete, *computable* model of `GF(32)`

Exactly as `MTuple/MTuple/GF16.lean` does for `GF(16)`, this file builds
the field `𝔽₂[x]/(x⁵ + x² + 1)` by hand on `Fin 32`: an element is the bit
pattern of its coordinate vector in the basis `1, x, x², x³, x⁴`, addition is
bitwise `xor`, and multiplication is carry-less multiplication reduced modulo
`x⁵ = x² + 1`.

The reduction polynomial `x⁵ + x² + 1` is the one used by the exploratory
script `scripts/mtuple_explore_kasami.py`, so the machine-checked counts of
`MTuple/MTupleExt/KasamiFiveFails.lean` are directly comparable with it.

Every field axiom is checked by `decide`, so the resulting `Field K32` instance
is computable and `Fintype.card K32 = 2 ^ 5`.
-/

namespace MTuple.GF32Model

/-- Multiplication by `x` modulo `x⁵ + x² + 1`, on bit patterns. -/
def xt (a : Nat) : Nat := if a &&& 16 == 16 then ((2 * a) % 32) ^^^ 5 else 2 * a

/-- Carry-less multiplication of bit patterns, reduced modulo `x⁵ + x² + 1`. -/
def mulN (a b : Nat) : Nat :=
  (if b &&& 1 == 1 then a else 0) ^^^ (if b &&& 2 == 2 then xt a else 0) ^^^
  (if b &&& 4 == 4 then xt (xt a) else 0) ^^^ (if b &&& 8 == 8 then xt (xt (xt a)) else 0) ^^^
  (if b &&& 16 == 16 then xt (xt (xt (xt a))) else 0)

/-- The carrier of the field with `32` elements. -/
def K32 : Type := Fin 32

instance : DecidableEq K32 := inferInstanceAs (DecidableEq (Fin 32))
instance : Fintype K32 := inferInstanceAs (Fintype (Fin 32))

namespace K32

instance : Zero K32 := ⟨(⟨0, by norm_num⟩ : Fin 32)⟩
instance : One K32 := ⟨(⟨1, by norm_num⟩ : Fin 32)⟩

instance : Add K32 :=
  ⟨fun a b => (⟨((a : Fin 32).val ^^^ (b : Fin 32).val) % 32, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 32)⟩

instance : Mul K32 :=
  ⟨fun a b => (⟨mulN (a : Fin 32).val (b : Fin 32).val % 32, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 32)⟩

/-- In characteristic `2` negation is the identity. -/
instance : Neg K32 := ⟨id⟩

/-- The inverse `a⁻¹ = a³⁰ = a² · a⁴ · a⁸ · a¹⁶` (and `0⁻¹ = 0`). -/
instance : Inv K32 :=
  ⟨fun a =>
    let s2 := a * a
    let s4 := s2 * s2
    let s8 := s4 * s4
    let s16 := s8 * s8
    s2 * s4 * (s8 * s16)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
instance instField : Field K32 :=
  Field.ofMinimalAxioms K32
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem two_eq_zero : (2 : K32) = 0 := by decide

instance : CharP K32 2 where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      rcases Nat.even_or_odd n with he | ho
      · exact he.two_dvd
      · exfalso
        obtain ⟨k, hk⟩ := ho
        rw [hk] at h
        push_cast at h
        rw [show ((2 : K32) * (k : K32)) = 0 by rw [two_eq_zero, zero_mul], zero_add] at h
        exact one_ne_zero h
    · rintro ⟨k, rfl⟩
      push_cast
      rw [two_eq_zero, zero_mul]

theorem card_eq : Fintype.card K32 = 2 ^ 5 := by decide

/-- The element of `K32` with bit pattern `k` (for `k < 32`). -/
def ofNat (k : Nat) (h : k < 32 := by norm_num) : K32 := (⟨k, h⟩ : Fin 32)

end K32

end MTuple.GF32Model
