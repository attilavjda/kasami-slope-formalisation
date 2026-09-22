import Mathlib

/-!
# A concrete, *computable* model of `GF(128)`

As in `MTuple/MTuple/GF16.lean` and `MTuple/MTuple/GF32.lean`,
the field `𝔽₂[x]/(x⁷ + x + 1)` is built by hand on `Fin 128`: an element is the
bit pattern of its coordinate vector in the basis `1, x, …, x⁶`, addition is
bitwise `xor`, and multiplication is carry-less multiplication reduced modulo
`x⁷ = x + 1`.  This is the reduction polynomial used by the exploratory script
`scripts/mtuple_explore_kasami.py`.

With `128³ = 2\,097\,152` triples the kernel evaluation of associativity and
distributivity is out of reach, so the ten field axioms are discharged by
`native_decide`; the resulting `Field K128` instance is computable and
`Fintype.card K128 = 2 ^ 7`.
-/

namespace MTuple.GF128Model

/-- Multiplication by `x` modulo `x⁷ + x + 1`, on bit patterns. -/
def xt (a : Nat) : Nat := if a &&& 64 == 64 then ((2 * a) % 128) ^^^ 3 else 2 * a

/-- Carry-less multiplication of bit patterns, reduced modulo `x⁷ + x + 1`. -/
def mulN (a b : Nat) : Nat :=
  (if b &&& 1 == 1 then a else 0) ^^^ (if b &&& 2 == 2 then xt a else 0) ^^^
  (if b &&& 4 == 4 then xt (xt a) else 0) ^^^ (if b &&& 8 == 8 then xt (xt (xt a)) else 0) ^^^
  (if b &&& 16 == 16 then xt (xt (xt (xt a))) else 0) ^^^
  (if b &&& 32 == 32 then xt (xt (xt (xt (xt a)))) else 0) ^^^
  (if b &&& 64 == 64 then xt (xt (xt (xt (xt (xt a))))) else 0)

/-- The carrier of the field with `128` elements. -/
def K128 : Type := Fin 128

instance : DecidableEq K128 := inferInstanceAs (DecidableEq (Fin 128))
instance : Fintype K128 := inferInstanceAs (Fintype (Fin 128))

namespace K128

instance : Zero K128 := ⟨(⟨0, by norm_num⟩ : Fin 128)⟩
instance : One K128 := ⟨(⟨1, by norm_num⟩ : Fin 128)⟩

instance : Add K128 :=
  ⟨fun a b => (⟨((a : Fin 128).val ^^^ (b : Fin 128).val) % 128, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 128)⟩

instance : Mul K128 :=
  ⟨fun a b => (⟨mulN (a : Fin 128).val (b : Fin 128).val % 128, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 128)⟩

/-- In characteristic `2` negation is the identity. -/
instance : Neg K128 := ⟨id⟩

/-- The inverse `a⁻¹ = a¹²⁶ = a² · a⁴ · a⁸ · a¹⁶ · a³² · a⁶⁴` (and `0⁻¹ = 0`). -/
instance : Inv K128 :=
  ⟨fun a =>
    let s2 := a * a
    let s4 := s2 * s2
    let s8 := s4 * s4
    let s16 := s8 * s8
    let s32 := s16 * s16
    let s64 := s32 * s32
    (s2 * s4) * (s8 * s16) * (s32 * s64)⟩

set_option maxRecDepth 100000 in
instance instField : Field K128 :=
  Field.ofMinimalAxioms K128
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

theorem two_eq_zero : (2 : K128) = 0 := by decide

instance : CharP K128 2 where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      rcases Nat.even_or_odd n with he | ho
      · exact he.two_dvd
      · exfalso
        obtain ⟨k, hk⟩ := ho
        rw [hk] at h
        push_cast at h
        rw [show ((2 : K128) * (k : K128)) = 0 by rw [two_eq_zero, zero_mul], zero_add] at h
        exact one_ne_zero h
    · rintro ⟨k, rfl⟩
      push_cast
      rw [two_eq_zero, zero_mul]

set_option maxRecDepth 4000 in
theorem card_eq : Fintype.card K128 = 2 ^ 7 := by decide

/-- The element of `K128` with bit pattern `k` (for `k < 128`). -/
def ofNat (k : Nat) (h : k < 128 := by norm_num) : K128 := (⟨k, h⟩ : Fin 128)

end K128

end MTuple.GF128Model
