import Mathlib

/-!
# A concrete, *computable* model of `GF(16)`

Mathlib's `GaloisField 2 4` is noncomputable, so no statement about it can be
discharged by `decide`.  For the sharpness example of
`MTuple.Counterexample` we therefore build the field
`𝔽₂[x]/(x⁴ + x + 1)` by hand on `Fin 16`: an element is the bit pattern of its
coordinate vector in the basis `1, x, x², x³`, addition is bitwise `xor`, and
multiplication is carry-less multiplication reduced modulo `x⁴ = x + 1`.

Every field axiom is checked by `decide`, so the resulting `Field K16` instance
is computable and `Fintype.card K16 = 2 ^ 4`.
-/

namespace MTuple.GF16Model

/-- Multiplication by `x` modulo `x⁴ + x + 1`, on bit patterns. -/
def xt (a : Nat) : Nat := if a &&& 8 == 8 then ((2 * a) % 16) ^^^ 3 else 2 * a

/-- Carry-less multiplication of bit patterns, reduced modulo `x⁴ + x + 1`. -/
def mulN (a b : Nat) : Nat :=
  (if b &&& 1 == 1 then a else 0) ^^^ (if b &&& 2 == 2 then xt a else 0) ^^^
  (if b &&& 4 == 4 then xt (xt a) else 0) ^^^ (if b &&& 8 == 8 then xt (xt (xt a)) else 0)

/-- The carrier of the field with `16` elements. -/
def K16 : Type := Fin 16

instance : DecidableEq K16 := inferInstanceAs (DecidableEq (Fin 16))
instance : Fintype K16 := inferInstanceAs (Fintype (Fin 16))

namespace K16

instance : Zero K16 := ⟨(⟨0, by norm_num⟩ : Fin 16)⟩
instance : One K16 := ⟨(⟨1, by norm_num⟩ : Fin 16)⟩

instance : Add K16 :=
  ⟨fun a b => (⟨((a : Fin 16).val ^^^ (b : Fin 16).val) % 16, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 16)⟩

instance : Mul K16 :=
  ⟨fun a b => (⟨mulN (a : Fin 16).val (b : Fin 16).val % 16, Nat.mod_lt _ (by norm_num)⟩ :
    Fin 16)⟩

/-- In characteristic `2` negation is the identity. -/
instance : Neg K16 := ⟨id⟩

/-- The inverse `a⁻¹ = a¹⁴` (and `0⁻¹ = 0`). -/
instance : Inv K16 := ⟨fun a => (a * a) * ((a * a) * (a * a)) * (((a * a) * (a * a)) *
  ((a * a) * (a * a)))⟩

instance instField : Field K16 :=
  Field.ofMinimalAxioms K16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem two_eq_zero : (2 : K16) = 0 := by decide

instance : CharP K16 2 where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      rcases Nat.even_or_odd n with he | ho
      · exact he.two_dvd
      · exfalso
        obtain ⟨k, hk⟩ := ho
        rw [hk] at h
        push_cast at h
        rw [show ((2 : K16) * (k : K16)) = 0 by rw [two_eq_zero, zero_mul], zero_add] at h
        exact one_ne_zero h
    · rintro ⟨k, rfl⟩
      push_cast
      rw [two_eq_zero, zero_mul]

theorem card_eq : Fintype.card K16 = 2 ^ 4 := by decide

/-- The element of `K16` with bit pattern `k` (for `k < 16`). -/
def ofNat (k : Nat) (h : k < 16 := by norm_num) : K16 := (⟨k, h⟩ : Fin 16)

end K16

end MTuple.GF16Model
