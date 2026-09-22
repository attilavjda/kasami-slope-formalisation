import MTuple.Counterexample
import MTupleExt.KasamiMTuple

/-!
# Kernel cross-checks of the exact formula, on a computable `GF(16)`

The general theorems of `MTuple/MTupleExt/ExactAffine.lean` predict, for
a half-size additive subgroup `V` of a field with `2ⁿ` elements and an
admissible coefficient vector `c`,

* `mCount m V c = 2^{(m−1)n−m}`       if `c` is not constant,
* `mCount m V c = 2·2^{(m−1)n−m}`     if `c` is constant.

Here the predictions are checked *by the kernel* (`decide`, no `native_decide`)
against a brute-force count on the computable `GF(16)` model of the library,
with `V` the `𝔽₂`-span of `{1, x, x²}` — the eight bit patterns `0,…,7`.

The contrast with `MTuple.mCount_S16_c16` (count `30`, a half-size set that is
*not* a subgroup) is what makes the subgroup hypothesis visible.
-/

open Finset MTuple.GF16Model MTuple.GF16Model.K16

namespace MTuple

/-- A half-size additive subgroup of `GF(16)`: the bit patterns `0,…,7`. -/
def V8 : Finset K16 :=
  {ofNat 0, ofNat 1, ofNat 2, ofNat 3, ofNat 4, ofNat 5, ofNat 6, ofNat 7}

theorem V8_card : V8.card = 2 ^ (4 - 1) := by decide

theorem V8_addClosed : ∀ x ∈ V8, ∀ y ∈ V8, x + y ∈ V8 := by decide

/-! ## A non-constant vector: the generic count -/

set_option maxRecDepth 100000 in
/-- Brute force: `#{(x,y,z) ∈ V8³ : x + x·y + (1+x)·z = 0} = 32`. -/
theorem mCount_V8_c16 : mCount 3 V8 c16 = 32 := by decide

/-- The brute-force value agrees with the general theorem (non-constant case). -/
theorem mCount_V8_c16_eq_generic : mCount 3 V8 c16 = 2 ^ ((3 - 1) * 4 - 3) := by
  rw [mCount_V8_c16]; norm_num

/-- …and the general theorem, instantiated, gives the same value. -/
theorem mCount_V8_c16_theory : mCount 3 V8 c16 = 2 ^ ((3 - 1) * 4 - 3) :=
  mCount_addClosed_of_not_const (n := 4) (by norm_num) (by norm_num) card_eq V8
    V8_addClosed V8_card c16_mem (by decide)

/-! ## A constant vector at even `m`: twice the generic count -/

/-- The constant vector `(1,1)` is admissible at `m = 2`. -/
theorem c2_mem : (fun _ : Fin 2 => (1 : K16)) ∈ coeffFamily K16 2 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- Brute force: `#{(x,y) ∈ V8² : x + y = 0} = 8`, twice the generic value `4`. -/
theorem mCount_V8_const2 : mCount 2 V8 (fun _ : Fin 2 => (1 : K16)) = 8 := by decide

/-- The brute-force value agrees with the general theorem (constant case). -/
theorem mCount_V8_const2_theory :
    mCount 2 V8 (fun _ : Fin 2 => (1 : K16)) = 2 * 2 ^ ((2 - 1) * 4 - 2) :=
  mCount_addClosed_const_eq_two_mul (n := 4) (by norm_num) (by norm_num) card_eq V8
    V8_addClosed V8_card c2_mem (fun _ => rfl)

theorem mCount_V8_const2_agrees : (8 : ℕ) = 2 * 2 ^ ((2 - 1) * 4 - 2) := by norm_num

/-! ## Axioms of the new results -/

#print axioms mCount_affineTraceHyperplane_of_not_const
#print axioms mCount_affineTraceHyperplane_const
#print axioms mCount_affineTraceHyperplane_const_eq_two_mul
#print axioms mCount_addClosed_of_not_const
#print axioms mCount_addClosed_const_eq_two_mul
#print axioms kasamiMTupleConjecture_odd_of_mod_pm_one
#print axioms kasami_mCount_const
#print axioms not_kasamiMTupleConjecture_even_of_mod_pm_one
#print axioms mCount_V8_c16
#print axioms mCount_V8_const2

end MTuple
