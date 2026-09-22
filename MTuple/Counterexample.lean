import MTuple.Generic
import MTuple.GF16

/-!
# A counterexample: the positivity hypothesis is a genuine restriction

`MTuple.mTupleCount_odd_of_mPhase_nonneg` assumes the phase
`P_m(c) = ∑_{t ≠ 0} ∏ᵢ T̂_S(t cᵢ)` is non-negative at every admissible `c`.  That
hypothesis is satisfiable — `MTuple/MTuple/SignFactorization.lean` and
`MTuple/MTuple/Gold.lean` prove it outright for affine cosets and for
Gold derivative images — but it is not automatic.

In `K16 = 𝔽₂[x]/(x⁴+x+1)` take

`S = {0, 1, x, 1+x, x², 1+x², x³, x+x³}`   (bit patterns `0,1,2,3,4,5,8,10`),
`c = (1, x, 1+x)`,

so `|S| = 2³` and `c` is admissible.  Then `N₃(S,c) = 30`, whereas the generic
value is `2^{(3−1)·4−3} = 32`; by `mPhase_nonneg_iff_forall_generic` some
admissible vector must then have a strictly negative phase
(`exists_mPhase_neg`).

All the arithmetic is checked by `decide` in the computable model
`MTuple/MTuple/GF16.lean`.
-/

open Finset MTuple.GF16Model MTuple.GF16Model.K16

namespace MTuple

/-- The half-size witness set in `GF(16)`. -/
def S16 : Finset K16 :=
  {ofNat 0, ofNat 1, ofNat 2, ofNat 3, ofNat 4, ofNat 5, ofNat 8, ofNat 10}

/-- The admissible coefficient vector `(1, x, 1+x)`. -/
def c16 : Fin 3 → K16 := ![ofNat 1, ofNat 2, ofNat 3]

theorem S16_card : S16.card = 2 ^ (4 - 1) := by decide

theorem c16_mem : c16 ∈ coeffFamily K16 3 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- The `3`-tuple count at `(S16, c16)` is `30`. -/
theorem mCount_S16_c16 : mCount 3 S16 c16 = 30 := by decide

/-- The count at `(S16, c16)` differs from the generic value `2^{(3−1)·4−3} = 32`. -/
theorem mCount_S16_c16_ne_generic : mCount 3 S16 c16 ≠ 2 ^ ((3 - 1) * 4 - 3) := by
  rw [mCount_S16_c16]
  norm_num

/-- **The generic count fails at `m = 3` for this half-size set.** -/
theorem not_forall_mCount_generic :
    ¬ ∀ c ∈ coeffFamily K16 3, mCount 3 S16 c = 2 ^ ((3 - 1) * 4 - 3) := by
  intro h
  exact mCount_S16_c16_ne_generic (h c16 c16_mem)

/-- **Hence the odd-`m` positivity hypothesis fails for this half-size set**:
some admissible coefficient vector has a strictly negative phase.  So
`mTupleCount_odd_of_mPhase_nonneg` really does assume something. -/
theorem not_forall_mPhase_nonneg :
    ¬ ∀ c ∈ coeffFamily K16 3, 0 ≤ mPhase 3 S16 c := by
  intro h
  exact not_forall_mCount_generic
    ((mPhase_nonneg_iff_forall_generic (n := 4) (m := 3) (by norm_num) (by norm_num)
      (by decide) S16 K16.card_eq S16_card).1 h)

/-- The negative phase, stated existentially. -/
theorem exists_mPhase_neg : ∃ c ∈ coeffFamily K16 3, mPhase 3 S16 c < 0 := by
  by_contra hcon
  push_neg at hcon
  exact not_forall_mPhase_nonneg hcon

end MTuple
