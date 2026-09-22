import MTuple.Counterexample
import MTupleExt.Normalisation

/-!
# The `m`-tuple conclusions form a strictly increasing hierarchy

Does the `m = 3` statement — "the `3`-tuple count is the generic value at every
admissible coefficient vector" — imply its `m = 5` analogue?  It does not, and
this module proves it with a machine-checked witness in the computable `GF(16)`
model of the library.

Let `S = {0, 1, x, x+1, x², x²+1, x³, x³+x²+x}` (bit patterns
`0,1,2,3,4,5,8,14`).  It is half-size and **not** an additive subgroup, so none
of the mechanisms of `MTuple/MTuple/` apply to it.  Nevertheless

* `S_mCount3_generic` — every admissible `3`-vector gives the generic count `32`;
* `S_mCount5_ne_generic` — the admissible `5`-vector `(1, x, x², x³, x³+x²+x+1)`
  gives `2040`, not the generic `2^{(5−1)·4−5} = 2048`.

So `m = 3` genericity is strictly weaker than `m = 5` genericity: a proof of the
Kasami triple statement carries no automatic information about longer tuples.
The `3`-tuple check is cheap because of the slope normalisation
`MTuple.mCount_three_normalise`: every admissible `3`-vector is a scalar
multiple of `(1, ρ, 1+ρ)`.
-/

open Finset MTuple.GF16Model MTuple.GF16Model.K16

namespace MTuple

/-- A half-size subset of `GF(16)` that is not an additive subgroup. -/
def Ssep : Finset K16 :=
  {ofNat 0, ofNat 1, ofNat 2, ofNat 3, ofNat 4, ofNat 5, ofNat 8, ofNat 14}

/-- The admissible `5`-vector `(1, x, x², x³, x³+x²+x+1)`. -/
def csep : Fin 5 → K16 := ![ofNat 1, ofNat 2, ofNat 4, ofNat 8, ofNat 15]

theorem Ssep_card : Ssep.card = 2 ^ (4 - 1) := by decide

/-- `Ssep` is not closed under addition, so it is not one of the sets reached by
the sign-factorisation mechanism. -/
theorem Ssep_not_addClosed : ¬ (∀ x ∈ Ssep, ∀ y ∈ Ssep, x + y ∈ Ssep) := by decide

theorem csep_mem : csep ∈ coeffFamily K16 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

/-! ## Every admissible `3`-vector gives the generic count -/

set_option maxRecDepth 40000 in
/-- The slope-normalised check: `32` for every slope `ρ ∉ {0,1}`. -/
theorem Ssep_mCount3_slope :
    ∀ r : K16, r ≠ 0 → r ≠ 1 → mCount 3 Ssep ![1, r, 1 + r] = 32 := by decide

/-- **The `m = 3` conclusion holds for `Ssep`**: the generic count at every
admissible coefficient vector. -/
theorem Ssep_mCount3_generic :
    ∀ c ∈ coeffFamily K16 3, mCount 3 Ssep c = 2 ^ ((3 - 1) * 4 - 3) := by
  intro c hc
  obtain ⟨hr0, hr1⟩ := coeff_three_ratio_ne hc
  rw [mCount_three_normalise Ssep hc, Ssep_mCount3_slope _ hr0 hr1]
  norm_num

/-! ## The `m = 5` conclusion fails -/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Brute force over `Ssep⁵`: the count is `2040`. -/
theorem Ssep_mCount5 : mCount 5 Ssep csep = 2040 := by decide

theorem Ssep_mCount5_ne_generic : mCount 5 Ssep csep ≠ 2 ^ ((5 - 1) * 4 - 5) := by
  rw [Ssep_mCount5]
  norm_num

/-! ## The separation -/

/-- **The `m = 3` conclusion does not imply the `m = 5` conclusion.**  There is a
half-size subset of `GF(16)` whose `3`-tuple count is generic at every admissible
coefficient vector and whose `5`-tuple count is not. -/
theorem exists_generic_three_not_five :
    ∃ S : Finset K16, S.card = 2 ^ (4 - 1) ∧
      (∀ c ∈ coeffFamily K16 3, mCount 3 S c = 2 ^ ((3 - 1) * 4 - 3)) ∧
      ∃ c ∈ coeffFamily K16 5, mCount 5 S c ≠ 2 ^ ((5 - 1) * 4 - 5) :=
  ⟨Ssep, Ssep_card, Ssep_mCount3_generic, csep, csep_mem, Ssep_mCount5_ne_generic⟩

#print axioms exists_generic_three_not_five

end MTuple
