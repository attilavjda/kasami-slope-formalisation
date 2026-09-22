import MTuple.Count

/-!
# Scaling invariance of the `m`-tuple count

The count `mCount m S c` only depends on the coefficient vector `c` up to a
nonzero scalar, because `∑ᵢ (λcᵢ)xᵢ = λ·∑ᵢ cᵢxᵢ`.  At `m = 3` this reduces the
admissible family to the one-parameter family `(1, ρ, 1+ρ)`, `ρ ∉ {0,1}` — the
"slope" normalisation used in the literature on the Kasami statement — which is
what makes an exhaustive machine check of the `m = 3` conclusion cheap in
`MTuple/MTupleExt/SeparationGF16.lean`.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

omit [Fintype K] [CharP K 2] in
/-- **The count is invariant under scaling the coefficient vector.** -/
theorem mCount_smul {m : ℕ} (S : Finset K) (c : Fin m → K) {l : K} (hl : l ≠ 0) :
    mCount m S (fun i => l * c i) = mCount m S c := by
  unfold mCount
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  have hrw : ∑ i, l * c i * x i = l * ∑ i, c i * x i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hrw, mul_eq_zero, hl, false_or]

/-- Every admissible `3`-vector is a scalar multiple of `(1, ρ, 1+ρ)` with
`ρ = c₁/c₀ ∉ {0, 1}`. -/
theorem coeff_three_eq_smul {c : Fin 3 → K} (hc : c ∈ coeffFamily K 3) :
    c = (fun i => c 0 * (![1, c 1 / c 0, 1 + c 1 / c 0] : Fin 3 → K) i) := by
  rw [mem_coeffFamily] at hc
  have h0 : c 0 ≠ 0 := hc.1 0
  have hsum := hc.2
  rw [Fin.sum_univ_three] at hsum
  have h2 : c 2 = c 0 + c 1 := (CharTwo.add_eq_zero.1 hsum).symm
  funext i
  fin_cases i
  · simp
  · simp
    field_simp
  · simp
    rw [h2]
    field_simp

/-- The slope `ρ = c₁/c₀` of an admissible `3`-vector is neither `0` nor `1`. -/
theorem coeff_three_ratio_ne {c : Fin 3 → K} (hc : c ∈ coeffFamily K 3) :
    c 1 / c 0 ≠ 0 ∧ c 1 / c 0 ≠ 1 := by
  rw [mem_coeffFamily] at hc
  have h0 : c 0 ≠ 0 := hc.1 0
  have h1 : c 1 ≠ 0 := hc.1 1
  have h2 : c 2 ≠ 0 := hc.1 2
  have hsum := hc.2
  rw [Fin.sum_univ_three] at hsum
  refine ⟨div_ne_zero h1 h0, fun h => ?_⟩
  have : c 1 = c 0 := by
    field_simp at h
    exact h
  apply h2
  have hc2 : c 2 = c 0 + c 1 := (CharTwo.add_eq_zero.1 hsum).symm
  rw [hc2, this, CharTwo.add_self_eq_zero]

/-- **Slope normalisation of the `3`-tuple count.**  The count at an admissible
`c` equals the count at `(1, ρ, 1+ρ)` with `ρ = c₁/c₀`. -/
theorem mCount_three_normalise (S : Finset K) {c : Fin 3 → K} (hc : c ∈ coeffFamily K 3) :
    mCount 3 S c = mCount 3 S ![1, c 1 / c 0, 1 + c 1 / c 0] := by
  have h0 : c 0 ≠ 0 := by
    rw [mem_coeffFamily] at hc
    exact hc.1 0
  conv_lhs => rw [coeff_three_eq_smul hc]
  exact mCount_smul S _ h0

end MTuple
