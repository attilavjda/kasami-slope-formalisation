import MTuple.Counterexample
import MTuple.Gold
import MTuple.Kasami
import MTuple.Comparison
import MTuple.Rigidity
import MTuple.Sharpness

/-!
# Verification

Three independent checks on the library.

* **An explicit computation at `m = 2`.**  For the admissible pair `(a, a)` the
  count is `|S| = 2^{n−1}`, strictly larger than the generic `2^{n−2}` — the
  even-`m` obstruction, by hand, at the smallest even tuple length.
* **A concrete carrier.**  The main theorems are instantiated at
  `K = GF(2ⁿ)`, where the admissible family is nonempty.
* **Axioms.**  `#print axioms` on every headline result.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## The explicit case `m = 2` -/

omit [Fintype K] in
/-- At tuple length `2` and admissible coefficients `(a, a)`, the solutions of
`a x₀ + a x₁ = 0` in `S²` are exactly the diagonal, so the count is `|S|`. -/
theorem mCount_two_diagonal (S : Finset K) (a : K) (ha : a ≠ 0) :
    mCount 2 S ![a, a] = S.card := by
  classical
  refine Finset.card_nbij' (fun x => x 0) (fun y => ![y, y]) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
    exact hx.1 0
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    refine ⟨fun i => by fin_cases i <;> simpa using hy, ?_⟩
    simp [Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
    have hsum : a * x 0 + a * x 1 = 0 := by
      have := hx.2
      simpa [Fin.sum_univ_two] using this
    have hx01 : x 0 = x 1 := by
      have : a * (x 0 + x 1) = 0 := by linear_combination hsum
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha
      · exact CharTwo.add_eq_zero.1 h
    funext i
    fin_cases i <;> simp [hx01]
  · intro y _
    simp

omit [Fintype K] in
/-- **The even-`m` obstruction, witnessed explicitly at `m = 2`:** the count
`2^{n−1}` strictly exceeds the generic value `2^{(2−1)n−2} = 2^{n−2}`. -/
theorem mCount_two_gt_generic {n : ℕ} (hn : 2 ≤ n) (S : Finset K) (a : K) (ha : a ≠ 0)
    (hS : S.card = 2 ^ (n - 1)) :
    2 ^ ((2 - 1) * n - 2) < mCount 2 S ![a, a] := by
  rw [mCount_two_diagonal S a ha, hS]
  have : (2 - 1) * n - 2 = n - 2 := by omega
  rw [this]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The pair `(a, a)` is indeed admissible. -/
theorem coeff_two_mem (a : K) (ha : a ≠ 0) : ![a, a] ∈ coeffFamily K 2 := by
  rw [mem_coeffFamily]
  refine ⟨fun i => by fin_cases i <;> simpa using ha, ?_⟩
  simp [Fin.sum_univ_two, CharTwo.add_self_eq_zero]

/-! ## A concrete carrier: `K = GF(2ⁿ)` -/

section Galois

noncomputable local instance galoisFintype (n : ℕ) [NeZero n] : Fintype (GaloisField 2 n) :=
  Fintype.ofFinite _

noncomputable local instance galoisDecEq (n : ℕ) : DecidableEq (GaloisField 2 n) :=
  Classical.decEq _

theorem galoisField_card (n : ℕ) [NeZero n] : Fintype.card (GaloisField 2 n) = 2 ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 n (NeZero.ne n)

/-- **The odd-`m` theorem over `GF(2ⁿ)`.** -/
theorem galois_mTupleCount_odd (n : ℕ) [NeZero n] (m : ℕ) (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hm : Odd m) (S : Finset (GaloisField 2 n)) (hS : S.card = 2 ^ (n - 1))
    (hpos : ∀ c ∈ coeffFamily (GaloisField 2 n) m, 0 ≤ mPhase m S c) :
    ∀ c ∈ coeffFamily (GaloisField 2 n) m, mCount m S c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm S (galoisField_card n) hS hpos

/-- **The even-`m` obstruction over `GF(2ⁿ)`.** -/
theorem galois_exists_mCount_gt_generic (n : ℕ) [NeZero n] (m : ℕ) (hn : 2 ≤ n) (hm2 : 2 ≤ m)
    (hm : Even m) (S : Finset (GaloisField 2 n)) (hS : S.card = 2 ^ (n - 1)) :
    ∃ c ∈ coeffFamily (GaloisField 2 n) m, 2 ^ ((m - 1) * n - m) < mCount m S c :=
  exists_mCount_gt_generic hn hm2 S (galoisField_card n) hS hm

/-- **Non-vacuity over `GF(2ⁿ)`**: the admissible family is nonempty. -/
theorem galois_coeffFamily_nonempty (n : ℕ) [NeZero n] (m : ℕ) (hn : 2 ≤ n) (hm2 : 2 ≤ m) :
    (coeffFamily (GaloisField 2 n) m).Nonempty := by
  refine coeffFamily_nonempty hm2 ?_
  rw [galoisField_card n]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end Galois

/-! ## Axioms of the headline results -/

#print axioms mCount_generic_of_mPhase_eq_zero
#print axioms mTupleCount_odd_of_mPhase_nonneg
#print axioms not_forall_mCount_generic_even
#print axioms mCount_const_gt_generic_even
#print axioms mCount_univ_ne_generic
#print axioms coeffFamily_nonempty
#print axioms mTupleCount_odd_traceHyperplane
#print axioms sign_factorization_iff_affine_trace_hyperplane
#print axioms apn_derivImage_eq_half
#print axioms cube_mCount_generic_odd
#print axioms kasamiTripleConjecture_of_mod_pm_one
#print axioms exists_mPhase_neg
#print axioms kca_coefficientTripleCount_of_mod_pm_one

end MTuple
