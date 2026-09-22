import MTuple.Admissible

/-!
# The `m`-tuple count, phase and deficiency

For a finite field `K` of characteristic `2` with `|K| = 2ⁿ`, a subset
`S ⊆ K`, and a coefficient vector `c : Fin m → K` we define

* `mCount m S c = #{x ∈ Sᵐ : ∑ᵢ cᵢ xᵢ = 0}`,
* `mPhase m S c = ∑_{t ≠ 0} ∏ᵢ T̂_S(t cᵢ)`,
* `mDeficiency n m S c = mCount m S c − 2^{(m−1)n−m}`.

The two results of this file are the **Fourier identity**

  `|K| · mCount m S c = ∑_t ∏ᵢ T̂_S(t cᵢ)`   (`card_mul_mCount`)

and its half-size normalisation

  `|K| · mDeficiency n m S c = mPhase m S c` (`card_mul_mDeficiency_eq_mPhase`),

which is the exact translation between the counting problem and the phase sum.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The `m`-tuple count `#{x ∈ Sᵐ : ∑ᵢ cᵢ xᵢ = 0}`. -/
def mCount (m : ℕ) (S : Finset K) (c : Fin m → K) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin m => S)).filter (fun x => ∑ i, c i * x i = 0)).card

/-- The `m`-phase sum `∑_{t ≠ 0} ∏ᵢ T̂_S(t cᵢ)`. -/
noncomputable def mPhase (m : ℕ) (S : Finset K) (c : Fin m → K) : ℤ :=
  ∑ t ∈ univ.erase (0 : K), ∏ i, Tsum S (t * c i)

/-- The `m`-tuple deficiency: the deviation of the count from the generic value
`2^{(m−1)n−m}`. -/
def mDeficiency (n m : ℕ) (S : Finset K) (c : Fin m → K) : ℤ :=
  (mCount m S c : ℤ) - 2 ^ ((m - 1) * n - m)

/-- **The Fourier identity for `m`-tuples.**
`|K| · #{x ∈ Sᵐ : ∑ᵢ cᵢxᵢ = 0} = ∑_t ∏ᵢ T̂_S(t cᵢ)`. -/
theorem card_mul_mCount (m : ℕ) (S : Finset K) (c : Fin m → K) :
    (Fintype.card K : ℤ) * (mCount m S c : ℤ) = ∑ t : K, ∏ i, Tsum S (t * c i) := by
  have key : ∀ t : K, ∏ i, Tsum S (t * c i)
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin m => S), chiZ (t * ∑ i, c i * x i) := by
    intro t
    have hT : ∀ i : Fin m, Tsum S (t * c i) = ∑ y ∈ S, chiZ (t * c i * y) := fun _ => rfl
    simp_rw [hT]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, chiZ_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_assoc]
  simp_rw [key]
  rw [Finset.sum_comm]
  have h2 : ∀ x ∈ Fintype.piFinset (fun _ : Fin m => S),
      ∑ t : K, chiZ (t * ∑ i, c i * x i)
        = if (∑ i, c i * x i) = 0 then (Fintype.card K : ℤ) else 0 :=
    fun x _ => sum_chiZ_mul _
  rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp [mCount, mul_comm]

/-- The exponent bookkeeping `n + ((m−1)n − m) = (n−1)m`. -/
theorem exp_arith {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    n + ((m - 1) * n - m) = (n - 1) * m := by
  have e1 : (m - 1) * n = m * n - n := by rw [Nat.sub_one_mul]
  have e2 : (n - 1) * m = n * m - m := by rw [Nat.sub_one_mul]
  have e3 : m * n = n * m := mul_comm m n
  have hge : m + n ≤ m * n := by nlinarith
  omega

/-- **`|K| · Deficiency_m(c) = Phase_m(c)`** for a half-size set `S`. -/
theorem card_mul_mDeficiency_eq_mPhase {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    (c : Fin m → K) :
    (Fintype.card K : ℤ) * mDeficiency n m S c = mPhase m S c := by
  have hsplit : ∑ t : K, ∏ i, Tsum S (t * c i)
      = (∏ i, Tsum S ((0 : K) * c i)) + mPhase m S c :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))).symm
  have hzero : (∏ i, Tsum S ((0 : K) * c i)) = (S.card : ℤ) ^ m := by
    simp [Tsum_zero]
  have hpow : (Fintype.card K : ℤ) * 2 ^ ((m - 1) * n - m) = (S.card : ℤ) ^ m := by
    rw [hcard, hS]
    push_cast
    rw [← pow_add, ← pow_mul, exp_arith hn hm]
  rw [mDeficiency, mul_sub, card_mul_mCount, hsplit, hzero, hpow]
  ring

end MTuple
