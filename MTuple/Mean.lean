import MTuple.Count

/-!
# The mean identity

Summing the phase over the whole admissible family `coeffFamily K m` reduces —
by Fourier inversion — to the `m`-th moment of

  `g(u) = ∑_{c ≠ 0} T̂_S(c) χ(u c) = |K|·1_S(u) − |S|`,

which for a half-size set takes exactly the two values `±2^{n−1}`, each on
`2^{n−1}` points.  Hence the moment is

  `2^{(n−1)(m+1)} · (1 + (−1)^m)`,

so it **vanishes for odd `m`** and is strictly positive for even `m`.  This is
the exact place where the parity of `m` enters.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The inverted transform `g(u) = ∑_{c ≠ 0} T̂_S(c) χ(uc) = |K|·1_S(u) − |S|`. -/
noncomputable def gfun (S : Finset K) (u : K) : ℤ :=
  (if u ∈ S then (Fintype.card K : ℤ) else 0) - S.card

/-- Fourier inversion: `∑_c T̂_S(c) χ(uc) = |K|·1_S(u)`. -/
theorem sum_Tsum_chiZ_univ (S : Finset K) (u : K) :
    ∑ c : K, Tsum S c * chiZ (u * c) = if u ∈ S then (Fintype.card K : ℤ) else 0 := by
  have h1 : ∀ c : K, Tsum S c * chiZ (u * c) = ∑ y ∈ S, chiZ (c * (y + u)) := by
    intro c
    rw [Tsum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by rw [mul_add, chiZ_add, mul_comm u c]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y ∈ S, ∑ c : K, chiZ (c * (y + u))
      = if y = u then (Fintype.card K : ℤ) else 0 := by
    intro y _
    rw [sum_chiZ_mul]
    congr 1
    exact propext CharTwo.add_eq_zero
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' S u]

/-- The nonzero-frequency form of the inversion. -/
theorem sum_Tsum_chiZ_erase (S : Finset K) (u : K) :
    ∑ c ∈ univ.erase (0 : K), Tsum S c * chiZ (u * c) = gfun S u := by
  have h := Finset.add_sum_erase (univ : Finset K) (fun c => Tsum S c * chiZ (u * c))
    (Finset.mem_univ (0 : K))
  rw [sum_Tsum_chiZ_univ] at h
  rw [gfun, ← h]
  simp [Tsum_zero, chiZ]

/-- The zero-sum-tuple moment: `|K| · ∑_{c admissible} ∏ᵢ T̂_S(cᵢ) = ∑_u g(u)^m`. -/
theorem card_mul_sum_prod_Tsum (m : ℕ) (S : Finset K) :
    (Fintype.card K : ℤ) * ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i)
      = ∑ u : K, (gfun S u) ^ m := by
  have hp : ∀ x : ℤ, x ^ m = ∏ _i : Fin m, x := by intro x; simp
  have key : ∀ u : K, (gfun S u) ^ m
      = ∑ c ∈ Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K)),
          (∏ i, Tsum S (c i)) * chiZ (u * ∑ i, c i) := by
    intro u
    rw [← sum_Tsum_chiZ_erase S u, hp, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, chiZ_sum, ← Finset.prod_mul_distrib]
  simp_rw [key]
  rw [Finset.sum_comm]
  have h2 : ∀ c ∈ Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K)),
      ∑ u : K, (∏ i, Tsum S (c i)) * chiZ (u * ∑ i, c i)
        = if (∑ i, c i) = 0 then (Fintype.card K : ℤ) * ∏ i, Tsum S (c i) else 0 := by
    intro c _
    rw [← Finset.mul_sum, sum_chiZ_mul]
    split <;> simp [mul_comm]
  rw [Finset.sum_congr rfl h2, coeffFamily, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split <;> simp

omit [Field K] [CharP K 2] in
/-- The `m`-th moment of `g` for a half-size set. -/
theorem sum_gfun_pow {n m : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) :
    ∑ u : K, (gfun S u) ^ m
      = (2 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ (n - 1)) ^ m * (1 + (-1) ^ m) := by
  have hsplit : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hsplitN : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hg1 : ∀ u ∈ S, (gfun S u) ^ m = ((2 : ℤ) ^ (n - 1)) ^ m := by
    intro u hu
    rw [gfun, if_pos hu, hcard, hS]
    push_cast
    rw [hsplit]
    ring_nf
  have hg2 : ∀ u ∈ univ \ S, (gfun S u) ^ m = (-1) ^ m * ((2 : ℤ) ^ (n - 1)) ^ m := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    rw [gfun, if_neg hu.2, hS]
    push_cast
    rw [← mul_pow]
    ring_nf
  have hcompl : (univ \ S).card = 2 ^ (n - 1) := by
    rw [Finset.card_univ_diff, hcard, hS, hsplitN]
    omega
  rw [← Finset.sum_sdiff (Finset.subset_univ S), Finset.sum_congr rfl hg1,
    Finset.sum_congr rfl hg2, Finset.sum_const, Finset.sum_const, hcompl, hS]
  ring

/-- The sum of the phases over the admissible family, in terms of the moment. -/
theorem sum_mPhase_eq (m : ℕ) (S : Finset K) :
    ∑ c ∈ coeffFamily K m, mPhase m S c
      = ((Fintype.card K : ℤ) - 1) * ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i) := by
  simp_rw [mPhase]
  rw [Finset.sum_comm]
  have key : ∀ t ∈ univ.erase (0 : K),
      ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (t * c i)
        = ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i) := by
    intro t ht
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    refine Finset.sum_nbij' (fun c => fun i => t * c i) (fun c => fun i => t⁻¹ * c i)
      ?_ ?_ ?_ ?_ ?_
    · intro c hc
      rw [mem_coeffFamily] at hc ⊢
      exact ⟨fun i => mul_ne_zero ht0 (hc.1 i), by rw [← Finset.mul_sum, hc.2, mul_zero]⟩
    · intro c hc
      rw [mem_coeffFamily] at hc ⊢
      exact ⟨fun i => mul_ne_zero (inv_ne_zero ht0) (hc.1 i), by
        rw [← Finset.mul_sum, hc.2, mul_zero]⟩
    · intro c _; funext i; field_simp
    · intro c _; funext i; field_simp
    · intro c _; rfl
  have hc1 : ((Fintype.card K - 1 : ℕ) : ℤ) = (Fintype.card K : ℤ) - 1 := by
    have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
    push_cast [Nat.cast_sub h1]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, nsmul_eq_mul, hc1]

/-! ## Odd `m`: the mean vanishes -/

/-- For a half-size set the moment vanishes when `m` is odd. -/
theorem sum_prod_Tsum_eq_zero {n m : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Odd m) :
    ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i) = 0 := by
  have h := card_mul_sum_prod_Tsum (K := K) m S
  rw [sum_gfun_pow hn S hcard hS, hm.neg_one_pow] at h
  simp only [add_neg_cancel, mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (card_pos_int (K := K)).ne'

/-- **Mean identity, odd `m`.**  `∑_{c admissible} Phase_m(c) = 0`. -/
theorem sum_mPhase_eq_zero {n m : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Odd m) :
    ∑ c ∈ coeffFamily K m, mPhase m S c = 0 := by
  rw [sum_mPhase_eq, sum_prod_Tsum_eq_zero hn S hcard hS hm, mul_zero]

/-- **Mean identity in deficiency form**: `∑_{c admissible} Deficiency_m(c) = 0`
for odd `m`. -/
theorem sum_mDeficiency_eq_zero {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Odd m) :
    ∑ c ∈ coeffFamily K m, mDeficiency n m S c = 0 := by
  have h : (Fintype.card K : ℤ) * ∑ c ∈ coeffFamily K m, mDeficiency n m S c
      = ∑ c ∈ coeffFamily K m, mPhase m S c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      card_mul_mDeficiency_eq_mPhase hn hm2 S hcard hS c
  rw [sum_mPhase_eq_zero (by omega) S hcard hS hm] at h
  exact (mul_eq_zero.1 h).resolve_left (card_pos_int (K := K)).ne'

/-! ## Even `m`: the mean is strictly positive -/

/-- For even `m` the moment is `2^{n+(n−1)m}`, not `0`. -/
theorem card_mul_sum_prod_Tsum_even {n m : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    (Fintype.card K : ℤ) * ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i)
      = 2 ^ (n + (n - 1) * m) := by
  rw [card_mul_sum_prod_Tsum, sum_gfun_pow hn S hcard hS, hm.neg_one_pow]
  rw [pow_add, ← pow_mul]
  have h2 : (2 : ℤ) ^ (n - 1) * 2 ^ ((n - 1) * m) * (1 + 1)
      = 2 ^ (n - 1) * 2 * 2 ^ ((n - 1) * m) := by ring
  rw [h2, ← pow_succ]
  congr 2
  omega

/-- **Even `m`: the phases have strictly positive sum over the admissible family.** -/
theorem sum_mPhase_pos {n m : ℕ} (hn : 2 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    0 < ∑ c ∈ coeffFamily K m, mPhase m S c := by
  have hcpos := card_pos_int (K := K)
  have hMpos : 0 < ∑ c ∈ coeffFamily K m, ∏ i, Tsum S (c i) := by
    have h := card_mul_sum_prod_Tsum_even (n := n) (m := m) (by omega) S hcard hS hm
    have hpow : (0 : ℤ) < 2 ^ (n + (n - 1) * m) := by positivity
    nlinarith
  have hK2 : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by
    rw [hcard]
    have : (2 : ℤ) ^ 1 ≤ 2 ^ n := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    simpa using this
  rw [sum_mPhase_eq]
  have : (0 : ℤ) < (Fintype.card K : ℤ) - 1 := by linarith
  exact mul_pos this hMpos

/-- **Even `m`: the deficiencies have strictly positive mean.** -/
theorem sum_mDeficiency_pos {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    0 < ∑ c ∈ coeffFamily K m, mDeficiency n m S c := by
  have hcpos := card_pos_int (K := K)
  have hphase := sum_mPhase_pos hn S hcard hS hm
  have h : (Fintype.card K : ℤ) * ∑ c ∈ coeffFamily K m, mDeficiency n m S c
      = ∑ c ∈ coeffFamily K m, mPhase m S c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      card_mul_mDeficiency_eq_mPhase hn hm2 S hcard hS c
  nlinarith

end MTuple
