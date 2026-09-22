import MTuple.Generic

/-!
# Sharpness: the hypotheses are load-bearing

Two refinements of the negative results.

* **Even `m` fails pointwise.**  For a half-size `S` and even `m ≥ 2` the count
  at *every* constant admissible vector `(a, …, a)`, `a ≠ 0`, strictly exceeds
  the generic value (`mCount_const_gt_generic_even`).  This upgrades
  `exists_mCount_gt_generic`, which only produces some bad vector.

* **Half-size is load-bearing.**  For `S = K` — not half-size — every admissible
  phase vanishes, yet the count is `|K|^{m−1}`, never the generic value
  (`mCount_univ_ne_generic`).  So `|S| = 2^{n−1}` cannot be dropped or absorbed
  into a normalisation.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## Even `m`: the constant vectors all exceed the generic count -/

/-- For even `m` the constant vector `(a, …, a)` with `a ≠ 0` is admissible. -/
theorem const_mem_coeffFamily {m : ℕ} (hm : Even m) {a : K} (ha : a ≠ 0) :
    (fun _ : Fin m => a) ∈ coeffFamily K m := by
  rw [mem_coeffFamily]
  refine ⟨fun _ => ha, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [(CharP.cast_eq_zero_iff K 2 m).2 hm.two_dvd, zero_mul]

/-- The phase at a constant vector is the `m`-th moment of the transform over the
nonzero frequencies: `P_m(a, …, a) = ∑_{u ≠ 0} T̂_S(u)^m`. -/
theorem mPhase_const_eq {m : ℕ} (S : Finset K) {a : K} (ha : a ≠ 0) :
    mPhase m S (fun _ => a) = ∑ u ∈ univ.erase (0 : K), (Tsum S u) ^ m := by
  rw [mPhase]
  refine Finset.sum_nbij' (fun t => t * a) (fun u => u * a⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_erase.2 ⟨mul_ne_zero (Finset.ne_of_mem_erase ht) ha, Finset.mem_univ _⟩
  · intro u hu
    exact Finset.mem_erase.2
      ⟨mul_ne_zero (Finset.ne_of_mem_erase hu) (inv_ne_zero ha), Finset.mem_univ _⟩
  · intro t _; field_simp
  · intro u _; field_simp
  · intro t _; simp

/-- A half-size set has a nonzero Fourier coefficient at some nonzero frequency.
(Otherwise its indicator would be constant.) -/
theorem exists_Tsum_ne_zero {n : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) :
    ∃ u ≠ (0 : K), Tsum S u ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  -- `S` is nonempty, so pick `y ∈ S`; the inverted transform at `y` is `|K| − |S| ≠ 0`.
  have hSpos : 0 < S.card := by rw [hS]; positivity
  obtain ⟨y, hy⟩ := Finset.card_pos.1 hSpos
  have hzero : gfun S y = 0 := by
    rw [← sum_Tsum_chiZ_erase S y]
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [hcon c (Finset.ne_of_mem_erase hc), zero_mul]
  rw [gfun, if_pos hy, hcard, hS] at hzero
  have hsplit : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  push_cast at hzero
  rw [hsplit] at hzero
  linarith

/-- **Even `m`: the phase is strictly positive at every constant admissible
vector.** -/
theorem mPhase_const_pos_even {n m : ℕ} (hn : 1 ≤ n) (hm : Even m) (hm0 : m ≠ 0)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    {a : K} (ha : a ≠ 0) :
    0 < mPhase m S (fun _ => a) := by
  obtain ⟨u, hu0, hu⟩ := exists_Tsum_ne_zero hn S hcard hS
  rw [mPhase_const_eq S ha]
  refine Finset.sum_pos' (fun v _ => hm.pow_nonneg _) ⟨u, ?_, ?_⟩
  · exact Finset.mem_erase.2 ⟨hu0, Finset.mem_univ _⟩
  · exact lt_of_le_of_ne (hm.pow_nonneg _) (Ne.symm (pow_ne_zero_iff hm0 |>.2 hu))

/-- **Even `m` fails pointwise, at every constant admissible vector.**  For a
half-size `S`, an even `m ≥ 2` and *every* `a ≠ 0`, the count at `(a, …, a)`
strictly exceeds the generic value `2^{(m−1)n−m}`.

This is the pointwise strengthening of `exists_mCount_gt_generic`, which only
produces *some* bad admissible vector out of the strictly positive mean. -/
theorem mCount_const_gt_generic_even {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (hm : Even m)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    {a : K} (ha : a ≠ 0) :
    2 ^ ((m - 1) * n - m) < mCount m S (fun _ => a) := by
  have hphase := mPhase_const_pos_even (by omega) hm (by omega) S hcard hS ha
  have hbridge := card_mul_mDeficiency_eq_mPhase hn hm2 S hcard hS (fun _ => a)
  have hcpos := card_pos_int (K := K)
  have hd : 0 < mDeficiency n m S (fun _ => a) := by nlinarith
  rw [mDeficiency, sub_pos] at hd
  exact_mod_cast hd

/-- **Even `m`: no half-size set is generic at any constant admissible vector.**
The negative statement, in the form "for every `a ≠ 0` the count differs from the
generic value". -/
theorem not_mCount_const_generic_even {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (hm : Even m)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    {a : K} (ha : a ≠ 0) :
    mCount m S (fun _ => a) ≠ 2 ^ ((m - 1) * n - m) :=
  (mCount_const_gt_generic_even hn hm2 hm S hcard hS ha).ne'

/-! ## Half-size is load-bearing: the counterexample `S = K` -/

/-- For `S = K` every admissible phase vanishes (the transform is supported at
the zero frequency). -/
theorem mPhase_univ_eq_zero {m : ℕ} (hm : 0 < m) {c : Fin m → K}
    (hc : c ∈ coeffFamily K m) :
    mPhase m (univ : Finset K) c = 0 := by
  rw [mem_coeffFamily] at hc
  refine Finset.sum_eq_zero fun t ht => ?_
  have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
  have hi : (⟨0, hm⟩ : Fin m) ∈ (univ : Finset (Fin m)) := Finset.mem_univ _
  refine Finset.prod_eq_zero hi ?_
  have hne : t * c ⟨0, hm⟩ ≠ 0 := mul_ne_zero ht0 (hc.1 _)
  rw [Tsum]
  have : ∑ y : K, chiZ (t * c ⟨0, hm⟩ * y) = ∑ y : K, chiZ (y * (t * c ⟨0, hm⟩)) :=
    Finset.sum_congr rfl fun y _ => by rw [mul_comm]
  rw [show (univ : Finset K) = Finset.univ from rfl, this, sum_chiZ_mul, if_neg hne]

/-- For `S = K` the count at an admissible vector is `|K|^{m−1}`. -/
theorem mCount_univ {m : ℕ} (hm : 0 < m) {c : Fin m → K} (hc : c ∈ coeffFamily K m) :
    mCount m (univ : Finset K) c = Fintype.card K ^ (m - 1) := by
  have hkey := card_mul_mCount m (univ : Finset K) c
  have hsplit : ∑ t : K, ∏ i, Tsum (univ : Finset K) (t * c i)
      = (∏ i, Tsum (univ : Finset K) ((0 : K) * c i)) + mPhase m (univ : Finset K) c :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))).symm
  rw [mPhase_univ_eq_zero hm hc, add_zero] at hsplit
  have hzero : (∏ i, Tsum (univ : Finset K) ((0 : K) * c i)) = (Fintype.card K : ℤ) ^ m := by
    simp [Tsum_zero, Finset.card_univ]
  rw [hsplit, hzero] at hkey
  have hpow : (Fintype.card K : ℤ) ^ m
      = (Fintype.card K : ℤ) * (Fintype.card K : ℤ) ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hkey
  have := mul_left_cancel₀ (card_pos_int (K := K)).ne' hkey
  exact_mod_cast this

/-- **Half-size is load-bearing.**  Taking `S = K` — which is *not* half-size —
makes every admissible phase vanish, yet the count is `|K|^{m−1} = 2^{nm−n}`,
never the generic `2^{(m−1)n−m}`.  So the hypothesis `|S| = 2^{n−1}` in every
theorem of the development cannot be weakened to "`S ⊆ K`", nor absorbed into a
normalisation: it is what makes the dictionary `|K|·D_m(c) = P_m(c)` true. -/
theorem mCount_univ_ne_generic {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) {c : Fin m → K} (hc : c ∈ coeffFamily K m) :
    mCount m (univ : Finset K) c ≠ 2 ^ ((m - 1) * n - m) := by
  rw [mCount_univ (by omega) hc, hcard, ← pow_mul]
  have hcomm : (m - 1) * n = n * (m - 1) := mul_comm _ _
  have h1 : 1 ≤ n * (m - 1) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hlt : (m - 1) * n - m < n * (m - 1) := by omega
  exact (Nat.pow_lt_pow_right (by norm_num) hlt).ne'

end MTuple
