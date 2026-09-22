import MTuple.APN
import MTuple.SignFactorization

/-!
# The Gold maps: an unconditional instance

For `k : ℕ` the *Gold map* is `G_k(x) = x^{2^k+1}`.  Its derivative

`G_k(x+a) + G_k(x) = (a x^{2^k} + a^{2^k} x) + a^{2^k+1}`

is an `𝔽₂`-linear map plus a constant (`gold_deriv`), so the derivative image
`Δ_a G_k` is a **coset of an additive subgroup** (`derivImage_gold`).  By
`MTuple.mPhase_coset_nonneg` its phase is therefore non-negative at every
admissible coefficient vector — the hypothesis of the odd-`m` theorem is *proved*
rather than assumed (`gold_mPhase_nonneg`).

For `k = 1` (the cube map `x³`, which is APN over every field of characteristic
`2`) the half-size hypothesis is also automatic, giving a completely
unconditional statement: `cube_mCount_generic_odd`.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## The Gold map and its derivative -/

/-- The Gold map `G_k(x) = x^{2^k+1}`. -/
def gold (k : ℕ) (x : K) : K := x ^ (2 ^ k + 1)

/-- The `𝔽₂`-linear part `L_{k,a}(x) = a x^{2^k} + a^{2^k} x` of the derivative. -/
def goldLin (k : ℕ) (a x : K) : K := a * x ^ (2 ^ k) + a ^ (2 ^ k) * x

/-- The image of `L_{k,a}`; an additive subgroup of `K` by `goldLinImage_add_mem`. -/
def goldLinImage (k : ℕ) (a : K) : Finset K := (univ : Finset K).image (goldLin k a)

omit [Fintype K] [DecidableEq K] in
/-- `G_k(x+a) + G_k(x) = L_{k,a}(x) + a^{2^k+1}`. -/
theorem gold_deriv (k : ℕ) (a x : K) :
    gold k (x + a) + gold k x = goldLin k a x + a ^ (2 ^ k + 1) := by
  have hfrob : (x + a) ^ (2 ^ k) = x ^ (2 ^ k) + a ^ (2 ^ k) :=
    add_pow_char_pow (p := 2) (n := k) x a
  unfold gold goldLin
  rw [pow_succ, pow_succ, pow_succ, hfrob]
  linear_combination (x ^ (2 ^ k) * x) * CharTwo.two_eq_zero (R := K)

omit [Fintype K] [DecidableEq K] in
theorem goldLin_add (k : ℕ) (a x y : K) :
    goldLin k a (x + y) = goldLin k a x + goldLin k a y := by
  have hfrob : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
    add_pow_char_pow (p := 2) (n := k) x y
  unfold goldLin
  rw [hfrob]
  ring

theorem goldLinImage_add_mem (k : ℕ) (a : K) :
    ∀ x ∈ goldLinImage k a, ∀ y ∈ goldLinImage k a, x + y ∈ goldLinImage k a := by
  intro x hx y hy
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hy
  exact Finset.mem_image.2 ⟨u + v, Finset.mem_univ _, goldLin_add k a u v⟩

/-- **The Gold derivative image is a coset**: `Δ_a G_k = L_{k,a}(K) + a^{2^k+1}`. -/
theorem derivImage_gold (k : ℕ) (a : K) :
    derivImage (gold k : K → K) a
      = (goldLinImage k a).image (fun v => v + a ^ (2 ^ k + 1)) := by
  rw [derivImage, goldLinImage, Finset.image_image]
  exact Finset.image_congr fun x _ => gold_deriv k a x

/-! ## The phase hypothesis is satisfied, unconditionally -/

/-- **The phase on a Gold derivative image is non-negative** at every admissible
coefficient vector, for every tuple length. -/
theorem gold_mPhase_nonneg {m : ℕ} (k : ℕ) (a : K) {c : Fin m → K}
    (hc : c ∈ coeffFamily K m) :
    0 ≤ mPhase m (derivImage (gold k : K → K) a) c := by
  rw [derivImage_gold]
  exact mPhase_coset_nonneg _ (goldLinImage_add_mem k a) _ hc

/-- **The generic count on a half-size Gold derivative image, odd `m`.**  No
positivity hypothesis is assumed: it is proved. -/
theorem gold_mCount_generic_odd {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (hcard : Fintype.card K = 2 ^ n) (k : ℕ) (a : K)
    (hS : (derivImage (gold k : K → K) a).card = 2 ^ (n - 1)) :
    ∀ c ∈ coeffFamily K m,
      mCount m (derivImage (gold k : K → K) a) c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm _ hcard hS (fun _ hc => gold_mPhase_nonneg k a hc)

/-! ## The cube map: half-size comes for free -/

omit [Fintype K] [DecidableEq K] in
/-- Two points with the same cube-derivative value differ by `0` or `a`. -/
theorem cube_deriv_eq_imp {a : K} (ha : a ≠ 0) {x y : K}
    (h : gold 1 (y + a) + gold 1 y = gold 1 (x + a) + gold 1 x) : y = x ∨ y = x + a := by
  have hy' : a * y ^ 2 + a ^ 2 * y = a * x ^ 2 + a ^ 2 * x := by
    have h1 := gold_deriv 1 a y
    have h2 := gold_deriv 1 a x
    rw [h1, h2] at h
    simpa [goldLin] using add_right_cancel h
  have hfac : a * ((y + x) * ((y + x) + a)) = 0 := by
    linear_combination hy' + (a * x ^ 2 + a ^ 2 * x + a * y * x) * (CharTwo.two_eq_zero (R := K))
  have h1 : (y + x) * ((y + x) + a) = 0 := (mul_eq_zero.1 hfac).resolve_left ha
  rcases mul_eq_zero.1 h1 with hc | hc
  · exact Or.inl (CharTwo.add_eq_zero.1 hc)
  · refine Or.inr ?_
    have hyx : y + x = a := CharTwo.add_eq_zero.1 hc
    calc y = (y + x) + x := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = a + x := by rw [hyx]
      _ = x + a := add_comm _ _

/-- **The cube map `x ↦ x³` is APN** over every finite field of characteristic
`2`. -/
theorem cube_isAPN : IsAPN (gold 1 : K → K) := by
  intro a b ha
  by_cases hne : ((univ : Finset K).filter (fun x => gold 1 (x + a) + gold 1 x = b)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    rw [Finset.mem_filter] at hx0
    have hsub : (univ : Finset K).filter (fun x => gold 1 (x + a) + gold 1 x = b) ⊆
        {x0, x0 + a} := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have h : gold 1 (y + a) + gold 1 y = gold 1 (x0 + a) + gold 1 x0 := by rw [hy.2, hx0.2]
      rcases cube_deriv_eq_imp ha h with hc | hc <;> simp [hc]
    calc ((univ : Finset K).filter (fun x => gold 1 (x + a) + gold 1 x = b)).card
        ≤ ({x0, x0 + a} : Finset K).card := Finset.card_le_card hsub
      _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- The cube derivative image is half-size, for every nonzero direction. -/
theorem card_derivImage_cube {n : ℕ} (hcard : Fintype.card K = 2 ^ n) {a : K} (ha : a ≠ 0) :
    (derivImage (gold 1 : K → K) a).card = 2 ^ (n - 1) :=
  apn_derivImage_eq_half _ cube_isAPN a ha n hcard

/-- **Unconditional instance of the odd-`m` theorem.**  On the derivative image of
the cube map, at every admissible coefficient vector, the `m`-tuple count is the
generic `2^{(m−1)n−m}` — nothing is assumed beyond `n ≥ 2`, `m ≥ 3` odd and
`a ≠ 0`. -/
theorem cube_mCount_generic_odd {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (hcard : Fintype.card K = 2 ^ n) {a : K} (ha : a ≠ 0) :
    ∀ c ∈ coeffFamily K m,
      mCount m (derivImage (gold 1 : K → K) a) c = 2 ^ ((m - 1) * n - m) :=
  gold_mCount_generic_odd hn hm3 hm hcard 1 a (card_derivImage_cube hcard ha)

/-- **Even `m`: the count on the cube derivative image is non-generic somewhere.** -/
theorem cube_exists_mCount_gt_generic {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (hm : Even m)
    (hcard : Fintype.card K = 2 ^ n) {a : K} (ha : a ≠ 0) :
    ∃ c ∈ coeffFamily K m,
      2 ^ ((m - 1) * n - m) < mCount m (derivImage (gold 1 : K → K) a) c :=
  apn_exists_mCount_gt_generic_even hn hm2 hm hcard _ cube_isAPN a ha

end MTuple
