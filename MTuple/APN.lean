import MTuple.Generic

/-!
# APN maps: the derivative image is automatically half-size

The *derivative* of `f : K → K` in the direction `a` is `D_a f (x) = f(x+a)+f(x)`
and `Δ_a f = { D_a f (x) : x ∈ K }` is its image (`derivImage`).  `f` is
**almost perfect nonlinear** when every equation `D_a f (x) = b` with `a ≠ 0` has
at most two solutions (`IsAPN`).

Since `D_a f (x+a) = D_a f (x)` and `x ≠ x+a`, every nonempty fibre has at least
two points, hence exactly two, hence `|Δ_a f| = 2^{n−1}`
(`apn_derivImage_eq_half`): the half-size hypothesis of the whole library holds
automatically on `Δ_a f`.  The three corollaries at the end are the main
theorems specialised to that set.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- `f` is almost perfect nonlinear: every derivative equation
`f (x + a) + f x = b` with `a ≠ 0` has at most two solutions. -/
def IsAPN (f : K → K) : Prop :=
  ∀ a b : K, a ≠ 0 → ((univ : Finset K).filter (fun x => f (x + a) + f x = b)).card ≤ 2

/-- The image `Δ_a f = { f (x + a) + f x : x ∈ K }` of the derivative of `f` in
the direction `a`. -/
def derivImage (f : K → K) (a : K) : Finset K :=
  (univ : Finset K).image (fun x => f (x + a) + f x)

/-- Every nonempty derivative fibre has at least two points: `x` and `x + a`. -/
theorem two_le_fiber_card (f : K → K) (a : K) (ha : a ≠ 0) {b : K}
    (hb : b ∈ derivImage f a) :
    2 ≤ ((univ : Finset K).filter (fun x => f (x + a) + f x = b)).card := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hb
  have hxa : f (x + a + a) + f (x + a) = b := by
    have h : x + a + a = x := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [h, add_comm]
    exact hx
  have hsub : ({x, x + a} : Finset K) ⊆
      (univ : Finset K).filter (fun x => f (x + a) + f x = b) := by
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · subst h; simpa using hx
    · rw [Finset.mem_singleton] at h; subst h; simpa using hxa
  have hne : x ≠ x + a := by
    intro h
    exact ha (by linear_combination -h)
  calc 2 = ({x, x + a} : Finset K).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Every nonempty derivative fibre of an APN map has exactly two points. -/
theorem fiber_card_eq_two (f : K → K) (hf : IsAPN f) (a : K) (ha : a ≠ 0) {b : K}
    (hb : b ∈ derivImage f a) :
    ((univ : Finset K).filter (fun x => f (x + a) + f x = b)).card = 2 :=
  le_antisymm (hf a b ha) (two_le_fiber_card f a ha hb)

/-- **The derivative image of an APN map has exactly `2ⁿ⁻¹` elements.** -/
theorem apn_derivImage_eq_half (f : K → K) (hf : IsAPN f) (a : K) (ha : a ≠ 0)
    (n : ℕ) (hcard : Fintype.card K = 2 ^ n) :
    (derivImage f a).card = 2 ^ (n - 1) := by
  have hsum : Fintype.card K = 2 * (derivImage f a).card := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_image (fun x : K => f (x + a) + f x) univ]
    rw [show ((univ : Finset K).image (fun x : K => f (x + a) + f x)) = derivImage f a from rfl,
      Finset.sum_congr rfl (fun b hb => fiber_card_eq_two f hf a ha hb),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have : Fintype.card K = 1 := by rw [hcard, hn0, pow_zero]
    have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
    omega
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hcard, hpow] at hsum
  omega


/-! ## The main theorems on a derivative image -/

/-- **APN + balance ⇒ the generic `m`-tuple count on the derivative image.**
This is the second FOL statement:
`∀n∀m∀f∀a∀c [ |K|=2ⁿ ∧ APN f ∧ a ≠ 0 ∧ 2 ≤ m ∧ (∀i, cᵢ ≠ 0) ∧ Bal → κ_m = 2^{(m−1)n−m} ]`.
The quoted hypothesis `∀ i, cᵢ ≠ 0` is omitted because the implication does not
need it: balance alone suffices. -/
theorem apn_mCount_generic_of_bal {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) (f : K → K) (hf : IsAPN f) (a : K) (ha : a ≠ 0)
    (c : Fin m → K) (hbal : mPhase m (derivImage f a) c = 0) :
    mCount m (derivImage f a) c = 2 ^ ((m - 1) * n - m) :=
  mCount_generic_of_mPhase_eq_zero hn hm2 (derivImage f a) hcard
    (apn_derivImage_eq_half f hf a ha n hcard) c hbal

/-- **APN + odd `m` + phase positivity ⇒ the generic `m`-tuple count everywhere
on the derivative image.** -/
theorem apn_mCount_generic_of_mPhase_nonneg {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (hcard : Fintype.card K = 2 ^ n) (f : K → K) (hf : IsAPN f) (a : K) (ha : a ≠ 0)
    (hpos : ∀ c ∈ coeffFamily K m, 0 ≤ mPhase m (derivImage f a) c) :
    ∀ c ∈ coeffFamily K m, mCount m (derivImage f a) c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm (derivImage f a) hcard
    (apn_derivImage_eq_half f hf a ha n hcard) hpos

/-- **APN + even `m`: the count on the derivative image is not generic everywhere.** -/
theorem apn_exists_mCount_gt_generic_even {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (hm : Even m)
    (hcard : Fintype.card K = 2 ^ n) (f : K → K) (hf : IsAPN f) (a : K) (ha : a ≠ 0) :
    ∃ c ∈ coeffFamily K m, 2 ^ ((m - 1) * n - m) < mCount m (derivImage f a) c :=
  exists_mCount_gt_generic hn hm2 (derivImage f a) hcard
    (apn_derivImage_eq_half f hf a ha n hcard) hm

end MTuple
