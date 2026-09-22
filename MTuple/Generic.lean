import MTuple.Mean

/-!
# The generic `m`-tuple count: the odd theorem and the even obstruction

Throughout, `K` is a finite field of characteristic `2` with `|K| = 2ⁿ`, `n ≥ 2`,
and `S ⊆ K` is a *half-size* set, `|S| = 2^{n−1}`.  The generic count is
`2^{(m−1)n−m}`.

* `mCount_generic_iff_mPhase_eq_zero` — the count is generic exactly when the
  phase vanishes (any `m ≥ 2`, no parity assumption).
* `mTupleCount_odd_of_mPhase_nonneg` — **odd `m ≥ 3`**: if the phase is
  non-negative at every admissible `c`, then the count is generic at every
  admissible `c`.  (Non-negative terms with zero sum are all zero; the sum is
  zero by `MTuple.sum_mPhase_eq_zero`.)
* `not_forall_mCount_generic_even` — **even `m ≥ 2`**: the same conclusion is
  false for *every* half-size set, so no hypothesis on the phase can produce it.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## Dictionary between the count, the deficiency and the phase -/

omit [Fintype K] [CharP K 2] in
/-- The count is generic exactly when the deficiency vanishes. -/
theorem mCount_generic_iff_mDeficiency_eq_zero {n m : ℕ} (S : Finset K) (c : Fin m → K) :
    mCount m S c = 2 ^ ((m - 1) * n - m) ↔ mDeficiency n m S c = 0 := by
  rw [mDeficiency, sub_eq_zero]
  constructor
  · intro h; rw [h]; push_cast; ring
  · intro h; exact_mod_cast h

/-- **Balance ⇒ generic count** (any tuple length `m ≥ 2`, no parity assumption).
This is the second FOL statement: with `Bal ≡ ∑_{v≠0} ∏ᵢ T̂(v cᵢ) = 0`,
the `m`-tuple count is exactly `2^{(m−1)n−m}`. -/
theorem mCount_generic_of_mPhase_eq_zero {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    (c : Fin m → K) (hbal : mPhase m S c = 0) :
    mCount m S c = 2 ^ ((m - 1) * n - m) := by
  have h := card_mul_mDeficiency_eq_mPhase hn hm2 S hcard hS c
  rw [hbal] at h
  have hd : mDeficiency n m S c = 0 :=
    (mul_eq_zero.1 h).resolve_left (card_pos_int (K := K)).ne'
  exact (mCount_generic_iff_mDeficiency_eq_zero S c).2 hd

/-- The count is generic exactly when the phase vanishes. -/
theorem mCount_generic_iff_mPhase_eq_zero {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m)
    (S : Finset K) (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    (c : Fin m → K) :
    mCount m S c = 2 ^ ((m - 1) * n - m) ↔ mPhase m S c = 0 := by
  refine ⟨fun h => ?_, fun h => mCount_generic_of_mPhase_eq_zero hn hm2 S hcard hS c h⟩
  have hd : mDeficiency n m S c = 0 := (mCount_generic_iff_mDeficiency_eq_zero S c).1 h
  have := card_mul_mDeficiency_eq_mPhase hn hm2 S hcard hS c
  rw [hd, mul_zero] at this
  exact this.symm

/-! ## Odd `m`: pointwise positivity forces the generic count -/

/-- **The `m`-tuple count for odd `m`.**  Pointwise non-negativity of the phase
sum on the admissible family forces the generic count `2^{(m−1)n−m}` at *every*
admissible coefficient vector. -/
theorem mTupleCount_odd_of_mPhase_nonneg {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hm : Odd m) (S : Finset K) (hcard : Fintype.card K = 2 ^ n)
    (hS : S.card = 2 ^ (n - 1))
    (hpos : ∀ c ∈ coeffFamily K m, 0 ≤ mPhase m S c) :
    ∀ c ∈ coeffFamily K m, mCount m S c = 2 ^ ((m - 1) * n - m) := by
  have hzero : ∀ c ∈ coeffFamily K m, mPhase m S c = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hpos).1
      (sum_mPhase_eq_zero (by omega) S hcard hS hm)
  intro c hc
  exact mCount_generic_of_mPhase_eq_zero hn (by omega) S hcard hS c (hzero c hc)

/-- For odd `m`, phase positivity on the admissible family is *equivalent* to the
generic count everywhere. -/
theorem mPhase_nonneg_iff_forall_generic {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hm : Odd m) (S : Finset K) (hcard : Fintype.card K = 2 ^ n)
    (hS : S.card = 2 ^ (n - 1)) :
    (∀ c ∈ coeffFamily K m, 0 ≤ mPhase m S c) ↔
      (∀ c ∈ coeffFamily K m, mCount m S c = 2 ^ ((m - 1) * n - m)) := by
  refine ⟨mTupleCount_odd_of_mPhase_nonneg hn hm3 hm S hcard hS, fun h c hc => ?_⟩
  rw [(mCount_generic_iff_mPhase_eq_zero hn (by omega) S hcard hS c).1 (h c hc)]

/-! ## Even `m`: the generic count necessarily fails somewhere -/

/-- **Even `m`: the count is not generic everywhere.**  There is an admissible
coefficient vector at which the count strictly exceeds `2^{(m−1)n−m}`. -/
theorem exists_mCount_gt_generic {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    ∃ c ∈ coeffFamily K m, 2 ^ ((m - 1) * n - m) < mCount m S c := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ c ∈ coeffFamily K m, mDeficiency n m S c ≤ 0 := by
    intro c hc
    have := hcon c hc
    rw [mDeficiency, sub_nonpos]
    exact_mod_cast this
  have hnp := Finset.sum_nonpos hle
  have hpos := sum_mDeficiency_pos hn hm2 S hcard hS hm
  linarith

/-- **Even `m`: the balance hypothesis fails somewhere.**  There is an admissible
coefficient vector with strictly positive phase. -/
theorem exists_mPhase_pos_even {n m : ℕ} (hn : 2 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    ∃ c ∈ coeffFamily K m, 0 < mPhase m S c := by
  by_contra hcon
  push_neg at hcon
  have := Finset.sum_nonpos hcon
  have hpos := sum_mPhase_pos hn S hcard hS hm
  linarith

/-- **Even `m`: the phase cannot vanish at every admissible coefficient vector.** -/
theorem not_forall_mPhase_eq_zero_even {n m : ℕ} (hn : 2 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    ¬ (∀ c ∈ coeffFamily K m, mPhase m S c = 0) := by
  intro h
  obtain ⟨c, hc, hpos⟩ := exists_mPhase_pos_even hn S hcard hS hm
  rw [h c hc] at hpos
  exact lt_irrefl 0 hpos

/-- **Even `m`: the analogue of the odd-`m` theorem is false.**  The conclusion
"generic count at every admissible `c`" fails for *every* half-size set, so no
hypothesis on the phase (positivity included) can produce it. -/
theorem not_forall_mCount_generic_even {n m : ℕ} (hn : 2 ≤ n) (hm2 : 2 ≤ m) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) (hm : Even m) :
    ¬ (∀ c ∈ coeffFamily K m, mCount m S c = 2 ^ ((m - 1) * n - m)) := by
  intro h
  obtain ⟨c, hc, hgt⟩ := exists_mCount_gt_generic hn hm2 S hcard hS hm
  rw [h c hc] at hgt
  exact lt_irrefl _ hgt

end MTuple
