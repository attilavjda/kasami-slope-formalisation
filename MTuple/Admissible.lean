import MTuple.Character

/-!
# The admissible family of coefficient vectors

A coefficient vector `c : Fin m → K` is *admissible* when every entry is nonzero
and the entries sum to zero:

`coeffFamily K m = { c : (∀ i, c i ≠ 0) ∧ ∑ i, c i = 0 }`.

These are the vectors the `m`-tuple problem is about.  The only substantive
result here is that the family is nonempty as soon as `m ≥ 2` and `|K| > 2`
(`coeffFamily_nonempty`), so no statement quantified over it is vacuous.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The admissible coefficient vectors: every entry nonzero, total sum zero. -/
noncomputable def coeffFamily (K : Type*) [Field K] [Fintype K] [DecidableEq K] (m : ℕ) :
    Finset (Fin m → K) :=
  (Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))).filter (fun c => ∑ i, c i = 0)

omit [CharP K 2] in
theorem mem_coeffFamily {m : ℕ} {c : Fin m → K} :
    c ∈ coeffFamily K m ↔ (∀ i, c i ≠ 0) ∧ ∑ i, c i = 0 := by
  simp [coeffFamily, Fintype.mem_piFinset, Finset.mem_erase]


omit [CharP K 2] in
/-- A field with more than two elements contains an element different from `0`
and `1`. -/
theorem exists_ne_zero_ne_one (h : 2 < Fintype.card K) : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (univ : Finset K) ⊆ {0, 1} := by
    intro x _
    rcases eq_or_ne x 0 with h0 | h0
    · simp [h0]
    · simp [hcon x h0]
  have hcard : (univ : Finset K).card ≤ ({0, 1} : Finset K).card :=
    Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  rw [Finset.card_univ] at hcard
  omega

/-- The admissible family is nonempty for every `m ≥ 2`, provided `|K| > 2`.
Hence none of the statements above is vacuous. -/
theorem coeffFamily_nonempty {m : ℕ} (hm2 : 2 ≤ m) (hK : 2 < Fintype.card K) :
    (coeffFamily K m).Nonempty := by
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne_one hK
  have hr1' : 1 + r ≠ 0 := by
    intro h
    exact hr1 (by
      have : r = -1 := by linear_combination h
      rw [this]; exact CharTwo.neg_eq 1)
  rcases Nat.even_or_odd m with hm | hm
  · -- even `m`: the all-ones vector works
    refine ⟨fun _ => (1 : K), ?_⟩
    rw [mem_coeffFamily]
    refine ⟨fun _ => one_ne_zero, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact (CharP.cast_eq_zero_iff K 2 m).2 hm.two_dvd
  · -- odd `m ≥ 3`: `(r, 1+r, 1, …, 1)`
    have hm3 : 3 ≤ m := by rcases hm with ⟨k, hk⟩; omega
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    let c : Fin m → K := fun i => if i = i0 then r else if i = i1 then 1 + r else 1
    have e0 : c i0 = r := by simp [c]
    have e1 : c i1 = 1 + r := by simp [c, h01.symm]
    refine ⟨c, ?_⟩
    rw [mem_coeffFamily]
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h0 : i = i0
      · rw [h0, e0]; exact hr0
      · by_cases h1 : i = i1
        · rw [h1, e1]; exact hr1'
        · simp [c, h0, h1]
    · have hsplit : ∑ i, c i
          = ∑ i ∈ ({i0, i1} : Finset (Fin m)), c i
            + ∑ i ∈ univ \ ({i0, i1} : Finset (Fin m)), c i := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ _)]
      have hpair : ∑ i ∈ ({i0, i1} : Finset (Fin m)), c i = 1 := by
        rw [Finset.sum_pair h01, e0, e1]
        linear_combination CharTwo.add_self_eq_zero r
      have hrest : ∀ i ∈ univ \ ({i0, i1} : Finset (Fin m)), c i = 1 := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hi
        push_neg at hi
        simp [c, hi.2.1, hi.2.2]
      have hcardrest : (univ \ ({i0, i1} : Finset (Fin m))).card = m - 2 := by
        rw [Finset.card_univ_diff, Fintype.card_fin, Finset.card_pair h01]
      have hcast : ((m - 2 : ℕ) : K) = 1 := by
        obtain ⟨k, hk⟩ : Odd (m - 2) := by rcases hm with ⟨j, hj⟩; exact ⟨j - 1, by omega⟩
        rw [hk]
        push_cast
        linear_combination CharTwo.add_self_eq_zero (k : K)
      have hsum2 : ∑ i ∈ univ \ ({i0, i1} : Finset (Fin m)), c i = 1 := by
        rw [Finset.sum_congr rfl hrest, Finset.sum_const, hcardrest, nsmul_eq_mul, mul_one, hcast]
      rw [hsplit, hpair, hsum2]
      exact CharTwo.add_self_eq_zero 1
end MTuple
