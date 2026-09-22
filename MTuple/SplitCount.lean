import MTuple.Count

/-!
# Splitting the `m`-tuple count into a convolution

Brute force over `Sᵐ` is hopeless as soon as `|S|ᵐ` gets large: already
`|S| = 64`, `m = 5` means `64⁵ ≈ 10⁹` tuples.  This file provides the standard
convolution shortcut, which makes such counts machine-checkable.

For a coefficient vector `c : Fin (m₁ + m₂) → K` write `s₁`, `s₂` for the two
partial sums.  Since the characteristic is `2`, a tuple is annihilated by `c`
exactly when its two halves have *equal* partial sums, so

`mCount (m₁+m₂) S c = ∑_{z ∈ K} fiberCount m₁ S c₁ z * fiberCount m₂ S c₂ z`
(`mCount_split`),

where `fiberCount m S c z = #{x ∈ Sᵐ : ∑ᵢ cᵢxᵢ = z}`.  The cost drops from
`|S|^{m₁+m₂}` to `|K| · (|S|^{m₁} + |S|^{m₂})`.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- `fiberCount m S c z = #{x ∈ Sᵐ : ∑ᵢ cᵢ xᵢ = z}`; the `m`-tuple count is the
fiber over `z = 0`. -/
def fiberCount (m : ℕ) (S : Finset K) (c : Fin m → K) (z : K) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin m => S)).filter (fun x => ∑ i, c i * x i = z)).card

omit [Fintype K] [CharP K 2] in
theorem mCount_eq_fiberCount (m : ℕ) (S : Finset K) (c : Fin m → K) :
    mCount m S c = fiberCount m S c 0 := rfl

omit [Fintype K] [CharP K 2] in
/-- Cutting a tuple into its first `m₁` and last `m₂` entries. -/
theorem mCount_eq_card_product (m₁ m₂ : ℕ) (S : Finset K) (c : Fin (m₁ + m₂) → K) :
    mCount (m₁ + m₂) S c
      = (((Fintype.piFinset (fun _ : Fin m₁ => S)) ×ˢ
          (Fintype.piFinset (fun _ : Fin m₂ => S))).filter (fun p =>
            (∑ i, c (Fin.castAdd m₂ i) * p.1 i) + (∑ i, c (Fin.natAdd m₁ i) * p.2 i) = 0)).card := by
  classical
  refine Finset.card_nbij'
    (fun x => (fun i => x (Fin.castAdd m₂ i), fun i => x (Fin.natAdd m₁ i)))
    (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_product] at hx ⊢
    refine ⟨⟨fun i => hx.1 _, fun i => hx.1 _⟩, ?_⟩
    have h2 := hx.2
    rw [Fin.sum_univ_add (f := fun i => c i * x i)] at h2
    exact h2
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_product] at hp ⊢
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hp.1.1 j
      · rw [Fin.append_right]; exact hp.1.2 j
    · rw [Fin.sum_univ_add (f := fun i => c i * Fin.append p.1 p.2 i)]
      simpa only [Fin.append_left, Fin.append_right] using hp.2
  · intro x _
    exact Fin.append_castAdd_natAdd
  · intro p _
    simp [Fin.append_left, Fin.append_right]

/-- **The convolution formula.**  Over a field of characteristic `2` the
`(m₁+m₂)`-tuple count is the inner product of the two partial-sum
distributions. -/
theorem mCount_split (m₁ m₂ : ℕ) (S : Finset K) (c : Fin (m₁ + m₂) → K) :
    mCount (m₁ + m₂) S c
      = ∑ z : K, fiberCount m₁ S (fun i => c (Fin.castAdd m₂ i)) z
          * fiberCount m₂ S (fun i => c (Fin.natAdd m₁ i)) z := by
  classical
  set P₁ := Fintype.piFinset (fun _ : Fin m₁ => S) with hP₁
  set P₂ := Fintype.piFinset (fun _ : Fin m₂ => S) with hP₂
  set s₁ : (Fin m₁ → K) → K := fun x => ∑ i, c (Fin.castAdd m₂ i) * x i with hs₁
  set s₂ : (Fin m₂ → K) → K := fun x => ∑ i, c (Fin.natAdd m₁ i) * x i with hs₂
  rw [mCount_eq_card_product m₁ m₂ S c]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (Fin m₁ → K) × (Fin m₂ → K) => s₁ p.1) (t := (univ : Finset K))
    (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hset : ((P₁ ×ˢ P₂).filter (fun p => s₁ p.1 + s₂ p.2 = 0)).filter
      (fun p => s₁ p.1 = z) = (P₁.filter (fun x => s₁ x = z)) ×ˢ (P₂.filter (fun x => s₂ x = z)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hsum⟩, hz⟩
      refine ⟨⟨h1, hz⟩, h2, ?_⟩
      have : s₂ p.2 = s₁ p.1 := (CharTwo.add_eq_zero.1 hsum).symm
      rw [this, hz]
    · rintro ⟨⟨h1, hz1⟩, h2, hz2⟩
      exact ⟨⟨⟨h1, h2⟩, by rw [hz1, hz2]; exact CharTwo.add_self_eq_zero z⟩, hz1⟩
  rw [hset, Finset.card_product]
  rfl

omit [Fintype K] [CharP K 2] in
/-- The fiber count as a multiplicity in the multiset of partial sums.  This is
the form that actually *computes*: the multiset of partial sums is built once
and then only counted into, instead of re-filtering `Sᵐ` for every `z`. -/
theorem fiberCount_eq_count (m : ℕ) (S : Finset K) (c : Fin m → K) (z : K) :
    fiberCount m S c z
      = ((Fintype.piFinset (fun _ : Fin m => S)).val.map (fun x => ∑ i, c i * x i)).count z := by
  rw [Multiset.count_map]
  simp [fiberCount, Finset.card, Finset.filter, eq_comm]

/-- **The convolution formula in computable form.**  Equivalent to
`mCount_split`, but phrased with multiset multiplicities, which is what makes
the `m = 5` counts over `GF(32)` and `GF(128)` machine-checkable. -/
theorem mCount_split_count (m₁ m₂ : ℕ) (S : Finset K) (c : Fin (m₁ + m₂) → K) :
    mCount (m₁ + m₂) S c
      = ∑ z : K,
          ((Fintype.piFinset (fun _ : Fin m₁ => S)).val.map
              (fun x => ∑ i, c (Fin.castAdd m₂ i) * x i)).count z *
          ((Fintype.piFinset (fun _ : Fin m₂ => S)).val.map
              (fun x => ∑ i, c (Fin.natAdd m₁ i) * x i)).count z := by
  rw [mCount_split]
  exact Finset.sum_congr rfl fun z _ => by
    rw [fiberCount_eq_count, fiberCount_eq_count]

end MTuple
