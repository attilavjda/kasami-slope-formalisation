import MTuple.Kasami
import MTuple.Sharpness
import MTupleExt.ExactAffine

/-!
# The `m`-tuple Kasami count for `k ≡ ±1 (mod n)`

`MTuple/MTuple/Kasami.lean` proves the Kasami *triple* count
`N(v₁,v₂) = 2^{2n−3}` for `k ≡ ±1 (mod n)` by showing that in those cases the
derivative image `Δ = Δ(d(k))` is a half-size additive subgroup.  Being a
subgroup is much more than non-negativity of the phase, and this file cashes in
the difference: for such `k` the *whole* `m`-tuple count of `Δ` is known
exactly, for every tuple length `m ≥ 2`, odd or even.

* `KasamiMTupleConjecture F n k m` — the `m`-tuple form of the statement: the
  number of `m`-tuples from `Δ` annihilated by an admissible coefficient vector
  is the generic value `2^{(m−1)n−m}`.  At `m = 3` and coefficient vector
  `(v₁, v₂, v₁+v₂)` this is the original conjecture
  (`kasamiTripleConjecture_of_KasamiMTupleConjecture`).
* `kasamiMTupleConjecture_odd_of_mod_pm_one` — it holds for every **odd** `m ≥ 3`
  when `k ≡ ±1 (mod n)`.
* `kasami_mCount_of_not_const` / `kasami_mCount_const` — the exact count for
  *every* `m ≥ 2`: generic at every non-constant admissible vector, and exactly
  twice generic at every constant one.
* `not_kasamiMTupleConjecture_even_of_mod_pm_one` — consequently the `m`-tuple
  statement is **false** for every even `m ≥ 2`; the conjecture is a genuinely
  odd-`m` phenomenon.

Nothing here touches the residues `k ≢ ±1 (mod n)`, which the library leaves
open (they are covered, at `m = 3`, by the complete solution cited in
`README.md`).
-/

open Finset

namespace MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## `Δ` is a half-size additive subgroup when `k ≡ ±1 (mod n)` -/

theorem kasamiDelta_addClosed_of_mod_pm_one {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    ∀ x ∈ kasamiDelta F (kasamiExp k), ∀ y ∈ kasamiDelta F (kasamiExp k),
      x + y ∈ kasamiDelta F (kasamiExp k) := by
  obtain ⟨j, hΔ⟩ := kasamiDelta_eq_frob_image hn hcard hk
  rw [hΔ]
  exact frobPow_image_add_mem j _ (goldLinImage_add_mem 1 1)

theorem card_kasamiDelta_of_mod_pm_one {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    (kasamiDelta F (kasamiExp k)).card = 2 ^ (n - 1) := by
  obtain ⟨j, hΔ⟩ := kasamiDelta_eq_frob_image hn hcard hk
  rw [hΔ, Finset.card_image_of_injective _ (frobPow_injective (F := F) j)]
  exact card_goldLinImage_one hcard

/-! ## The `m`-tuple form of the conjecture -/

/-- The `m`-tuple form of the Kasami cyclic-additive statement: for every
admissible coefficient vector `c` (all entries nonzero, entries summing to `0`)
the number of `m`-tuples from `Δ(d(k))` annihilated by `c` is the generic value
`2^{(m−1)n−m}`.  For `m = 3` this is the original conjecture. -/
def KasamiMTupleConjecture (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n k m : ℕ) : Prop :=
  ∀ c ∈ coeffFamily F m, mCount m (kasamiDelta F (kasamiExp k)) c = 2 ^ ((m - 1) * n - m)

/-- At `m = 3` the `m`-tuple statement specialises to the triple statement. -/
theorem kasamiTripleConjecture_of_KasamiMTupleConjecture {n k : ℕ}
    (h : KasamiMTupleConjecture F n k 3) : KasamiTripleConjecture F n k := by
  intro v₁ v₂ h₁ h₂ h₁₂
  rw [tripleCount_eq_mCount, h _ (coeff_triple_mem h₁ h₂ h₁₂)]

/-! ## The exact count for every `m`, when `k ≡ ±1 (mod n)` -/

/-- **Non-constant coefficient vector: exactly the generic count**, for every
`m ≥ 2` — odd or even. -/
theorem kasami_mCount_of_not_const {n k m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1)
    {c : Fin m → F} (hc : c ∈ coeffFamily F m) (hne : ¬ ∀ i j, c i = c j) :
    mCount m (kasamiDelta F (kasamiExp k)) c = 2 ^ ((m - 1) * n - m) :=
  mCount_addClosed_of_not_const hn hm hcard _
    (kasamiDelta_addClosed_of_mod_pm_one hn hcard hk)
    (card_kasamiDelta_of_mod_pm_one hn hcard hk) hc hne

/-- **Constant coefficient vector: exactly twice the generic count.** -/
theorem kasami_mCount_const {n k m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1)
    {a : F} {c : Fin m → F} (hc : c ∈ coeffFamily F m) (hconst : ∀ i, c i = a) :
    mCount m (kasamiDelta F (kasamiExp k)) c = 2 * 2 ^ ((m - 1) * n - m) :=
  mCount_addClosed_const_eq_two_mul hn hm hcard _
    (kasamiDelta_addClosed_of_mod_pm_one hn hcard hk)
    (card_kasamiDelta_of_mod_pm_one hn hcard hk) hc hconst

/-- **The `m`-tuple conjecture holds for every odd `m ≥ 3` when `k ≡ ±1 (mod n)`.** -/
theorem kasamiMTupleConjecture_odd_of_mod_pm_one {n k m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hodd : Odd m) (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    KasamiMTupleConjecture F n k m := fun c hc =>
  kasami_mCount_of_not_const hn (by omega) hcard hk hc (not_const_of_odd hodd hc)

/-- The original triple conjecture is the case `m = 3`, recovered from the
`m`-tuple theorem. -/
theorem kasamiTripleConjecture_of_mod_pm_one' {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    KasamiTripleConjecture F n k :=
  kasamiTripleConjecture_of_KasamiMTupleConjecture
    (kasamiMTupleConjecture_odd_of_mod_pm_one hn le_rfl (by decide) hcard hk)

/-- **The `m`-tuple statement fails for every even `m ≥ 2`.**  The constant
vector `(a, …, a)` is admissible for even `m`, and there the count is twice the
generic value.  So the Kasami statement is specific to odd tuple lengths. -/
theorem not_kasamiMTupleConjecture_even_of_mod_pm_one {n k m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (heven : Even m) (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    ¬ KasamiMTupleConjecture F n k m := by
  intro h
  have hconst : (fun _ : Fin m => (1 : F)) ∈ coeffFamily F m :=
    const_mem_coeffFamily heven one_ne_zero
  have h1 := h _ hconst
  have h2 := kasami_mCount_const (F := F) (a := 1) hn hm hcard hk hconst (fun _ => rfl)
  rw [h1] at h2
  have hpos : 0 < 2 ^ ((m - 1) * n - m) := Nat.two_pow_pos _
  omega

/-- **For every `k`, the even-`m` statement fails as soon as `Δ` is half-size.**
No congruence condition on `k` is needed here: the even-`m` obstruction of the
library applies to every half-size set. -/
theorem not_kasamiMTupleConjecture_even_of_card {n k m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (heven : Even m) (hcard : Fintype.card F = 2 ^ n)
    (hΔ : (kasamiDelta F (kasamiExp k)).card = 2 ^ (n - 1)) :
    ¬ KasamiMTupleConjecture F n k m := fun h =>
  not_forall_mCount_generic_even hn hm _ hcard hΔ heven h

end MTuple
