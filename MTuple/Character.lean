import Mathlib

/-!
# The additive character and its Fourier transform

The base layer of the library: everything else is built on this file, which
depends only on `Mathlib`.

Here we set up the canonical additive character of a finite field of
characteristic `2`,

  `χ(x) = (−1)^{Tr(x)} ∈ ℤ`,

its multiplicativity, and orthogonality `∑_t χ(t c) = |K| · [c = 0]`, together
with the Fourier transform `T̂_S(u) = ∑_{y ∈ S} χ(u y)` of the indicator of a
finite subset `S ⊆ K`.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A field of characteristic `2` is a `ZMod 2`-algebra, so the absolute trace
`Tr : K → 𝔽₂` is available. -/
noncomputable instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The canonical additive character `χ(x) = (−1)^{Tr x}`, valued in `ℤ`. -/
noncomputable def chiZ (x : K) : ℤ :=
  if Algebra.trace (ZMod 2) K x = 0 then 1 else -1

/-- The Fourier transform of the indicator of `S`: `T̂_S(u) = ∑_{y ∈ S} χ(u y)`. -/
noncomputable def Tsum (S : Finset K) (u : K) : ℤ := ∑ y ∈ S, chiZ (u * y)

omit [Fintype K] [DecidableEq K] in
@[simp] theorem chiZ_zero : chiZ (0 : K) = 1 := by simp [chiZ]

omit [Fintype K] [DecidableEq K] in
theorem Tsum_zero (S : Finset K) : Tsum S 0 = S.card := by
  simp [Tsum, chiZ]

omit [Fintype K] [DecidableEq K] in
/-- The character is multiplicative on sums. -/
theorem chiZ_add (x y : K) : chiZ (x + y) = chiZ x * chiZ y := by
  have key : ∀ a b : ZMod 2, (if a + b = 0 then (1 : ℤ) else -1)
      = (if a = 0 then (1 : ℤ) else -1) * (if b = 0 then (1 : ℤ) else -1) := by decide
  simp only [chiZ, map_add]
  exact key _ _

omit [Fintype K] [DecidableEq K] in
/-- The character of a finite sum is the product of the characters. -/
theorem chiZ_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    chiZ (∑ i ∈ s, f i) = ∏ i ∈ s, chiZ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chiZ_add, ih]

omit [DecidableEq K] in
/-- The character sum over the whole field vanishes, because the trace is
surjective onto `𝔽₂`. -/
theorem sum_chiZ : ∑ x : K, chiZ x = 0 := by
  obtain ⟨e, he⟩ := Algebra.trace_surjective (ZMod 2) K 1
  have hflip : ∀ x : K, chiZ (x + e) = -chiZ x := by
    intro x
    rw [chiZ_add]
    have : chiZ e = -1 := by simp [chiZ, he]
    rw [this]; ring
  have hbij : ∑ x : K, chiZ (x + e) = ∑ x : K, chiZ x :=
    Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  simp only [hflip, Finset.sum_neg_distrib] at hbij
  linarith

/-- **Orthogonality**: `∑_t χ(t c) = |K|` if `c = 0`, and `0` otherwise. -/
theorem sum_chiZ_mul (c : K) :
    ∑ t : K, chiZ (t * c) = if c = 0 then (Fintype.card K : ℤ) else 0 := by
  by_cases hc : c = 0
  · simp [hc, chiZ]
  · rw [if_neg hc, ← sum_chiZ (K := K)]
    exact Fintype.sum_equiv (Equiv.mulRight₀ c hc) _ _ (fun _ => rfl)

omit [DecidableEq K] [CharP K 2] in
theorem card_pos_int : (0 : ℤ) < (Fintype.card K : ℤ) := by
  exact_mod_cast Fintype.card_pos

end MTuple
