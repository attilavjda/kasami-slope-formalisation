import MTuple.Generic

/-!
# The sign-factorisation mechanism, and the sets that admit it

A *sign factorisation* of the transform of `S` is a decomposition

`T̂_S(u) = ε(u)·w(u)`,  `w ≥ 0`,  `ε(0) = 1`,  `ε(u+v) = ε(u)·ε(v)`.

Because the admissible coefficient vectors sum to zero, the `ε`-part cancels in
`∏ᵢ T̂_S(t cᵢ)`, so the phase is non-negative *unconditionally*
(`mPhase_nonneg_of_sign_factorization`).  Combined with the odd-`m` theorem this
gives the generic count with nothing assumed
(`mTupleCount_odd_of_sign_factorization`).

The rest of the file exhibits the sets to which this applies:

* a coset `V + b` of an additive subgroup `V` (`mTupleCount_odd_affine_coset`);
* in particular the trace hyperplane `H(u₀) = {y : Tr(u₀y) = 0}` and its cosets,
  which are half-size for `u₀ ≠ 0` (`mTupleCount_odd_traceHyperplane`,
  `mTupleCount_odd_traceHyperplane_coset`), giving half-size sets with
  non-negative phase in every field (`exists_half_size_mPhase_nonneg`).

`MTuple/MTuple/Rigidity.lean` proves that these are the *only* sets with
a sign factorisation.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## The mechanism

The mechanism proposed for even `m` is: write `Ŝ(u) = ε(u)·w(u)` with `w ≥ 0`
and `ε` an additive `±1`-valued character.  Then for `∑ᵢ cᵢ = 0`

  `∏ᵢ Ŝ(t cᵢ) = ε(t·∑ᵢ cᵢ)·∏ᵢ w(t cᵢ) = ∏ᵢ w(t cᵢ) ≥ 0`,

so the phase is non-negative at every admissible `c` — for *every* tuple length.
For odd `m` this replaces the positivity hypothesis outright and yields the
generic count.  For even `m` it does *not* yield balance: non-negative phases
are compatible with the strictly positive mean of §3, and indeed
`exists_mPhase_pos_even` shows balance must fail somewhere.
-/

omit [Fintype K] [DecidableEq K] [CharP K 2] in
/-- A `ℤ`-valued function that is multiplicative on sums turns finite sums into
finite products. -/
theorem prod_eps_eq_eps_sum {ι : Type*} (eps : K → ℤ) (heps0 : eps 0 = 1)
    (heps : ∀ u v, eps (u + v) = eps u * eps v) (s : Finset ι) (f : ι → K) :
    ∏ i ∈ s, eps (f i) = eps (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [heps0]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, heps, ih]

/-- **Sign factorisation ⇒ phase non-negativity** at every admissible `c`
(any tuple length). -/
theorem mPhase_nonneg_of_sign_factorization {m : ℕ} (S : Finset K) (eps w : K → ℤ)
    (hfac : ∀ u, Tsum S u = eps u * w u) (hw : ∀ u, 0 ≤ w u) (heps0 : eps 0 = 1)
    (heps : ∀ u v, eps (u + v) = eps u * eps v) {c : Fin m → K}
    (hc : c ∈ coeffFamily K m) :
    0 ≤ mPhase m S c := by
  rw [mem_coeffFamily] at hc
  refine Finset.sum_nonneg fun t _ => ?_
  have hsplit : ∏ i, Tsum S (t * c i)
      = (∏ i, eps (t * c i)) * ∏ i, w (t * c i) := by
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib]
  have hone : (∏ i, eps (t * c i)) = 1 := by
    rw [prod_eps_eq_eps_sum eps heps0 heps, ← Finset.mul_sum, hc.2, mul_zero, heps0]
  rw [hsplit, hone, one_mul]
  exact Finset.prod_nonneg fun i _ => hw _

/-- **Odd `m` under sign factorisation**: the generic count, with no positivity
hypothesis to assume separately. -/
theorem mTupleCount_odd_of_sign_factorization {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hm : Odd m) (S : Finset K) (hcard : Fintype.card K = 2 ^ n)
    (hS : S.card = 2 ^ (n - 1)) (eps w : K → ℤ)
    (hfac : ∀ u, Tsum S u = eps u * w u) (hw : ∀ u, 0 ≤ w u) (heps0 : eps 0 = 1)
    (heps : ∀ u v, eps (u + v) = eps u * eps v) :
    ∀ c ∈ coeffFamily K m, mCount m S c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm S hcard hS
    (fun _ hc => mPhase_nonneg_of_sign_factorization S eps w hfac hw heps0 heps hc)

/-! ## Character sums over an additive subgroup -/

/-- The character sum over an additive subgroup is non-negative (it is `|V|` when
the character is trivial on `V`, and `0` otherwise). -/
theorem subgroupCharSum_nonneg (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (u : K) :
    0 ≤ ∑ v ∈ V, chiZ (u * v) := by
  by_cases h : ∀ v ∈ V, chiZ (u * v) = 1
  · rw [Finset.sum_congr rfl h]
    simp
  · push_neg at h
    obtain ⟨v₀, hv₀, hne⟩ := h
    have hval : chiZ (u * v₀) = -1 := by
      by_cases ht : Algebra.trace (ZMod 2) K (u * v₀) = 0
      · exact absurd (by simp [chiZ, ht]) hne
      · simp [chiZ, ht]
    have hreindex : ∑ v ∈ V, chiZ (u * (v + v₀)) = ∑ v ∈ V, chiZ (u * v) := by
      refine Finset.sum_nbij' (fun v => v + v₀) (fun v => v + v₀) ?_ ?_ ?_ ?_ ?_
      · exact fun v hv => hVadd v hv v₀ hv₀
      · exact fun v hv => hVadd v hv v₀ hv₀
      · intro v _
        show v + v₀ + v₀ = v
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · intro v _
        show v + v₀ + v₀ = v
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · intro v _
        rfl
    have hflip : ∑ v ∈ V, chiZ (u * (v + v₀)) = - ∑ v ∈ V, chiZ (u * v) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [mul_add, chiZ_add, hval]
      ring
    rw [hreindex] at hflip
    linarith

/-- The transform of an additive subgroup is non-negative. -/
theorem Tsum_addClosed_nonneg (V : Finset K) (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (u : K) :
    0 ≤ Tsum V u :=
  subgroupCharSum_nonneg V hVadd u

/-- **The phase of an additive subgroup is non-negative**, at every admissible
coefficient vector and every tuple length. -/
theorem mPhase_addClosed_nonneg {m : ℕ} (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) {c : Fin m → K} (hc : c ∈ coeffFamily K m) :
    0 ≤ mPhase m V c :=
  mPhase_nonneg_of_sign_factorization V (fun _ => 1) (Tsum V)
    (fun u => (one_mul _).symm) (Tsum_addClosed_nonneg V hVadd) rfl
    (fun _ _ => by norm_num) hc

/-- **The `m`-tuple count of a half-size additive subgroup is generic for every
odd `m ≥ 3`.** -/
theorem mTupleCount_odd_of_addClosed {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (V : Finset K) (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V)
    (hcard : Fintype.card K = 2 ^ n) (hV : V.card = 2 ^ (n - 1)) :
    ∀ c ∈ coeffFamily K m, mCount m V c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm V hcard hV
    (fun _ hc => mPhase_addClosed_nonneg V hVadd hc)

/-! ## The transform of an affine coset factorises -/

omit [Fintype K] in
/-- `T̂_{V+b}(u) = χ(u b) · ∑_{v ∈ V} χ(u v)`. -/
theorem Tsum_coset (V : Finset K) (b u : K) :
    Tsum (V.image (fun v => v + b)) u = chiZ (u * b) * ∑ v ∈ V, chiZ (u * v) := by
  rw [Tsum, Finset.sum_image (fun x _ y _ h => by
    simpa using add_right_cancel h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_add, chiZ_add, mul_comm]

/-- **The phase of a coset of an additive subgroup is non-negative**, at every
admissible coefficient vector and every tuple length. -/
theorem mPhase_coset_nonneg {m : ℕ} (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (b : K) {c : Fin m → K}
    (hc : c ∈ coeffFamily K m) :
    0 ≤ mPhase m (V.image (fun v => v + b)) c :=
  mPhase_nonneg_of_sign_factorization _
    (fun u => chiZ (u * b)) (fun u => ∑ v ∈ V, chiZ (u * v))
    (Tsum_coset V b) (subgroupCharSum_nonneg V hVadd)
    (by simp)
    (fun u v => by show chiZ ((u + v) * b) = chiZ (u * b) * chiZ (v * b)
                   rw [add_mul, chiZ_add]) hc

/-- **The `m`-tuple count of a half-size affine coset is generic for every odd
`m ≥ 3`.**  No positivity hypothesis is assumed: the sign factorisation supplies
it. -/
theorem mTupleCount_odd_affine_coset {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (V : Finset K) (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (b : K)
    (hcard : Fintype.card K = 2 ^ n)
    (hS : (V.image (fun v => v + b)).card = 2 ^ (n - 1)) :
    ∀ c ∈ coeffFamily K m, mCount m (V.image (fun v => v + b)) c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm _ hcard hS
    (fun _ hc => mPhase_coset_nonneg V hVadd b hc)

/-! ## The trace hyperplane and its size -/

/-- The trace hyperplane `H(u₀) = { y : Tr(u₀ y) = 0 }`. -/
noncomputable def traceHyperplane (u₀ : K) : Finset K :=
  univ.filter (fun y => Algebra.trace (ZMod 2) K (u₀ * y) = 0)

omit [DecidableEq K] in
theorem mem_traceHyperplane {u₀ y : K} :
    y ∈ traceHyperplane u₀ ↔ Algebra.trace (ZMod 2) K (u₀ * y) = 0 := by
  simp [traceHyperplane]

omit [DecidableEq K] in
/-- The trace hyperplane is closed under addition. -/
theorem traceHyperplane_add_mem (u₀ : K) :
    ∀ x ∈ traceHyperplane u₀, ∀ y ∈ traceHyperplane u₀, x + y ∈ traceHyperplane u₀ := by
  intro x hx y hy
  rw [mem_traceHyperplane] at hx hy ⊢
  rw [mul_add, map_add, hx, hy, add_zero]

/-- For `u₀ ≠ 0` the trace hyperplane is half-size. -/
theorem card_traceHyperplane {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {u₀ : K} (hu₀ : u₀ ≠ 0) :
    (traceHyperplane u₀).card = 2 ^ (n - 1) := by
  -- a point off the hyperplane
  obtain ⟨e, he⟩ := Algebra.trace_surjective (ZMod 2) K 1
  set z : K := u₀⁻¹ * e with hz
  have huz : u₀ * z = e := by
    rw [hz, ← mul_assoc, mul_inv_cancel₀ hu₀, one_mul]
  -- translation by `z` is a bijection from the hyperplane onto its complement
  have hswap : (univ \ traceHyperplane u₀).card = (traceHyperplane u₀).card := by
    refine Finset.card_nbij' (fun y => y + z) (fun y => y + z) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_sdiff, mem_traceHyperplane] at hy
      rw [Finset.mem_coe, mem_traceHyperplane, mul_add, map_add, huz, he]
      have hy2 : Algebra.trace (ZMod 2) K (u₀ * y) = 1 := by
        have hne := hy.2
        revert hne
        generalize Algebra.trace (ZMod 2) K (u₀ * y) = t
        revert t
        decide
      rw [hy2]
      decide
    · intro y hy
      rw [Finset.mem_coe, mem_traceHyperplane] at hy
      rw [Finset.mem_coe, Finset.mem_sdiff, mem_traceHyperplane]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mul_add, map_add, hy, huz, he, zero_add]
      decide
    · intro y _
      show y + z + z = y
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · intro y _
      show y + z + z = y
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hsub : (traceHyperplane u₀) ⊆ univ := Finset.subset_univ _
  have hcard' : (univ \ traceHyperplane u₀).card
      = Fintype.card K - (traceHyperplane u₀).card := by
    rw [Finset.card_univ_diff]
  have hle : (traceHyperplane u₀).card ≤ Fintype.card K := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsub
  have hsplit : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hcard'] at hswap
  omega

/-! ## Non-negativity of the phase, unconditionally -/

/-- The character sums of a trace hyperplane are non-negative. -/
theorem Tsum_traceHyperplane_nonneg (u₀ u : K) : 0 ≤ Tsum (traceHyperplane u₀) u :=
  Tsum_addClosed_nonneg _ (traceHyperplane_add_mem u₀) u

/-- **The phase hypothesis holds outright for a trace hyperplane**, at every
admissible coefficient vector and every tuple length. -/
theorem mPhase_traceHyperplane_nonneg {m : ℕ} (u₀ : K) :
    ∀ c ∈ coeffFamily K m, 0 ≤ mPhase m (traceHyperplane u₀) c := by
  intro c hc
  exact mPhase_nonneg_of_sign_factorization _ (fun _ => 1) (Tsum (traceHyperplane u₀))
    (fun u => (one_mul _).symm) (Tsum_traceHyperplane_nonneg u₀) rfl (fun _ _ => by norm_num) hc

/-! ## The unconditional generic count for odd `m` -/

/-- **The trace hyperplane has the generic `m`-tuple count for every odd `m ≥ 3`
and every `n ≥ 2`** — unconditionally: no phase hypothesis is assumed, it is
proved. -/
theorem mTupleCount_odd_traceHyperplane {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m) (hm : Odd m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) :
    ∀ c ∈ coeffFamily K m, mCount m (traceHyperplane u₀) c = 2 ^ ((m - 1) * n - m) :=
  mTupleCount_odd_of_mPhase_nonneg hn hm3 hm _ hcard
    (card_traceHyperplane (by omega) hcard hu₀) (mPhase_traceHyperplane_nonneg u₀)

/-- The same for every affine hyperplane `H(u₀) + b`. -/
theorem mTupleCount_odd_traceHyperplane_coset {n m : ℕ} (hn : 2 ≤ n) (hm3 : 3 ≤ m)
    (hm : Odd m) (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (b : K) :
    ∀ c ∈ coeffFamily K m,
      mCount m ((traceHyperplane u₀).image (fun v => v + b)) c = 2 ^ ((m - 1) * n - m) := by
  have hcardH : ((traceHyperplane u₀).image (fun v => v + b)).card = 2 ^ (n - 1) := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using add_right_cancel h)]
    exact card_traceHyperplane (by omega) hcard hu₀
  exact mTupleCount_odd_affine_coset hn hm3 hm _ (traceHyperplane_add_mem u₀) b hcard hcardH

/-- Non-vacuity in the positive direction: there **is** a half-size set whose
phase is non-negative at every admissible coefficient vector, for every tuple
length. -/
theorem exists_half_size_mPhase_nonneg {n m : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) :
    ∃ S : Finset K, S.card = 2 ^ (n - 1) ∧ ∀ c ∈ coeffFamily K m, 0 ≤ mPhase m S c := by
  have hone : (1 : K) ≠ 0 := one_ne_zero
  exact ⟨traceHyperplane 1, card_traceHyperplane (by omega) hcard hone,
    mPhase_traceHyperplane_nonneg 1⟩


end MTuple
