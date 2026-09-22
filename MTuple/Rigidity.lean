import MTuple.SignFactorization

/-!
# How rigid is the sign-factorisation mechanism?

`MTuple/MTuple/SignFactorization.lean` discharges the odd-`m` phase
hypothesis without assuming it whenever the transform has a *sign factorisation*

  `T̂_S(u) = ε(u)·w(u)`,  `w ≥ 0`,  `ε(0) = 1`,  `ε(u+v) = ε(u)·ε(v)`,

and shows every half-size coset of an additive subgroup has one.  How much more
can the mechanism reach?  The answer proved here is: **nothing more**.

> **`sign_factorization_iff_affine_trace_hyperplane`.**  For a half-size `S` in a
> field with `2ⁿ` elements (`n ≥ 1`), a sign factorisation of `T̂_S` exists *iff*
> `S = { y : Tr(u₀ y) = d }` for some `u₀ ≠ 0` and some `d ∈ 𝔽₂` — that is, iff
> `S` is an affine hyperplane.

So the mechanism covers exactly the affine (Gold-type) case, and it can never be
instantiated at a set that fails the phase hypothesis: the half-size subset of
`GF(16)` of `MTuple/MTuple/Counterexample.lean` fails that hypothesis at
`m = 3`, and by the theorem above it could not have had a sign factorisation in
the first place.

The proof of the hard direction is spectral and elementary:

* a `±1`-valued additive character sums to `|K|` or to `0` (`sum_pm_character`);
* hence `∑_u w(u) = |K|·#{y ∈ S : ε = χ(· y)} ≤ |K|` (`sum_w_le_card`);
* Parseval gives `∑_u w(u)² = |K|·|S| = 2^{2n−1}` (`sum_Tsum_sq`), and
  `w ≤ |S| = 2^{n−1}` forces `∑_u w(u) ≥ 2ⁿ`;
* equality therefore holds throughout, so `w` takes only the values `0` and
  `2^{n−1}`, at exactly two frequencies `0` and `u₀`;
* Fourier inversion then reads off `S = { y : χ(u₀ y) = ε(u₀) }`.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## §0  The predicate -/

/-- `S` admits a *sign factorisation*: `T̂_S = ε·w` with `w ≥ 0` and `ε` an
additive character (necessarily `±1`-valued). -/
def HasSignFactorization (S : Finset K) : Prop :=
  ∃ eps w : K → ℤ, (∀ u, Tsum S u = eps u * w u) ∧ (∀ u, 0 ≤ w u) ∧ eps 0 = 1 ∧
    ∀ u v, eps (u + v) = eps u * eps v

/-- The affine trace hyperplane `{ y : Tr(u₀ y) = d }`. -/
noncomputable def affineTraceHyperplane (u₀ : K) (d : ZMod 2) : Finset K :=
  univ.filter (fun y => Algebra.trace (ZMod 2) K (u₀ * y) = d)

omit [DecidableEq K] in
theorem mem_affineTraceHyperplane {u₀ y : K} {d : ZMod 2} :
    y ∈ affineTraceHyperplane u₀ d ↔ Algebra.trace (ZMod 2) K (u₀ * y) = d := by
  simp [affineTraceHyperplane]

omit [DecidableEq K] in
theorem affineTraceHyperplane_zero (u₀ : K) :
    affineTraceHyperplane u₀ 0 = traceHyperplane u₀ := rfl

/-! ## §1  Elementary facts about `chiZ` and `Tsum` -/

omit [Fintype K] [DecidableEq K] in
theorem chiZ_eq_one_or_neg_one (x : K) : chiZ x = 1 ∨ chiZ x = -1 := by
  unfold chiZ
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype K] [DecidableEq K] in
theorem chiZ_eq_one_iff (x : K) : chiZ x = 1 ↔ Algebra.trace (ZMod 2) K x = 0 := by
  have h : ∀ t : ZMod 2, ((if t = 0 then (1 : ℤ) else -1) = 1) ↔ t = 0 := by decide
  simp [chiZ, h (Algebra.trace (ZMod 2) K x)]

omit [Fintype K] [DecidableEq K] in
theorem chiZ_eq_neg_one_iff (x : K) : chiZ x = -1 ↔ Algebra.trace (ZMod 2) K x = 1 := by
  have h : ∀ t : ZMod 2, ((if t = 0 then (1 : ℤ) else -1) = -1) ↔ t = 1 := by decide
  simpa [chiZ] using h (Algebra.trace (ZMod 2) K x)

omit [Fintype K] [DecidableEq K] in
theorem Tsum_le_card (S : Finset K) (u : K) : Tsum S u ≤ (S.card : ℤ) := by
  calc Tsum S u = ∑ y ∈ S, chiZ (u * y) := rfl
    _ ≤ ∑ _y ∈ S, (1 : ℤ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rcases chiZ_eq_one_or_neg_one (u * y) with h | h <;> simp [h]
    _ = (S.card : ℤ) := by simp

omit [Fintype K] [DecidableEq K] in
theorem neg_card_le_Tsum (S : Finset K) (u : K) : -(S.card : ℤ) ≤ Tsum S u := by
  have h : -Tsum S u ≤ (S.card : ℤ) := by
    calc -Tsum S u = ∑ y ∈ S, -chiZ (u * y) := by rw [Finset.sum_neg_distrib]; rfl
      _ ≤ ∑ _y ∈ S, (1 : ℤ) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rcases chiZ_eq_one_or_neg_one (u * y) with h | h <;> simp [h]
      _ = (S.card : ℤ) := by simp
  linarith

/-- **Parseval.**  `∑_u T̂_S(u)² = |K|·|S|`. -/
theorem sum_Tsum_sq (S : Finset K) :
    ∑ u : K, (Tsum S u) ^ 2 = (Fintype.card K : ℤ) * S.card := by
  have hexp : ∀ u : K, (Tsum S u) ^ 2
      = ∑ y ∈ S, ∑ z ∈ S, chiZ (u * (y + z)) := by
    intro u
    rw [sq, Tsum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by
      rw [mul_add, chiZ_add]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ y ∈ S, ∑ u : K, ∑ z ∈ S, chiZ (u * (y + z))
      = (Fintype.card K : ℤ) := by
    intro y hy
    rw [Finset.sum_comm]
    have h1 : ∀ z ∈ S, ∑ u : K, chiZ (u * (y + z))
        = if z = y then (Fintype.card K : ℤ) else 0 := by
      intro z _
      rw [sum_chiZ_mul]
      have hiff : (y + z = 0) ↔ (z = y) := by
        constructor
        · intro h; exact (CharTwo.add_eq_zero.1 h).symm
        · intro h; rw [h]; exact CharTwo.add_self_eq_zero y
      exact if_congr hiff rfl rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' S y, if_pos hy]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## §2  Sums of `±1`-valued additive characters -/

omit [DecidableEq K] in
/-- A `±1`-valued additive character sums to `|K|` if it is trivial and to `0`
otherwise. -/
theorem sum_pm_character (psi : K → ℤ) (h0 : psi 0 = 1)
    (hmul : ∀ u v, psi (u + v) = psi u * psi v) :
    ∑ u : K, psi u = if (∀ u : K, psi u = 1) then (Fintype.card K : ℤ) else 0 := by
  split
  · rename_i hall
    rw [Finset.sum_congr rfl fun u _ => hall u]
    simp
  · rename_i hnot
    push_neg at hnot
    obtain ⟨u₁, hu₁⟩ := hnot
    have hsq : psi u₁ * psi u₁ = 1 := by
      rw [← hmul, CharTwo.add_self_eq_zero, h0]
    have hneg : psi u₁ = -1 :=
      (Int.eq_one_or_neg_one_of_mul_eq_one hsq).resolve_left hu₁
    have hshift : ∑ u : K, psi (u + u₁) = ∑ u : K, psi u :=
      Fintype.sum_equiv (Equiv.addRight u₁) _ _ (fun _ => rfl)
    have hflip : ∑ u : K, psi (u + u₁) = - ∑ u : K, psi u := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ => by rw [hmul, hneg]; ring
    rw [hshift] at hflip
    linarith

/-! ## §3  The hard direction -/

section Rigidity

variable {S : Finset K} {eps w : K → ℤ}

omit [Fintype K] [DecidableEq K] in
/-- Under a sign factorisation, `ε` is `±1`-valued. -/
theorem eps_eq_one_or_neg_one (heps0 : eps 0 = 1) (heps : ∀ u v, eps (u + v) = eps u * eps v)
    (u : K) : eps u = 1 ∨ eps u = -1 := by
  have hsq : eps u * eps u = 1 := by rw [← heps, CharTwo.add_self_eq_zero, heps0]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hsq

/-- `∑_u w(u) ≤ |K|`: the weight sum is `|K|` times the number of `y ∈ S` at
which the character `ε` coincides with `χ(· y)`, and there is at most one such
`y`. -/
theorem sum_w_le_card (hfac : ∀ u, Tsum S u = eps u * w u)
    (heps0 : eps 0 = 1) (heps : ∀ u v, eps (u + v) = eps u * eps v) :
    ∑ u : K, w u ≤ (Fintype.card K : ℤ) := by
  classical
  have hsq : ∀ u : K, eps u * eps u = 1 := fun u => by
    rw [← heps, CharTwo.add_self_eq_zero, heps0]
  -- `w u = ε u · T̂(u)`
  have hw : ∀ u, w u = eps u * Tsum S u := by
    intro u
    calc w u = (eps u * eps u) * w u := by rw [hsq, one_mul]
      _ = eps u * (eps u * w u) := by ring
      _ = eps u * Tsum S u := by rw [hfac]
  -- swap the two summations
  have hswap : ∑ u : K, w u = ∑ y ∈ S, ∑ u : K, eps u * chiZ (u * y) := by
    simp_rw [hw, Tsum, Finset.mul_sum]
    rw [Finset.sum_comm]
  -- each inner sum is `|K|` or `0`
  set A : Finset K := S.filter (fun y => ∀ u : K, eps u * chiZ (u * y) = 1) with hA
  have hAsub : A ⊆ S := Finset.filter_subset _ _
  have hinner : ∀ y ∈ S, ∑ u : K, eps u * chiZ (u * y)
      = if y ∈ A then (Fintype.card K : ℤ) else 0 := by
    intro y hy
    have h := sum_pm_character (fun u => eps u * chiZ (u * y)) (by simp [heps0])
      (fun u v => by
        show eps (u + v) * chiZ ((u + v) * y) = eps u * chiZ (u * y) * (eps v * chiZ (v * y))
        rw [heps, add_mul, chiZ_add]; ring)
    rw [h]
    congr 1
    simp [hA, hy]
  -- at most one such `y`
  have hAcard : A.card ≤ 1 := by
    refine Finset.card_le_one.2 fun y hy z hz => ?_
    rw [hA, Finset.mem_filter] at hy hz
    have hchi : ∀ u : K, chiZ (u * (y + z)) = 1 := by
      intro u
      have h1 := hy.2 u
      have h2 := hz.2 u
      have h3 := hsq u
      have ha : chiZ (u * y) = eps u := by
        calc chiZ (u * y) = (eps u * eps u) * chiZ (u * y) := by rw [h3, one_mul]
          _ = eps u * (eps u * chiZ (u * y)) := by ring
          _ = eps u := by rw [h1, mul_one]
      have hb : chiZ (u * z) = eps u := by
        calc chiZ (u * z) = (eps u * eps u) * chiZ (u * z) := by rw [h3, one_mul]
          _ = eps u * (eps u * chiZ (u * z)) := by ring
          _ = eps u := by rw [h2, mul_one]
      have hyz : chiZ (u * y) = chiZ (u * z) := ha.trans hb.symm
      rw [mul_add, chiZ_add, hyz]
      rcases chiZ_eq_one_or_neg_one (u * z) with h | h <;> rw [h] <;> norm_num
    have hsum : ∑ u : K, chiZ (u * (y + z)) = (Fintype.card K : ℤ) := by
      rw [Finset.sum_congr rfl fun u _ => hchi u]
      simp
    rw [sum_chiZ_mul] at hsum
    by_cases hyz : y + z = 0
    · exact CharTwo.add_eq_zero.1 hyz
    · rw [if_neg hyz] at hsum
      exact absurd hsum.symm (card_pos_int (K := K)).ne'
  have hc : (A.card : ℤ) ≤ 1 := by exact_mod_cast hAcard
  rw [hswap, Finset.sum_congr rfl hinner, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 hAsub, Finset.sum_const, nsmul_eq_mul]
  nlinarith [card_pos_int (K := K)]

/-- **The hard direction.**  A half-size set with a sign factorisation is an
affine trace hyperplane. -/
theorem affine_of_signFactorization {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1))
    (hfac : ∀ u, Tsum S u = eps u * w u) (hw0 : ∀ u, 0 ≤ w u)
    (heps0 : eps 0 = 1) (heps : ∀ u v, eps (u + v) = eps u * eps v) :
    ∃ u₀ : K, u₀ ≠ 0 ∧ ∃ d : ZMod 2, S = affineTraceHyperplane u₀ d := by
  classical
  have hsplit : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  have hsq : ∀ u : K, eps u * eps u = 1 := fun u => by
    rw [← heps, CharTwo.add_self_eq_zero, heps0]
  -- `w = |T̂|`, in particular `w u ≤ 2^{n-1}` and `w 0 = 2^{n-1}`
  have hw : ∀ u, w u = eps u * Tsum S u := by
    intro u
    calc w u = (eps u * eps u) * w u := by rw [hsq, one_mul]
      _ = eps u * (eps u * w u) := by ring
      _ = eps u * Tsum S u := by rw [hfac]
  have hwsq : ∀ u, (w u) ^ 2 = (Tsum S u) ^ 2 := by
    intro u
    rw [hfac]
    nlinarith [hsq u]
  have hwle : ∀ u, w u ≤ 2 ^ (n - 1) := by
    intro u
    have h1 : Tsum S u ≤ (S.card : ℤ) := Tsum_le_card S u
    have h2 : -(S.card : ℤ) ≤ Tsum S u := neg_card_le_Tsum S u
    rw [hS] at h1 h2
    push_cast at h1 h2
    rcases eps_eq_one_or_neg_one heps0 heps u with h | h <;> rw [hw u, h] <;> linarith
  have hw0card : w 0 = 2 ^ (n - 1) := by
    rw [hw 0, heps0, one_mul, Tsum_zero, hS]
    push_cast
    ring
  -- Parseval and the two bounds on `∑ w`
  have hparseval : ∑ u : K, (w u) ^ 2 = 2 ^ n * 2 ^ (n - 1) := by
    rw [Finset.sum_congr rfl fun u _ => hwsq u, sum_Tsum_sq, hcard, hS]
    push_cast
    ring
  have hupper : ∑ u : K, w u ≤ 2 ^ n := by
    have h := sum_w_le_card hfac heps0 heps
    rw [hcard] at h
    push_cast at h
    exact h
  have hlower : (2 : ℤ) ^ n ≤ ∑ u : K, w u := by
    have hterm : ∀ u : K, (w u) ^ 2 ≤ 2 ^ (n - 1) * w u := by
      intro u
      nlinarith [hw0 u, hwle u]
    have h := Finset.sum_le_sum (fun u (_ : u ∈ (univ : Finset K)) => hterm u)
    rw [hparseval, ← Finset.mul_sum] at h
    nlinarith [h]
  have hsum : ∑ u : K, w u = 2 ^ n := le_antisymm hupper hlower
  -- equality forces `w u ∈ {0, 2^{n-1}}`
  have hzero : ∑ u : K, (2 ^ (n - 1) * w u - (w u) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hparseval]
    ring
  have hall : ∀ u : K, 2 ^ (n - 1) * w u - (w u) ^ 2 = 0 := by
    have hnn : ∀ u ∈ (univ : Finset K), 0 ≤ 2 ^ (n - 1) * w u - (w u) ^ 2 := by
      intro u _
      nlinarith [hw0 u, hwle u]
    intro u
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero u (Finset.mem_univ u)
  have hdich : ∀ u : K, w u = 0 ∨ w u = 2 ^ (n - 1) := by
    intro u
    have h := hall u
    have hfactor : w u * (2 ^ (n - 1) - w u) = 0 := by nlinarith [h]
    rcases mul_eq_zero.1 hfactor with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  -- the support of `w` has exactly two points
  set B : Finset K := univ.filter (fun u : K => w u = 2 ^ (n - 1)) with hB
  have hmemB : ∀ u : K, u ∈ B ↔ w u = 2 ^ (n - 1) := by
    intro u
    rw [hB, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hsumB : ∑ u : K, w u = (B.card : ℤ) * 2 ^ (n - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun u : K => w u = 2 ^ (n - 1))]
    have h1 : ∑ u ∈ univ.filter (fun u : K => w u = 2 ^ (n - 1)), w u
        = (B.card : ℤ) * 2 ^ (n - 1) := by
      rw [Finset.sum_congr rfl (fun u hu => (Finset.mem_filter.1 hu).2), Finset.sum_const,
        nsmul_eq_mul, hB]
    have h2 : ∑ u ∈ univ.filter (fun u : K => ¬ w u = 2 ^ (n - 1)), w u = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      rcases hdich u with h | h
      · exact h
      · exact absurd h (Finset.mem_filter.1 hu).2
    rw [h1, h2, add_zero]
  have hBcard : B.card = 2 := by
    have h := hsumB
    rw [hsum, hsplit] at h
    have hz : ((B.card : ℤ) - 2) * 2 ^ (n - 1) = 0 := by linarith
    rcases mul_eq_zero.1 hz with h' | h'
    · have : (B.card : ℤ) = 2 := by linarith
      exact_mod_cast this
    · exact absurd h' (by positivity)
  have hzeroB : (0 : K) ∈ B := (hmemB 0).2 hw0card
  obtain ⟨u₀, hu₀B, hu₀ne⟩ : ∃ u₀ ∈ B, u₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : B ⊆ {0} := fun u hu => Finset.mem_singleton.2 (hcon u hu)
    have := Finset.card_le_card hsub
    simp [hBcard] at this
  have hBeq : B = {0, u₀} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro u hu
      rcases Finset.mem_insert.1 hu with h | h
      · rw [h]; exact hzeroB
      · rw [Finset.mem_singleton.1 h]; exact hu₀B
    · rw [hBcard, Finset.card_pair (Ne.symm hu₀ne)]
  -- Fourier inversion supported on `{0, u₀}`
  have hTzero : ∀ u : K, u ∉ B → Tsum S u = 0 := by
    intro u hu
    have hwu : w u = 0 := by
      rcases hdich u with h | h
      · exact h
      · exact absurd ((hmemB u).2 h) hu
    rw [hfac, hwu, mul_zero]
  have hTu₀ : Tsum S u₀ = eps u₀ * 2 ^ (n - 1) := by
    rw [hfac, (hmemB u₀).1 hu₀B]
  have hinv : ∀ y : K, (if y ∈ S then (Fintype.card K : ℤ) else 0)
      = 2 ^ (n - 1) + eps u₀ * 2 ^ (n - 1) * chiZ (u₀ * y) := by
    intro y
    rw [← sum_Tsum_chiZ_univ S y]
    rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu => by rw [hTzero u hu, zero_mul])]
    rw [hBeq, Finset.sum_insert (by simpa using (Ne.symm hu₀ne)), Finset.sum_singleton]
    rw [hTu₀, Tsum_zero, hS]
    push_cast
    simp [chiZ, mul_comm]
  -- read off the set
  refine ⟨u₀, hu₀ne, if eps u₀ = 1 then 0 else 1, ?_⟩
  ext y
  have hy := hinv y
  rw [hcard] at hy
  push_cast at hy
  rw [hsplit] at hy
  constructor
  · intro hyS
    rw [if_pos hyS] at hy
    have hchi : eps u₀ * chiZ (u₀ * y) = 1 := by
      have hfactor : (eps u₀ * chiZ (u₀ * y) - 1) * 2 ^ (n - 1) = 0 := by nlinarith [hy]
      rcases mul_eq_zero.1 hfactor with h | h
      · linarith
      · exact absurd h (by positivity)
    rw [mem_affineTraceHyperplane]
    rcases eps_eq_one_or_neg_one heps0 heps u₀ with h | h
    · rw [if_pos h]
      rw [h, one_mul] at hchi
      exact (chiZ_eq_one_iff (u₀ * y)).1 hchi
    · rw [if_neg (by rw [h]; norm_num)]
      have hneg : chiZ (u₀ * y) = -1 := by
        rw [h] at hchi
        linarith
      exact (chiZ_eq_neg_one_iff (u₀ * y)).1 hneg
  · intro hyH
    rw [mem_affineTraceHyperplane] at hyH
    by_contra hyS
    rw [if_neg hyS] at hy
    have hchi : eps u₀ * chiZ (u₀ * y) = -1 := by
      have hfactor : (eps u₀ * chiZ (u₀ * y) + 1) * 2 ^ (n - 1) = 0 := by nlinarith [hy]
      rcases mul_eq_zero.1 hfactor with h | h
      · linarith
      · exact absurd h (by positivity)
    rcases eps_eq_one_or_neg_one heps0 heps u₀ with h | h
    · rw [if_pos h] at hyH
      rw [h, one_mul] at hchi
      have hzero1 := (chiZ_eq_neg_one_iff (u₀ * y)).1 hchi
      rw [hyH] at hzero1
      exact absurd hzero1 (by decide)
    · rw [if_neg (by rw [h]; norm_num)] at hyH
      have hone : chiZ (u₀ * y) = 1 := by
        rw [h] at hchi
        linarith
      have hzero0 := (chiZ_eq_one_iff (u₀ * y)).1 hone
      rw [hyH] at hzero0
      exact absurd hzero0 (by decide)

end Rigidity

/-! ## §4  The easy direction, and the characterisation -/

/-- Every affine trace hyperplane is a coset of the trace hyperplane. -/
theorem affineTraceHyperplane_eq_coset {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2) :
    ∃ b : K, affineTraceHyperplane u₀ d = (traceHyperplane u₀).image (fun v => v + b) := by
  classical
  obtain ⟨e, he⟩ := Algebra.trace_surjective (ZMod 2) K 1
  refine ⟨if d = 0 then 0 else u₀⁻¹ * e, ?_⟩
  have hval : Algebra.trace (ZMod 2) K (u₀ * (if d = 0 then 0 else u₀⁻¹ * e)) = d := by
    by_cases hd : d = 0
    · rw [if_pos hd, mul_zero, map_zero, hd]
    · rw [if_neg hd, ← mul_assoc, mul_inv_cancel₀ hu₀, one_mul, he]
      exact ((by decide : ∀ t : ZMod 2, t ≠ 0 → (1 : ZMod 2) = t) d hd)
  set b : K := if d = 0 then 0 else u₀⁻¹ * e with hb
  ext y
  rw [mem_affineTraceHyperplane, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨y + b, ?_, ?_⟩
    · rw [mem_traceHyperplane, mul_add, map_add, hy, hval]
      exact CharTwo.add_self_eq_zero d
    · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro ⟨v, hv, rfl⟩
    rw [mem_traceHyperplane] at hv
    rw [mul_add, map_add, hv, hval, zero_add]

/-- Every affine trace hyperplane has a sign factorisation. -/
theorem hasSignFactorization_affineTraceHyperplane {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2) :
    HasSignFactorization (affineTraceHyperplane u₀ d) := by
  obtain ⟨b, hb⟩ := affineTraceHyperplane_eq_coset hu₀ d
  refine ⟨fun u => chiZ (u * b), fun u => ∑ v ∈ traceHyperplane u₀, chiZ (u * v), ?_, ?_, ?_, ?_⟩
  · intro u
    rw [hb]
    exact Tsum_coset _ b u
  · exact fun u => subgroupCharSum_nonneg _ (traceHyperplane_add_mem u₀) u
  · simp
  · intro u v
    show chiZ ((u + v) * b) = chiZ (u * b) * chiZ (v * b)
    rw [add_mul, chiZ_add]

/-- **The sign-factorisation mechanism is exactly the affine case.**  For a
half-size `S` in a field with `2ⁿ` elements, a sign factorisation exists if and
only if `S` is an affine hyperplane `{ y : Tr(u₀ y) = d }`, `u₀ ≠ 0`.

Consequently the mechanism proves the odd-`m` generic count for Gold derivative
sets (which are affine hyperplanes) and for nothing beyond the affine family. -/
theorem sign_factorization_iff_affine_trace_hyperplane {n : ℕ} (hn : 1 ≤ n) (S : Finset K)
    (hcard : Fintype.card K = 2 ^ n) (hS : S.card = 2 ^ (n - 1)) :
    HasSignFactorization S ↔
      ∃ u₀ : K, u₀ ≠ 0 ∧ ∃ d : ZMod 2, S = affineTraceHyperplane u₀ d := by
  constructor
  · rintro ⟨eps, w, hfac, hw0, heps0, heps⟩
    exact affine_of_signFactorization hn hcard hS hfac hw0 heps0 heps
  · rintro ⟨u₀, hu₀, d, rfl⟩
    exact hasSignFactorization_affineTraceHyperplane hu₀ d

end MTuple
