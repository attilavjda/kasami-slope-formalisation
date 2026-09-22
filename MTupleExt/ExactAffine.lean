import MTuple.Rigidity

/-!
# The exact `m`-tuple count of an affine trace hyperplane

`MTuple/MTuple/` proves two one-sided statements about the `m`-tuple
count of a half-size set `S ⊆ K`, `|K| = 2ⁿ`:

* for **odd** `m` and a set with a sign factorisation the count is the generic
  value `2^{(m−1)n−m}` at every admissible coefficient vector;
* for **even** `m` the generic count must fail somewhere, and it does fail at the
  constant coefficient vectors.

By `MTuple.sign_factorization_iff_affine_trace_hyperplane`, the sets reached by
the mechanism are exactly the affine trace hyperplanes `{y : Tr(u₀y) = d}`.  For
*those* sets this file computes the count **exactly, for every `m`**:

`mCount m S c = 2^{(m−1)n−m} + (2^{(n−1)m−n} if c is constant, 0 otherwise)`.

So on the whole range of the mechanism the deviation from the generic value is
completely localised: it happens at the constant coefficient vectors and nowhere
else, and there it is exactly `2^{(n−1)m−n}`.  Since a constant admissible vector
exists only for even `m`, this single formula contains both one-sided statements
of the library and sharpens the even one from an inequality to an equality.

Main results:

* `Tsum_affineTraceHyperplane_eq_zero`, `Tsum_affineTraceHyperplane_self` — the
  transform of an affine trace hyperplane is supported on `{0, u₀}`;
* `mPhase_affineTraceHyperplane_of_not_const`,
  `mPhase_affineTraceHyperplane_const` — the phase, exactly;
* `mCount_affineTraceHyperplane_of_not_const`,
  `mCount_affineTraceHyperplane_const` — the count, exactly;
* `mCount_addClosed_of_not_const`, `mCount_addClosed_const` — the same for an
  arbitrary half-size additive subgroup, via the rigidity theorem.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## The transform of an affine trace hyperplane -/

/-- The sign attached to a class `d ∈ 𝔽₂`: `+1` for `0`, `−1` for `1`. -/
def sgnZ (d : ZMod 2) : ℤ := if d = 0 then 1 else -1

theorem sgnZ_mul_self (d : ZMod 2) : sgnZ d * sgnZ d = 1 := by
  by_cases h : d = 0 <;> simp [sgnZ, h]

omit [Fintype K] [DecidableEq K] in
theorem chiZ_eq_sgnZ_trace (x : K) : chiZ x = sgnZ (Algebra.trace (ZMod 2) K x) := by
  by_cases h : Algebra.trace (ZMod 2) K x = 0 <;> simp [chiZ, sgnZ, h]

theorem sgnZ_ne_of_ne {d e : ZMod 2} (h : d ≠ e) : sgnZ d = -sgnZ e := by
  revert h; revert d e; decide

/-- **The transform of an affine trace hyperplane.**  Doubling avoids a division:
`2·T̂_{H(u₀,d)}(u) = |K|·[u = 0] + sgn(d)·|K|·[u = u₀]`. -/
theorem two_mul_Tsum_affineTraceHyperplane (u₀ : K) (d : ZMod 2) (u : K) :
    2 * Tsum (affineTraceHyperplane u₀ d) u
      = (if u = 0 then (Fintype.card K : ℤ) else 0)
        + sgnZ d * (if u = u₀ then (Fintype.card K : ℤ) else 0) := by
  have key : ∀ y : K,
      (if Algebra.trace (ZMod 2) K (u₀ * y) = d then (2 : ℤ) * chiZ (u * y) else 0)
        = chiZ (y * u) + sgnZ d * chiZ (y * (u + u₀)) := by
    intro y
    have hmul : chiZ (y * (u + u₀)) = chiZ (y * u) * chiZ (u₀ * y) := by
      rw [mul_add, chiZ_add, mul_comm y u₀]
    have hchi : chiZ (u₀ * y) = sgnZ (Algebra.trace (ZMod 2) K (u₀ * y)) :=
      chiZ_eq_sgnZ_trace _
    by_cases h : Algebra.trace (ZMod 2) K (u₀ * y) = d
    · rw [if_pos h, hmul, hchi, h, mul_comm u y]
      have hrw : sgnZ d * (chiZ (y * u) * sgnZ d) = chiZ (y * u) * (sgnZ d * sgnZ d) := by ring
      rw [hrw, sgnZ_mul_self]
      ring
    · rw [if_neg h, hmul, hchi, sgnZ_ne_of_ne h]
      have hrw : sgnZ d * (chiZ (y * u) * -sgnZ d)
          = -(chiZ (y * u) * (sgnZ d * sgnZ d)) := by ring
      rw [hrw, sgnZ_mul_self]
      ring
  have hsum : 2 * Tsum (affineTraceHyperplane u₀ d) u
      = ∑ y : K, (chiZ (y * u) + sgnZ d * chiZ (y * (u + u₀))) := by
    rw [← Finset.sum_congr rfl (fun y (_ : y ∈ (univ : Finset K)) => key y), Tsum,
      Finset.mul_sum, affineTraceHyperplane, Finset.sum_filter]
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_chiZ_mul, sum_chiZ_mul]
  congr 2
  exact if_congr CharTwo.add_eq_zero rfl rfl

/-- Off `{0, u₀}` the transform vanishes. -/
theorem Tsum_affineTraceHyperplane_eq_zero (u₀ : K) (d : ZMod 2) {u : K}
    (h0 : u ≠ 0) (h1 : u ≠ u₀) : Tsum (affineTraceHyperplane u₀ d) u = 0 := by
  have h := two_mul_Tsum_affineTraceHyperplane u₀ d u
  rw [if_neg h0, if_neg h1, mul_zero, add_zero] at h
  linarith

/-- The cardinality of an affine trace hyperplane: `2^{n−1}` for `u₀ ≠ 0`. -/
theorem card_affineTraceHyperplane {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2) :
    (affineTraceHyperplane u₀ d).card = 2 ^ (n - 1) := by
  have h := two_mul_Tsum_affineTraceHyperplane u₀ d (0 : K)
  rw [if_pos rfl, if_neg (Ne.symm hu₀), mul_zero, add_zero, Tsum_zero, hcard] at h
  push_cast at h
  have hsplit : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsplit] at h
  have hc : ((affineTraceHyperplane u₀ d).card : ℤ) = 2 ^ (n - 1) := by linarith
  exact_mod_cast hc

/-- At `u₀` itself the transform is `±2^{n−1}`. -/
theorem Tsum_affineTraceHyperplane_self {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2) :
    Tsum (affineTraceHyperplane u₀ d) u₀ = sgnZ d * 2 ^ (n - 1) := by
  have h := two_mul_Tsum_affineTraceHyperplane u₀ d u₀
  rw [if_neg hu₀, if_pos rfl, hcard] at h
  push_cast at h
  have hsplit : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsplit] at h
  linarith

/-! ## The phase of an affine trace hyperplane, exactly -/

/-- **Non-constant coefficient vectors: the phase vanishes.**  No parity
assumption on `m`. -/
theorem mPhase_affineTraceHyperplane_of_not_const {m : ℕ} {u₀ : K} (d : ZMod 2)
    {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hne : ¬ ∀ i j, c i = c j) :
    mPhase m (affineTraceHyperplane u₀ d) c = 0 := by
  rw [mem_coeffFamily] at hc
  refine Finset.sum_eq_zero fun t ht => ?_
  have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
  by_contra hprod
  have hall : ∀ i, Tsum (affineTraceHyperplane u₀ d) (t * c i) ≠ 0 := by
    intro i hi
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have heq : ∀ i, t * c i = u₀ := by
    intro i
    by_contra h
    exact hall i (Tsum_affineTraceHyperplane_eq_zero u₀ d (mul_ne_zero ht0 (hc.1 i)) h)
  exact hne fun i j => mul_left_cancel₀ ht0 ((heq i).trans (heq j).symm)

/-- **Constant coefficient vectors: the phase is exactly `2^{(n−1)m}`.**  (A
constant admissible vector forces `m` even, and then the sign `sgn(d)` drops
out, so the answer does not depend on which of the two parallel hyperplanes is
taken.) -/
theorem mPhase_affineTraceHyperplane_const {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2)
    {a : K} {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hconst : ∀ i, c i = a) :
    mPhase m (affineTraceHyperplane u₀ d) c = 2 ^ ((n - 1) * m) := by
  rw [mem_coeffFamily] at hc
  have ha : a ≠ 0 := by
    have h := hc.1 ⟨0, by omega⟩
    rwa [hconst] at h
  -- a constant admissible vector forces `m` even
  have hmeven : Even m := by
    have hsum : ((m : ℕ) : K) * a = 0 := by
      have hs : ∑ i, c i = ((m : ℕ) : K) * a := by
        rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [← hs, hc.2]
    have hm0 : ((m : ℕ) : K) = 0 := (mul_eq_zero.1 hsum).resolve_right ha
    exact even_iff_two_dvd.2 ((CharP.cast_eq_zero_iff K 2 m).1 hm0)
  set t₀ : K := u₀ * a⁻¹ with ht₀
  have ht₀0 : t₀ ≠ 0 := mul_ne_zero hu₀ (inv_ne_zero ha)
  have ht₀a : t₀ * a = u₀ := by
    rw [ht₀, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  rw [mPhase]
  refine (Finset.sum_eq_single_of_mem t₀ (Finset.mem_erase.2 ⟨ht₀0, Finset.mem_univ _⟩)
    ?_).trans ?_
  · -- every other nonzero `t` contributes `0`
    intro t ht htne
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) ?_
    refine Tsum_affineTraceHyperplane_eq_zero u₀ d ?_ ?_
    · rw [hconst]; exact mul_ne_zero ht0 ha
    · rw [hconst]
      intro h
      exact htne (mul_right_cancel₀ ha (by rw [h, ht₀a]))
  · have hfac : ∀ i : Fin m, Tsum (affineTraceHyperplane u₀ d) (t₀ * c i)
        = sgnZ d * 2 ^ (n - 1) := by
      intro i
      rw [hconst i, ht₀a]
      exact Tsum_affineTraceHyperplane_self hn hcard hu₀ d
    obtain ⟨k, hk⟩ := hmeven
    have hsgn : sgnZ d ^ m = 1 := by
      have hrw : sgnZ d ^ m = (sgnZ d * sgnZ d) ^ k := by rw [hk, pow_add, mul_pow]
      rw [hrw, sgnZ_mul_self, one_pow]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, hsgn, one_mul, ← pow_mul]

/-! ## The count of an affine trace hyperplane, exactly -/

/-- Exponent bookkeeping: `n + ((n−1)m − n) = (n−1)m` for `n, m ≥ 2`. -/
theorem exp_arith' {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    n + ((n - 1) * m - n) = (n - 1) * m := by
  have h : n ≤ (n - 1) * m := by
    have h1 : (n - 1) * 2 ≤ (n - 1) * m := Nat.mul_le_mul_left _ hm
    omega
  omega

/-- **The count at a non-constant admissible vector is exactly generic**, for
*every* `m ≥ 2` — odd or even. -/
theorem mCount_affineTraceHyperplane_of_not_const {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2)
    {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hne : ¬ ∀ i j, c i = c j) :
    mCount m (affineTraceHyperplane u₀ d) c = 2 ^ ((m - 1) * n - m) :=
  mCount_generic_of_mPhase_eq_zero hn hm _ hcard
    (card_affineTraceHyperplane (by omega) hcard hu₀ d) c
    (mPhase_affineTraceHyperplane_of_not_const d hc hne)

/-- **The count at a constant admissible vector exceeds the generic value by
exactly `2^{(n−1)m−n}`.** -/
theorem mCount_affineTraceHyperplane_const {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2)
    {a : K} {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hconst : ∀ i, c i = a) :
    (mCount m (affineTraceHyperplane u₀ d) c : ℤ)
      = 2 ^ ((m - 1) * n - m) + 2 ^ ((n - 1) * m - n) := by
  have hS := card_affineTraceHyperplane (n := n) (by omega) hcard hu₀ d
  have hkey := card_mul_mDeficiency_eq_mPhase (K := K) (n := n) (m := m) hn hm _ hcard hS c
  rw [mPhase_affineTraceHyperplane_const (by omega) (by omega) hcard hu₀ d hc hconst,
    mDeficiency, hcard] at hkey
  push_cast at hkey
  have hpow : (2 : ℤ) ^ n * 2 ^ ((n - 1) * m - n) = 2 ^ ((n - 1) * m) := by
    rw [← pow_add, exp_arith' hn hm]
  have hne : (2 : ℤ) ^ n ≠ 0 := by positivity
  have hcancel : (mCount m (affineTraceHyperplane u₀ d) c : ℤ) - 2 ^ ((m - 1) * n - m)
      = 2 ^ ((n - 1) * m - n) :=
    mul_left_cancel₀ hne (by rw [hkey, hpow])
  linarith

/-! ## The same for an arbitrary half-size additive subgroup -/

/-- A half-size additive subgroup *is* an affine trace hyperplane: this is the
rigidity theorem applied with the trivial sign. -/
theorem exists_affineTraceHyperplane_of_addClosed {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (hV : V.card = 2 ^ (n - 1)) :
    ∃ u₀ : K, u₀ ≠ 0 ∧ ∃ d : ZMod 2, V = affineTraceHyperplane u₀ d :=
  affine_of_signFactorization hn hcard hV (eps := fun _ => 1) (w := Tsum V)
    (fun u => (one_mul _).symm) (Tsum_addClosed_nonneg V hVadd) rfl
    (fun _ _ => by norm_num)

/-- **Half-size additive subgroup, non-constant vector: exactly the generic
count**, for every `m ≥ 2`. -/
theorem mCount_addClosed_of_not_const {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (hV : V.card = 2 ^ (n - 1))
    {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hne : ¬ ∀ i j, c i = c j) :
    mCount m V c = 2 ^ ((m - 1) * n - m) := by
  obtain ⟨u₀, hu₀, d, hVeq⟩ :=
    exists_affineTraceHyperplane_of_addClosed (by omega) hcard V hVadd hV
  rw [hVeq]
  exact mCount_affineTraceHyperplane_of_not_const hn hm hcard hu₀ d hc hne

/-- **Half-size additive subgroup, constant vector: the count exceeds the generic
value by exactly `2^{(n−1)m−n}`.** -/
theorem mCount_addClosed_const {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (hV : V.card = 2 ^ (n - 1))
    {a : K} {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hconst : ∀ i, c i = a) :
    (mCount m V c : ℤ) = 2 ^ ((m - 1) * n - m) + 2 ^ ((n - 1) * m - n) := by
  obtain ⟨u₀, hu₀, d, hVeq⟩ :=
    exists_affineTraceHyperplane_of_addClosed (by omega) hcard V hVadd hV
  rw [hVeq]
  exact mCount_affineTraceHyperplane_const hn hm hcard hu₀ d hc hconst

/-! ## The dichotomy in its sharpest form

The two exponents coincide: `(n−1)m − n = (m−1)n − m`, both being `mn − m − n`.
So the excess at a constant coefficient vector is *exactly one more copy* of the
generic value: on an affine trace hyperplane the `m`-tuple count is generic at
every non-constant admissible vector and exactly **twice** generic at every
constant one.  Constant admissible vectors exist only for even `m`
(`not_const_of_odd`), which is why the odd case is uniformly generic.
-/

/-- `(n−1)m − n = (m−1)n − m` for `n, m ≥ 2`; both sides are `mn − m − n`. -/
theorem exp_symm {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (n - 1) * m - n = (m - 1) * n - m := by
  have h1 : (n - 1) * m = n * m - m := by rw [Nat.sub_one_mul]
  have h2 : (m - 1) * n = n * m - n := by rw [Nat.sub_one_mul, mul_comm]
  have hge : m + n ≤ n * m := by nlinarith
  omega

/-- For odd `m` an admissible coefficient vector is never constant. -/
theorem not_const_of_odd {m : ℕ} (hm : Odd m) {c : Fin m → K}
    (hc : c ∈ coeffFamily K m) : ¬ ∀ i j, c i = c j := by
  rw [mem_coeffFamily] at hc
  intro hconst
  have hm1 : 1 ≤ m := hm.pos
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  have ha : c i0 ≠ 0 := hc.1 i0
  have hs : ∑ i, c i = ((m : ℕ) : K) * c i0 := by
    rw [Finset.sum_congr rfl fun i _ => hconst i i0, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hm0 : ((m : ℕ) : K) = 0 := by
    have := hc.2
    rw [hs] at this
    exact (mul_eq_zero.1 this).resolve_right ha
  have hdvd : (2 : ℕ) ∣ m := (CharP.cast_eq_zero_iff K 2 m).1 hm0
  rw [Nat.odd_iff] at hm
  omega

/-- **Constant vector: exactly twice the generic count.** -/
theorem mCount_affineTraceHyperplane_const_eq_two_mul {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2)
    {a : K} {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hconst : ∀ i, c i = a) :
    mCount m (affineTraceHyperplane u₀ d) c = 2 * 2 ^ ((m - 1) * n - m) := by
  have h := mCount_affineTraceHyperplane_const hn hm hcard hu₀ d hc hconst
  rw [exp_symm hn hm] at h
  have h2 : (mCount m (affineTraceHyperplane u₀ d) c : ℤ) = 2 * 2 ^ ((m - 1) * n - m) := by
    rw [h]; ring
  exact_mod_cast h2

/-- **Odd `m`, affine trace hyperplane: the generic count, with no averaging
argument.**  For odd `m` no admissible vector is constant, so the exact formula
gives the generic value directly. -/
theorem mCount_affineTraceHyperplane_odd {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hodd : Odd m)
    (hcard : Fintype.card K = 2 ^ n) {u₀ : K} (hu₀ : u₀ ≠ 0) (d : ZMod 2)
    {c : Fin m → K} (hc : c ∈ coeffFamily K m) :
    mCount m (affineTraceHyperplane u₀ d) c = 2 ^ ((m - 1) * n - m) :=
  mCount_affineTraceHyperplane_of_not_const hn hm hcard hu₀ d hc (not_const_of_odd hodd hc)

/-- **Half-size additive subgroup, constant vector: exactly twice the generic
count.** -/
theorem mCount_addClosed_const_eq_two_mul {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card K = 2 ^ n) (V : Finset K)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) (hV : V.card = 2 ^ (n - 1))
    {a : K} {c : Fin m → K} (hc : c ∈ coeffFamily K m) (hconst : ∀ i, c i = a) :
    mCount m V c = 2 * 2 ^ ((m - 1) * n - m) := by
  obtain ⟨u₀, hu₀, d, hVeq⟩ :=
    exists_affineTraceHyperplane_of_addClosed (by omega) hcard V hVadd hV
  rw [hVeq]
  exact mCount_affineTraceHyperplane_const_eq_two_mul hn hm hcard hu₀ d hc hconst

end MTuple
