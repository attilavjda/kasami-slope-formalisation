import KasamiCyclicAdditive
import MTupleExt.KasamiMTuple

/-!
# Transporting the completed `m = 3` theorem into the `m`-tuple frame

The `m`-tuple library proves the Kasami statement on its own only for
`k ≡ ±1 (mod n)`, because the mechanism that discharges its positivity
hypothesis (a sign factorisation of the Walsh transform) reaches exactly the
affine trace hyperplanes.  The completed `m = 3` theorem
(`KasamiCyclicAdditive.carlet_kasami_cyclic_additive_literature`, proved in
the `KasamiCyclicAdditive` dependency) discharges the very same hypothesis at `m = 3` for *every* `k` coprime
to `n`, by a different route: the Fermat-cubic root-existence input
(`KasamiCyclicAdditive.rootEquationSolvable`), which is the link that completed
the `m = 3` proof, gives pointwise non-negativity of the third phase moment at
every admissible slope, and the exact slope average then forces equality.

This module makes that transfer machine-checked.  It contains no new
mathematics: it identifies the two statement surfaces and reads the completed
theorem as a statement about `mCount` and `mPhase`.

* `coefficientTripleCount_eq_mCount` — the two surfaces count the same thing;
* `kasamiMTupleConjecture_three_of_coprime` — `KasamiMTupleConjecture K n k 3`
  holds for every `k` coprime to `n` (not only for `k ≡ ±1 (mod n)`);
* `mPhase_three_kasamiDelta_eq_zero` / `mPhase_three_kasamiDelta_nonneg` — the
  phase input of the odd-`m` machinery, discharged at `m = 3` for every such `k`.

Nothing here extends to `m ≥ 5`: `MTuple.exists_generic_three_not_five` exhibits
a half-size set that is generic at every admissible `3`-vector and not generic
at an admissible `5`-vector, so the `m = 3` conclusion is strictly weaker than
the `m = 5` one.
-/

open Finset

namespace MTuple

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ## The two statement surfaces agree -/

/-- `4^k − 2^k + 1 = 2^{2k} − 2^k + 1`. -/
theorem kasamiExponent_eq_kasamiExp (k : ℕ) :
    KasamiCyclicAdditive.kasamiExponent k = kasamiExp k := by
  have h : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [KasamiCyclicAdditive.kasamiExponent, kasamiExp, h]

omit [CharP K 2] in
/-- The derivative image of the `KasamiCyclicAdditive` surface is the library's `Δ`. -/
theorem derivativeImage_eq_kasamiDelta (k : ℕ) :
    KasamiCyclicAdditive.derivativeImage k K = kasamiDelta K (kasamiExp k) := by
  rw [KasamiCyclicAdditive.derivativeImage, kasamiDelta]
  refine Finset.image_congr fun b _ => ?_
  rw [KasamiCyclicAdditive.kasamiDerivative, kasamiExponent_eq_kasamiExp]
  ring

omit [CharP K 2] in
/-- The registered triple count is the library's `3`-tuple count at the
admissible vector `(v₁, v₂, v₁+v₂)`. -/
theorem coefficientTripleCount_eq_mCount (k : ℕ) (v₁ v₂ : K) :
    KasamiCyclicAdditive.coefficientTripleCount k v₁ v₂
      = mCount 3 (kasamiDelta K (kasamiExp k)) ![v₁, v₂, v₁ + v₂] := by
  rw [← tripleCount_eq_mCount, KasamiCyclicAdditive.coefficientTripleCount, tripleCount,
    derivativeImage_eq_kasamiDelta]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_assoc]

/-! ## Admissible `3`-vectors are exactly the Carlet coefficient triples -/

/-- An admissible coefficient vector of length `3` has the shape
`(v₁, v₂, v₁+v₂)` with `v₁, v₂` nonzero and distinct. -/
theorem coeffFamily_three_repr {c : Fin 3 → K} (hc : c ∈ coeffFamily K 3) :
    c 0 ≠ 0 ∧ c 1 ≠ 0 ∧ c 0 ≠ c 1 ∧ c = ![c 0, c 1, c 0 + c 1] := by
  rw [mem_coeffFamily] at hc
  obtain ⟨hne, hsum⟩ := hc
  rw [Fin.sum_univ_three] at hsum
  have h2 : c 2 = c 0 + c 1 := by
    exact (CharTwo.add_eq_zero.1 hsum).symm
  refine ⟨hne 0, hne 1, ?_, ?_⟩
  · intro h01
    refine hne 2 ?_
    rw [h2, h01]
    exact CharTwo.add_self_eq_zero _
  · funext i
    fin_cases i <;> simp [h2]

/-! ## The completed `m = 3` theorem, read in the `m`-tuple frame -/

/-- **The `m`-tuple statement at `m = 3`, for every `k` coprime to `n`.**  This
is the completed `m = 3` theorem of the `KasamiCyclicAdditive` dependency, transported verbatim: the
`3`-tuple count of the Kasami derivative image is the generic value
`2^{2n−3}` at every admissible coefficient vector. -/
theorem kasamiMTupleConjecture_three_of_coprime {n k : ℕ}
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n) :
    KasamiMTupleConjecture K n k 3 := by
  intro c hc
  obtain ⟨h0, h1, h01, hceq⟩ := coeffFamily_three_repr hc
  have hmain :=
    KasamiCyclicAdditive.carlet_kasami_cyclic_additive_literature (K := K) hkn hcard h0 h1 h01
  rw [coefficientTripleCount_eq_mCount] at hmain
  rw [show ((3 : ℕ) - 1) * n - 3 = 2 * n - 3 by omega]
  conv_lhs => rw [hceq]
  exact hmain

/-- The Kasami derivative image is half-size for every `k` coprime to `n`
(`KasamiCyclicAdditive`'s Müller–Cohen–Matthews input, after the reduction `k ↦ k % n`). -/
theorem card_kasamiDelta_of_coprime {n k : ℕ} (hn : 2 ≤ n)
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n) :
    (kasamiDelta K (kasamiExp k)).card = 2 ^ (n - 1) := by
  obtain ⟨hpos, hlt, hcop⟩ := KasamiCyclicAdditive.mod_parameter_admissible hn hkn
  have hhalf : 2 * (KasamiCyclicAdditive.derivativeImage (k % n) K).card = Fintype.card K :=
    KasamiCyclicAdditive.kasami_half_size hpos hlt hcop hcard
  rw [← KasamiCyclicAdditive.derivativeImage_mod_degree (K := K) (n := n) (k := k) hcard,
    derivativeImage_eq_kasamiDelta, hcard] at hhalf
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    ring
  omega

/-- **The phase input of the odd-`m` machinery, discharged at `m = 3` for every
`k` coprime to `n`.**  This is what the completed `m = 3` proof contributes to
the `m`-tuple frame: the third phase moment of the Kasami derivative image
vanishes at every admissible coefficient vector, with no congruence restriction
on `k`. -/
theorem mPhase_three_kasamiDelta_eq_zero {n k : ℕ} (hn : 2 ≤ n)
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n)
    {c : Fin 3 → K} (hc : c ∈ coeffFamily K 3) :
    mPhase 3 (kasamiDelta K (kasamiExp k)) c = 0 :=
  (mCount_generic_iff_mPhase_eq_zero (n := n) hn (by norm_num) _ hcard
      (card_kasamiDelta_of_coprime hn hkn hcard) c).1
    (kasamiMTupleConjecture_three_of_coprime hkn hcard c hc)

/-- The same statement in the exact form in which the odd-`m` theorem
`mTupleCount_odd_of_mPhase_nonneg` consumes it. -/
theorem mPhase_three_kasamiDelta_nonneg {n k : ℕ} (hn : 2 ≤ n)
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n) :
    ∀ c ∈ coeffFamily K 3, 0 ≤ mPhase 3 (kasamiDelta K (kasamiExp k)) c := fun _ hc =>
  le_of_eq (mPhase_three_kasamiDelta_eq_zero hn hkn hcard hc).symm

/-- The original triple statement, recovered from the transported `m`-tuple
form. -/
theorem kasamiTripleConjecture_of_coprime {n k : ℕ}
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n) :
    KasamiTripleConjecture K n k :=
  kasamiTripleConjecture_of_KasamiMTupleConjecture
    (kasamiMTupleConjecture_three_of_coprime hkn hcard)

end MTuple
