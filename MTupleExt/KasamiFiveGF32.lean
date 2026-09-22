import MTuple.SplitCount
import MTuple.GF32
import MTupleExt.KasamiMTuple
import MTupleExt.Normalisation

/-!
# The `m = 5` Kasami statement is **false** for `n = 5, k = 2`

`MTuple/MTupleExt/KasamiMTuple.lean` proves the `m`-tuple statement for
every odd `m` in the residues `k ≡ ±1 (mod n)`, and
`MTuple/MTupleExt/M3Transfer.lean` proves it at `m = 3` for every `k`
coprime to `n`.  Whether the `m ≥ 5` statement survives in the *hard* residues
`k ≢ ±1 (mod n)` was left open; an exploratory script outside Lean suggested it
does not.  This file turns the first of those explorations into a
machine-checked refutation.

Working in the computable model `K32 = 𝔽₂[x]/(x⁵+x²+1)` of `GF(32)` and with
the Kasami exponent `d(2) = 2⁴ − 2² + 1 = 13` (so `n = 5`, `k = 2`, and
`k % n = 2 ∉ {1, 4}` — a hard residue, but `gcd(2,5) = 1`):

* `kasami52_card` — `|Δ| = 2⁴`, as it must be;
* `kasami52_three` — the `m = 3` conclusion **holds** (exhaustively over all
  admissible coefficient vectors, via the slope normalisation), confirming the
  transported `m = 3` theorem in this instance;
* `kasami52_mCount5` — at the admissible vector `c = (1, 1, x, x³+1, x³+x+1)`
  the `5`-tuple count is `32704`, not the generic `2^{(5−1)·5−5} = 32768`;
* `not_kasamiMTupleConjecture_five_gf32` — hence `KasamiMTupleConjecture K32 5 2 5`
  is false;
* `exists_injective_admissible_five_nongeneric_gf32` — the same with a
  coefficient vector whose entries are pairwise distinct, so the failure is not
  an artefact of repeated coefficients.

The `5`-tuple count is computed through the convolution formula
`MTuple.mCount_split_count`; a brute-force scan of `Δ⁵` (`16⁵ ≈ 10⁶` tuples)
would also be possible here, but the same code scales to `GF(128)` in
`MTuple/MTupleExt/KasamiFiveGF128.lean`, where brute force does not.
-/

open Finset MTuple.GF32Model MTuple.GF32Model.K32

namespace MTuple

/-- The Kasami derivative image `Δ(d(2))` in `GF(32)`, `d(2) = 13`. -/
def kasami52 : Finset K32 := kasamiDelta K32 (kasamiExp 2)

/-- The admissible `5`-vector `(1, 1, x, x³+1, x³+x+1)` (bit patterns
`1, 1, 2, 9, 11`). -/
def c52 : Fin 5 → K32 := ![ofNat 1, ofNat 1, ofNat 2, ofNat 9, ofNat 11]

set_option maxRecDepth 1000000 in
/-- `Δ` is half-size, as guaranteed by `card_kasamiDelta_of_coprime`. -/
theorem kasami52_card : kasami52.card = 2 ^ (5 - 1) := by decide +kernel

theorem c52_mem : c52 ∈ coeffFamily K32 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

/-! ## `m = 3`: the conclusion holds -/

set_option maxRecDepth 1000000 in
/-- Exhaustive check over the normalised slopes `(1, ρ, 1+ρ)`, `ρ ∉ {0,1}`: the
`3`-tuple count is always the generic `2^{2·5−3} = 128`. -/
theorem kasami52_mCount3_slope :
    ∀ r : K32, r ≠ 0 → r ≠ 1 → mCount 3 kasami52 ![1, r, 1 + r] = 128 := by decide +kernel

/-- **The `m = 3` statement holds for `n = 5, k = 2`** — an independent,
machine-checked confirmation of `kasamiMTupleConjecture_three_of_coprime` in
this instance. -/
theorem kasami52_three : KasamiMTupleConjecture K32 5 2 3 := by
  intro c hc
  obtain ⟨hr0, hr1⟩ := coeff_three_ratio_ne hc
  show mCount 3 kasami52 c = _
  rw [mCount_three_normalise kasami52 hc, kasami52_mCount3_slope _ hr0 hr1]
  norm_num

/-! ## `m = 5`: the conclusion fails -/

set_option maxRecDepth 1000000 in
/-- The `5`-tuple count at `c52`, computed by convolution: `32704`. -/
theorem kasami52_mCount5 : mCount 5 kasami52 c52 = 32704 := by
  refine (mCount_split_count 3 2 kasami52 c52).trans ?_
  have key :
      (let M : Multiset K32 := (Fintype.piFinset (fun _ : Fin 3 => kasami52)).val.map
          (fun x => ∑ i, c52 (Fin.castAdd 2 i) * x i)
       let N : Multiset K32 := (Fintype.piFinset (fun _ : Fin 2 => kasami52)).val.map
          (fun x => ∑ i, c52 (Fin.natAdd 3 i) * x i)
       ∑ z : K32, M.count z * N.count z) = 32704 := by decide +kernel
  exact key

/-- The count misses the generic value `2^{(5−1)·5−5} = 32768` by `64`. -/
theorem kasami52_mCount5_ne_generic : mCount 5 kasami52 c52 ≠ 2 ^ ((5 - 1) * 5 - 5) := by
  rw [kasami52_mCount5]
  norm_num

/-- **The `m = 5` Kasami `m`-tuple statement is false for `n = 5`, `k = 2`.**
The residue `k % n = 2` is a hard one (`k ≢ ±1 mod n`), and `gcd(k,n) = 1`, so
this is a genuine counterexample to extending the completed `m = 3` theorem to
`m = 5`. -/
theorem not_kasamiMTupleConjecture_five_gf32 : ¬ KasamiMTupleConjecture K32 5 2 5 := by
  intro h
  have hx := h c52 c52_mem
  rw [show kasamiDelta K32 (kasamiExp 2) = kasami52 from rfl, kasami52_mCount5] at hx
  norm_num at hx

/-! ## A witness with pairwise distinct entries -/

/-- The admissible `5`-vector `(1, x, x², x³, x³+x²+x+1)` (bit patterns
`1, 2, 4, 8, 15`), whose entries are pairwise distinct. -/
def c52inj : Fin 5 → K32 := ![ofNat 1, ofNat 2, ofNat 4, ofNat 8, ofNat 15]

theorem c52inj_mem : c52inj ∈ coeffFamily K32 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

theorem c52inj_injective : Function.Injective c52inj := by decide

set_option maxRecDepth 1000000 in
/-- Here the count is `32800`, i.e. `32` **above** the generic value. -/
theorem kasami52_mCount5_inj : mCount 5 kasami52 c52inj = 32800 := by
  refine (mCount_split_count 3 2 kasami52 c52inj).trans ?_
  have key :
      (let M : Multiset K32 := (Fintype.piFinset (fun _ : Fin 3 => kasami52)).val.map
          (fun x => ∑ i, c52inj (Fin.castAdd 2 i) * x i)
       let N : Multiset K32 := (Fintype.piFinset (fun _ : Fin 2 => kasami52)).val.map
          (fun x => ∑ i, c52inj (Fin.natAdd 3 i) * x i)
       ∑ z : K32, M.count z * N.count z) = 32800 := by decide +kernel
  exact key

/-- The failure is not an artefact of repeated coefficients: there is an
admissible `5`-vector with **pairwise distinct** entries whose count is not
generic. -/
theorem exists_injective_admissible_five_nongeneric_gf32 :
    ∃ c ∈ coeffFamily K32 5, Function.Injective c ∧
      mCount 5 kasami52 c ≠ 2 ^ ((5 - 1) * 5 - 5) :=
  ⟨c52inj, c52inj_mem, c52inj_injective, by rw [kasami52_mCount5_inj]; norm_num⟩

/-- The setting is the intended one: `|K32| = 2⁵`, the exponent parameter `k = 2`
is coprime to `n = 5` (so the completed `m = 3` theorem applies) and `k` is a
*hard* residue, `k ≢ ±1 (mod n)` (so the odd-`m` subgroup mechanism does not). -/
theorem kasami52_setting :
    Fintype.card K32 = 2 ^ 5 ∧ Nat.Coprime 2 5 ∧ ¬ (2 % 5 = 1 ∨ 2 % 5 = 5 - 1) :=
  ⟨K32.card_eq, by decide, by decide⟩

/-- The two halves side by side: at `n = 5, k = 2` the `m = 3` conclusion holds
and the `m = 5` conclusion fails. -/
theorem kasami52_three_not_five :
    KasamiMTupleConjecture K32 5 2 3 ∧ ¬ KasamiMTupleConjecture K32 5 2 5 :=
  ⟨kasami52_three, not_kasamiMTupleConjecture_five_gf32⟩

#print axioms not_kasamiMTupleConjecture_five_gf32
#print axioms kasami52_three_not_five
#print axioms exists_injective_admissible_five_nongeneric_gf32

end MTuple
