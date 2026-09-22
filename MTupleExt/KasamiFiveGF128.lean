import MTuple.SplitCount
import MTuple.GF128
import MTupleExt.KasamiMTuple
import MTupleExt.Normalisation

/-!
# The `m = 5` Kasami statement is **false** for `n = 7, k = 2` and `n = 7, k = 3`

The companion of `MTuple/MTupleExt/KasamiFiveGF32.lean`, one field up.
We work in the computable model `K128 = 𝔽₂[x]/(x⁷+x+1)` of `GF(128)`, with the
Kasami exponents `d(2) = 13` and `d(3) = 57`.  Both residues are hard
(`k % n = 2, 3 ∉ {1, 6}`) and both are coprime to `n = 7`, so the completed
`m = 3` theorem applies to them — and indeed the `m = 3` conclusion is verified
here directly (`kasami72_three`, `kasami73_three`).

At `m = 5` the conclusion fails in both cases:

* `kasami72_mCount5` — at `c = (1, 1, x+1, x³+x², x³+x²+x+1)` the count is
  `8387584`, i.e. `1024` **below** the generic `2^{(5−1)·7−5} = 8388608`;
* `kasami73_mCount5` — at `c = (1, 1, x, x²+1, x²+x+1)` the count is `8389632`,
  i.e. `1024` **above** the generic value.

Both also have witnesses with pairwise distinct entries
(`exists_injective_admissible_five_nongeneric_gf128`).

So the deficiency has both signs; the `m = 5` statement is not merely violated,
it is violated in both directions, which rules out any one-sided (positivity
type) mechanism for odd `m ≥ 5` in the hard residues.

Brute force over `Δ⁵` is impossible here (`64⁵ ≈ 1.07 · 10⁹` tuples); all counts
go through the convolution formula `MTuple.mCount_split_count`, which costs
`|K| · (|Δ|³ + |Δ|²)` instead.
-/

set_option maxRecDepth 100000

open Finset MTuple.GF128Model MTuple.GF128Model.K128

namespace MTuple

/-! ## `n = 7`, `k = 2` -/

/-- The Kasami derivative image `Δ(d(2))` in `GF(128)`, `d(2) = 13`. -/
def kasami72 : Finset K128 := kasamiDelta K128 (kasamiExp 2)

/-- The admissible `5`-vector with bit patterns `(1, 1, 3, 12, 15)`. -/
def c72 : Fin 5 → K128 := ![ofNat 1, ofNat 1, ofNat 3, ofNat 12, ofNat 15]

theorem kasami72_card : kasami72.card = 2 ^ (7 - 1) := by native_decide

theorem c72_mem : c72 ∈ coeffFamily K128 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

/-- Exhaustive slope check at `m = 3`: always the generic `2^{2·7−3} = 2048`. -/
theorem kasami72_mCount3_slope :
    ∀ r : K128, r ≠ 0 → r ≠ 1 → mCount 3 kasami72 ![1, r, 1 + r] = 2048 := by
  intro r h0 h1
  refine (mCount_split_count 2 1 kasami72 ![1, r, 1 + r]).trans ?_
  revert h0 h1
  revert r
  have key : ∀ r : K128, r ≠ 0 → r ≠ 1 →
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami72)).val.map
          (fun x => ∑ i, (![1, r, 1 + r] : Fin 3 → K128) (Fin.castAdd 1 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 1 => kasami72)).val.map
          (fun x => ∑ i, (![1, r, 1 + r] : Fin 3 → K128) (Fin.natAdd 2 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 2048 := by native_decide
  exact key

/-- **The `m = 3` statement holds for `n = 7, k = 2`.** -/
theorem kasami72_three : KasamiMTupleConjecture K128 7 2 3 := by
  intro c hc
  obtain ⟨hr0, hr1⟩ := coeff_three_ratio_ne hc
  show mCount 3 kasami72 c = _
  rw [mCount_three_normalise kasami72 hc, kasami72_mCount3_slope _ hr0 hr1]
  norm_num

/-- The `5`-tuple count at `c72`, computed by convolution: `8387584`. -/
theorem kasami72_mCount5 : mCount 5 kasami72 c72 = 8387584 := by
  refine (mCount_split_count 3 2 kasami72 c72).trans ?_
  have key :
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 3 => kasami72)).val.map
          (fun x => ∑ i, c72 (Fin.castAdd 2 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami72)).val.map
          (fun x => ∑ i, c72 (Fin.natAdd 3 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 8387584 := by native_decide
  exact key

theorem kasami72_mCount5_ne_generic : mCount 5 kasami72 c72 ≠ 2 ^ ((5 - 1) * 7 - 5) := by
  rw [kasami72_mCount5]
  norm_num

/-- **The `m = 5` Kasami `m`-tuple statement is false for `n = 7`, `k = 2`.** -/
theorem not_kasamiMTupleConjecture_five_gf128_k2 : ¬ KasamiMTupleConjecture K128 7 2 5 := by
  intro h
  have hx := h c72 c72_mem
  rw [show kasamiDelta K128 (kasamiExp 2) = kasami72 from rfl, kasami72_mCount5] at hx
  norm_num at hx

/-! ## `n = 7`, `k = 3` -/

/-- The Kasami derivative image `Δ(d(3))` in `GF(128)`, `d(3) = 57`. -/
def kasami73 : Finset K128 := kasamiDelta K128 (kasamiExp 3)

/-- The admissible `5`-vector with bit patterns `(1, 1, 2, 5, 7)`. -/
def c73 : Fin 5 → K128 := ![ofNat 1, ofNat 1, ofNat 2, ofNat 5, ofNat 7]

theorem kasami73_card : kasami73.card = 2 ^ (7 - 1) := by native_decide

theorem c73_mem : c73 ∈ coeffFamily K128 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

/-- Exhaustive slope check at `m = 3`: always the generic `2^{2·7−3} = 2048`. -/
theorem kasami73_mCount3_slope :
    ∀ r : K128, r ≠ 0 → r ≠ 1 → mCount 3 kasami73 ![1, r, 1 + r] = 2048 := by
  intro r h0 h1
  refine (mCount_split_count 2 1 kasami73 ![1, r, 1 + r]).trans ?_
  revert h0 h1
  revert r
  have key : ∀ r : K128, r ≠ 0 → r ≠ 1 →
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami73)).val.map
          (fun x => ∑ i, (![1, r, 1 + r] : Fin 3 → K128) (Fin.castAdd 1 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 1 => kasami73)).val.map
          (fun x => ∑ i, (![1, r, 1 + r] : Fin 3 → K128) (Fin.natAdd 2 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 2048 := by native_decide
  exact key

/-- **The `m = 3` statement holds for `n = 7, k = 3`.** -/
theorem kasami73_three : KasamiMTupleConjecture K128 7 3 3 := by
  intro c hc
  obtain ⟨hr0, hr1⟩ := coeff_three_ratio_ne hc
  show mCount 3 kasami73 c = _
  rw [mCount_three_normalise kasami73 hc, kasami73_mCount3_slope _ hr0 hr1]
  norm_num

/-- The `5`-tuple count at `c73`, computed by convolution: `8389632`. -/
theorem kasami73_mCount5 : mCount 5 kasami73 c73 = 8389632 := by
  refine (mCount_split_count 3 2 kasami73 c73).trans ?_
  have key :
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 3 => kasami73)).val.map
          (fun x => ∑ i, c73 (Fin.castAdd 2 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami73)).val.map
          (fun x => ∑ i, c73 (Fin.natAdd 3 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 8389632 := by native_decide
  exact key

theorem kasami73_mCount5_ne_generic : mCount 5 kasami73 c73 ≠ 2 ^ ((5 - 1) * 7 - 5) := by
  rw [kasami73_mCount5]
  norm_num

/-- **The `m = 5` Kasami `m`-tuple statement is false for `n = 7`, `k = 3`.** -/
theorem not_kasamiMTupleConjecture_five_gf128_k3 : ¬ KasamiMTupleConjecture K128 7 3 5 := by
  intro h
  have hx := h c73 c73_mem
  rw [show kasamiDelta K128 (kasamiExp 3) = kasami73 from rfl, kasami73_mCount5] at hx
  norm_num at hx

/-! ## Witnesses with pairwise distinct entries -/

/-- Admissible `5`-vector with bit patterns `(1, 2, 4, 8, 15)`, pairwise
distinct entries, for `k = 2`. -/
def c72inj : Fin 5 → K128 := ![ofNat 1, ofNat 2, ofNat 4, ofNat 8, ofNat 15]

/-- Admissible `5`-vector with bit patterns `(1, 2, 4, 9, 14)`, pairwise
distinct entries, for `k = 3`. -/
def c73inj : Fin 5 → K128 := ![ofNat 1, ofNat 2, ofNat 4, ofNat 9, ofNat 14]

theorem c72inj_mem : c72inj ∈ coeffFamily K128 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

theorem c73inj_mem : c73inj ∈ coeffFamily K128 5 := by
  rw [mem_coeffFamily]
  exact ⟨by decide, by decide⟩

theorem c72inj_injective : Function.Injective c72inj := by decide

theorem c73inj_injective : Function.Injective c73inj := by decide

theorem kasami72_mCount5_inj : mCount 5 kasami72 c72inj = 8387584 := by
  refine (mCount_split_count 3 2 kasami72 c72inj).trans ?_
  have key :
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 3 => kasami72)).val.map
          (fun x => ∑ i, c72inj (Fin.castAdd 2 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami72)).val.map
          (fun x => ∑ i, c72inj (Fin.natAdd 3 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 8387584 := by native_decide
  exact key

theorem kasami73_mCount5_inj : mCount 5 kasami73 c73inj = 8388096 := by
  refine (mCount_split_count 3 2 kasami73 c73inj).trans ?_
  have key :
      (let M : Multiset K128 := (Fintype.piFinset (fun _ : Fin 3 => kasami73)).val.map
          (fun x => ∑ i, c73inj (Fin.castAdd 2 i) * x i)
       let N : Multiset K128 := (Fintype.piFinset (fun _ : Fin 2 => kasami73)).val.map
          (fun x => ∑ i, c73inj (Fin.natAdd 3 i) * x i)
       ∑ z : K128, M.count z * N.count z) = 8388096 := by native_decide
  exact key

/-- The failures are not artefacts of repeated coefficients: in both hard
residues there is an admissible `5`-vector with **pairwise distinct** entries
whose count is not generic. -/
theorem exists_injective_admissible_five_nongeneric_gf128 :
    (∃ c ∈ coeffFamily K128 5, Function.Injective c ∧
        mCount 5 kasami72 c ≠ 2 ^ ((5 - 1) * 7 - 5)) ∧
    (∃ c ∈ coeffFamily K128 5, Function.Injective c ∧
        mCount 5 kasami73 c ≠ 2 ^ ((5 - 1) * 7 - 5)) :=
  ⟨⟨c72inj, c72inj_mem, c72inj_injective, by rw [kasami72_mCount5_inj]; norm_num⟩,
   ⟨c73inj, c73inj_mem, c73inj_injective, by rw [kasami73_mCount5_inj]; norm_num⟩⟩

/-- The setting is the intended one: `|K128| = 2⁷`, both `k = 2` and `k = 3` are
coprime to `n = 7` and both are *hard* residues, `k ≢ ±1 (mod 7)`. -/
theorem kasami7_setting :
    Fintype.card K128 = 2 ^ 7 ∧ (Nat.Coprime 2 7 ∧ ¬ (2 % 7 = 1 ∨ 2 % 7 = 7 - 1)) ∧
      (Nat.Coprime 3 7 ∧ ¬ (3 % 7 = 1 ∨ 3 % 7 = 7 - 1)) :=
  ⟨K128.card_eq, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- At `n = 7` both hard residues `k = 2, 3` satisfy the `m = 3` conclusion and
violate the `m = 5` one. -/
theorem kasami7_three_not_five :
    (KasamiMTupleConjecture K128 7 2 3 ∧ ¬ KasamiMTupleConjecture K128 7 2 5) ∧
    (KasamiMTupleConjecture K128 7 3 3 ∧ ¬ KasamiMTupleConjecture K128 7 3 5) :=
  ⟨⟨kasami72_three, not_kasamiMTupleConjecture_five_gf128_k2⟩,
   ⟨kasami73_three, not_kasamiMTupleConjecture_five_gf128_k3⟩⟩

#print axioms not_kasamiMTupleConjecture_five_gf128_k2
#print axioms not_kasamiMTupleConjecture_five_gf128_k3
#print axioms kasami7_three_not_five
#print axioms exists_injective_admissible_five_nongeneric_gf128

end MTuple
