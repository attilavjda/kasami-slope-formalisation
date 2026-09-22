import MTuple.Gold

/-!
# An application: the Kasami triple count for `k ≡ ±1 (mod n)`

For `k : ℕ` the *Kasami exponent* is `d(k) = 2^{2k} − 2^k + 1` (`kasamiExp`), and
the associated set on `F = GF(2ⁿ)` is

`Δ(d) = { b^d + (b+1)^d + 1 : b ∈ F }`  (`kasamiDelta`).

The conjecture in question asks, for distinct nonzero `v₁, v₂`, that

`N(v₁,v₂) = #{ (x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0 } = 2^{2n−3}`

(`tripleCount`, `KasamiTripleConjecture`).  Since `(v₁, v₂, v₁+v₂)` is an
admissible coefficient vector and `2^{2n−3}` is the generic value at `m = 3`,
this is exactly the `m = 3` instance of the library's odd-`m` theorem
(`tripleCount_eq_mCount`).

Here it is **proved unconditionally for `k ≡ ±1 (mod n)`, every `n ≥ 2`**
(`kasamiTripleConjecture_of_mod_pm_one`).  In those two cases the Kasami power
map is the cube map, respectively a Frobenius twist of it, so `Δ` is an additive
subgroup — the image of `b ↦ b² + b` up to a Frobenius twist — and the phase is
non-negative by `MTuple.mPhase_addClosed_nonneg`.  The remaining residues are
left open.
-/

open Finset

namespace MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The statement -/

/-- The Kasami exponent `d(k) = 2^{2k} − 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- `Δ(d) = { b^d + (b+1)^d + 1 : b ∈ F }`. -/
def kasamiDelta (F : Type*) [Field F] [Fintype F] [DecidableEq F] (dd : ℕ) : Finset F :=
  (univ : Finset F).image (fun b => b ^ dd + (b + 1) ^ dd + 1)

/-- `N(v₁,v₂) = #{ (x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0 }`. -/
def tripleCount (dd : ℕ) (v₁ v₂ : F) : ℕ :=
  ((univ : Finset (F × F × F)).filter (fun p =>
    p.1 ∈ kasamiDelta F dd ∧ p.2.1 ∈ kasamiDelta F dd ∧ p.2.2 ∈ kasamiDelta F dd ∧
      v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)).card

/-- The conjecture on `F = GF(2ⁿ)` for the Kasami exponent `d(k)`: the count
`N(v₁,v₂)` equals `2^{2n−3}` for all distinct nonzero `v₁, v₂`. -/
def KasamiTripleConjecture (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n k : ℕ) :
    Prop :=
  ∀ v₁ v₂ : F, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ → tripleCount (kasamiExp k) v₁ v₂ = 2 ^ (2 * n - 3)

/-! ## The bridge to the library's `mCount` -/

/-- The coefficient vector `(v₁, v₂, v₁+v₂)` is admissible. -/
theorem coeff_triple_mem {v₁ v₂ : F} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (h₁₂ : v₁ ≠ v₂) :
    ![v₁, v₂, v₁ + v₂] ∈ coeffFamily F 3 := by
  rw [mem_coeffFamily]
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact h₁
    · exact h₂
    · intro h
      exact h₁₂ (CharTwo.add_eq_zero.1 (by simpa using h))
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination CharTwo.add_self_eq_zero (v₁ + v₂)

omit [CharP F 2] in
/-- `N(v₁,v₂)` is exactly the library's `3`-tuple count on `Δ(d)`. -/
theorem tripleCount_eq_mCount (dd : ℕ) (v₁ v₂ : F) :
    tripleCount dd v₁ v₂ = mCount 3 (kasamiDelta F dd) ![v₁, v₂, v₁ + v₂] := by
  classical
  refine Finset.card_nbij' (fun p => ![p.1, p.2.1, p.2.2]) (fun x => (x 0, x 1, x 2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset] at hp ⊢
    refine ⟨fun i => by fin_cases i <;> simp [hp.1, hp.2.1, hp.2.2.1], ?_⟩
    simpa [Fin.sum_univ_three] using hp.2.2.2
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_univ, true_and] at hx ⊢
    refine ⟨hx.1 0, hx.1 1, hx.1 2, ?_⟩
    simpa [Fin.sum_univ_three] using hx.2
  · intro p _
    simp
  · intro x _
    funext i
    fin_cases i <;> simp

/-! ## Frobenius twists of an additive subgroup -/

omit [Fintype F] [DecidableEq F] in
/-- `x ↦ x^{2^j}` is injective on a field of characteristic `2`. -/
theorem frobPow_injective (j : ℕ) : Function.Injective (fun x : F => x ^ (2 ^ j)) := by
  intro x y hxy
  have h : (x + y) ^ (2 ^ j) = 0 := by
    rw [add_pow_char_pow (p := 2) (n := j) x y]
    simpa using CharTwo.add_eq_zero.2 hxy
  exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 h)

omit [Fintype F] in
/-- The image of an additive subgroup under `x ↦ x^{2^j}` is an additive subgroup. -/
theorem frobPow_image_add_mem (j : ℕ) (V : Finset F)
    (hVadd : ∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) :
    ∀ x ∈ V.image (fun v => v ^ (2 ^ j)), ∀ y ∈ V.image (fun v => v ^ (2 ^ j)),
      x + y ∈ V.image (fun v => v ^ (2 ^ j)) := by
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
  exact Finset.mem_image.2 ⟨u + v, hVadd u hu v hv,
    add_pow_char_pow (p := 2) (n := j) u v⟩

/-! ## `Δ` is an additive subgroup for `k ≡ ±1 (mod n)` -/

omit [Fintype F] [DecidableEq F] in
/-- `b³ + (b+1)³ + 1 = b² + b`, the image of the `𝔽₂`-linear map `goldLin 1 1`. -/
theorem cube_delta (b : F) : b ^ 3 + (b + 1) ^ 3 + 1 = goldLin 1 1 b := by
  have h := gold_deriv 1 (1 : F) b
  simp only [gold, one_pow] at h
  rw [show (2 : ℕ) ^ 1 + 1 = 3 from rfl] at h
  linear_combination h + CharTwo.add_self_eq_zero (1 : F)

omit [DecidableEq F] [CharP F 2] in
/-- Frobenius periodicity: `x^{2^k}` depends only on `k mod n`. -/
theorem pow_two_pow_mod {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (x : F) :
    x ^ 2 ^ k = x ^ 2 ^ (k % n) := by
  have hcardpow : ∀ y : F, y ^ 2 ^ n = y := fun y => by rw [← hcard]; exact FiniteField.pow_card y
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
        rcases lt_or_ge k n with h | h
        · rw [Nat.mod_eq_of_lt h]
        · have hk : k - n + n = k := Nat.sub_add_cancel h
          have h1 : x ^ 2 ^ k = x ^ 2 ^ (k - n) := by
            conv_lhs => rw [← hk, pow_add, pow_mul]
            exact hcardpow _
          rw [h1, ih (k - n) (by omega), Nat.mod_eq_sub_mod h]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
/-- The defining relation of the Kasami exponent: `x^{d(k)}·x^{2^k} = x^{2^{2k}}·x`. -/
theorem kasami_pow_relation (k : ℕ) (x : F) :
    x ^ kasamiExp k * x ^ 2 ^ k = x ^ 2 ^ (2 * k) * x := by
  have hle : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hexp : kasamiExp k + 2 ^ k = 2 ^ (2 * k) + 1 := by
    simp only [kasamiExp]; omega
  rw [← pow_add, hexp, pow_add, pow_one]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem kasamiExp_ne_zero (k : ℕ) : kasamiExp k ≠ 0 := by
  have hle : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [kasamiExp]; omega

omit [DecidableEq F] [CharP F 2] in
/-- For `k ≡ 1 (mod n)` and `n ≥ 2` the Kasami power map is the cube map. -/
theorem kasami_pow_eq_cube {n k : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hk : k % n = 1) (x : F) : x ^ kasamiExp k = x ^ 3 := by
  have hA : x ^ 2 ^ k = x ^ 2 := by rw [pow_two_pow_mod hcard k x, hk, pow_one]
  have hrel := kasami_pow_relation (F := F) k x
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- `n = 2`: every nonzero `x` satisfies `x³ = 1`, and the relation gives `x^d = 1`.
    subst hn2
    have hB : x ^ 2 ^ (2 * k) = x := by
      rw [pow_two_pow_mod hcard (2 * k) x, show (2 * k) % 2 = 0 by omega]; norm_num
    rw [hA, hB] at hrel
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_pow (kasamiExp_ne_zero k), zero_pow (by norm_num)]
    · have hx3 : x ^ 3 = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one x hx
        rwa [hcard] at h
      have hcan : x ^ kasamiExp k * x ^ 2 = 1 * x ^ 2 := by rw [hrel]; ring
      rw [mul_right_cancel₀ (pow_ne_zero 2 hx) hcan, hx3]
  · -- `n ≥ 3`: the Frobenius exponents `k` and `2k` reduce to `1` and `2`.
    have h2k : (2 * k) % n = 2 := by
      rw [Nat.mul_mod, hk, mul_one, Nat.mod_mod_of_dvd _ dvd_rfl, Nat.mod_eq_of_lt (by omega)]
    have hB : x ^ 2 ^ (2 * k) = x ^ 4 := by
      rw [pow_two_pow_mod hcard (2 * k) x, h2k]; norm_num
    rw [hA, hB] at hrel
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_pow (kasamiExp_ne_zero k), zero_pow (by norm_num)]
    · refine mul_right_cancel₀ (pow_ne_zero 2 hx) ?_
      rw [hrel]; ring

omit [DecidableEq F] [CharP F 2] in
/-- For `k ≡ −1 (mod n)` and `n ≥ 2` the Kasami power map is the `(n−2)`-fold
Frobenius twist of the cube map.  (At `n = 2` the two residues `1` and `n − 1`
coincide and the twist is trivial.) -/
theorem kasami_pow_eq_cube_frob {n k : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hk : k % n = n - 1) (x : F) : x ^ kasamiExp k = (x ^ 3) ^ 2 ^ (n - 2) := by
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · subst hn2
    simpa using kasami_pow_eq_cube (n := 2) le_rfl hcard (by simpa using hk) x
  have hn : 3 ≤ n := hn3
  have hcardpow : ∀ y : F, y ^ 2 ^ n = y := fun y => by rw [← hcard]; exact FiniteField.pow_card y
  have h2k : (2 * k) % n = n - 2 := by
    have hmod2 : 2 % n = 2 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.mul_mod, hk, hmod2]
    have h1 : 2 * (n - 1) = n + (n - 2) := by omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (show n - 2 < n by omega)]
  have hA : x ^ 2 ^ k = x ^ 2 ^ (n - 1) := by rw [pow_two_pow_mod hcard k x, hk]
  have hB : x ^ 2 ^ (2 * k) = x ^ 2 ^ (n - 2) := by rw [pow_two_pow_mod hcard (2 * k) x, h2k]
  have hrel := kasami_pow_relation (F := F) k x
  rw [hA, hB] at hrel
  have e1 : 2 ^ (n - 2) * 2 = 2 ^ (n - 1) := by rw [← pow_succ]; congr 1; omega
  have e2 : 2 ^ (n - 2) * 4 = 2 ^ n := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega
  set u : F := x ^ 2 ^ (n - 2) with hu
  have hu2 : u ^ 2 = x ^ 2 ^ (n - 1) := by rw [hu, ← pow_mul, e1]
  have hu4 : u ^ 4 = x := by rw [hu, ← pow_mul, e2]; exact hcardpow x
  have hgoal : (x ^ 3) ^ 2 ^ (n - 2) = u ^ 3 := by rw [hu, ← pow_mul, ← pow_mul, mul_comm]
  rw [hgoal]
  rcases eq_or_ne x 0 with rfl | hx
  · have hu0 : u = 0 := by rw [hu]; exact zero_pow (by positivity)
    rw [zero_pow (kasamiExp_ne_zero k), hu0]
    norm_num
  · have hune : u ≠ 0 := by rw [hu]; exact pow_ne_zero _ hx
    refine mul_right_cancel₀ (pow_ne_zero 2 hune) ?_
    rw [← hu2] at hrel
    rw [hrel, ← hu4]; ring

/-- For `k ≡ ±1 (mod n)` the set `Δ(d(k))` is a Frobenius twist of the additive
subgroup `{ b² + b : b ∈ F }`. -/
theorem kasamiDelta_eq_frob_image {n k : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hk : k % n = 1 ∨ k % n = n - 1) :
    ∃ j : ℕ, kasamiDelta F (kasamiExp k)
      = (goldLinImage 1 (1 : F)).image (fun v => v ^ (2 ^ j)) := by
  have himg : ∀ j : ℕ, (∀ x : F, x ^ kasamiExp k = (x ^ 3) ^ 2 ^ j) →
      kasamiDelta F (kasamiExp k)
        = (goldLinImage 1 (1 : F)).image (fun v => v ^ (2 ^ j)) := by
    intro j hj
    rw [kasamiDelta, goldLinImage, Finset.image_image]
    refine Finset.image_congr fun b _ => ?_
    have hfrob : ((b ^ 3) ^ 2 ^ j + ((b + 1) ^ 3) ^ 2 ^ j + 1)
        = (b ^ 3 + (b + 1) ^ 3 + 1) ^ 2 ^ j := by
      rw [add_pow_char_pow (p := 2) (n := j), add_pow_char_pow (p := 2) (n := j), one_pow]
    show b ^ kasamiExp k + (b + 1) ^ kasamiExp k + 1 = ((goldLin 1 1) b) ^ 2 ^ j
    rw [hj b, hj (b + 1), hfrob, cube_delta b]
  rcases hk with hk | hk
  · exact ⟨0, himg 0 (fun x => by rw [kasami_pow_eq_cube hn hcard hk x]; simp)⟩
  · exact ⟨n - 2, himg (n - 2) (fun x => kasami_pow_eq_cube_frob hn hcard hk x)⟩

/-! ## The conjecture for `k ≡ ±1 (mod n)` -/

/-- `{ b² + b : b ∈ F }` has `2^{n−1}` elements: it is the derivative image of the
cube map at direction `1`, up to a translation. -/
theorem card_goldLinImage_one {n : ℕ} (hcard : Fintype.card F = 2 ^ n) :
    (goldLinImage 1 (1 : F)).card = 2 ^ (n - 1) := by
  have h := card_derivImage_cube (K := F) hcard (a := 1) one_ne_zero
  rw [derivImage_gold 1 (1 : F),
    Finset.card_image_of_injective _ (fun x y hxy => by simpa using add_right_cancel hxy)] at h
  exact h

/-- **The Kasami triple count for `k ≡ ±1 (mod n)`.**  On every field with `2ⁿ`
elements, `n ≥ 2`, and every `k` with `k ≡ ±1 (mod n)`, the count `N(v₁,v₂)` is
`2^{2n−3}` for all distinct nonzero `v₁, v₂` (`n ≥ 2`).  Nothing is assumed about the
phase: `Δ` is an additive subgroup, so the positivity is proved. -/
theorem kasamiTripleConjecture_of_mod_pm_one {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1) :
    KasamiTripleConjecture F n k := by
  obtain ⟨j, hΔ⟩ := kasamiDelta_eq_frob_image hn hcard hk
  have hadd : ∀ x ∈ kasamiDelta F (kasamiExp k), ∀ y ∈ kasamiDelta F (kasamiExp k),
      x + y ∈ kasamiDelta F (kasamiExp k) := by
    rw [hΔ]
    exact frobPow_image_add_mem j _ (goldLinImage_add_mem 1 1)
  have hcardΔ : (kasamiDelta F (kasamiExp k)).card = 2 ^ (n - 1) := by
    rw [hΔ, Finset.card_image_of_injective _ (frobPow_injective (F := F) j)]
    exact card_goldLinImage_one hcard
  intro v₁ v₂ h₁ h₂ h₁₂
  have hgen := mTupleCount_odd_of_addClosed (n := n) (m := 3) (by omega) le_rfl
    (by decide) _ hadd hcard hcardΔ _ (coeff_triple_mem h₁ h₂ h₁₂)
  rw [tripleCount_eq_mCount, hgen]

end MTuple
