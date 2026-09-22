import MTuple.Kasami

/-!
# Statement-level bridge to the `KasamiCyclicAdditive` statement surface

`COMPARISON.md` compares this library with two other Kasami developments and
with the Nagy–Vajda article.  The comparison of the two `m = 3` formalisations
(the *partial* one proved here, and the *complete* one of the
`kasami_cyclic_additive` development) is only meaningful if the two statements
really are about the same objects, so the identification is machine-checked
here rather than asserted in prose.

The `kasami_cyclic_additive` statement surface (its `Challenge.lean` /
`Basic.lean`) is reproduced verbatim below under the prefix `kca`:

```text
kcaExponent k              = 4 ^ k - 2 ^ k + 1
kcaDerivative k b          = (b + 1) ^ d + b ^ d + 1
kcaDerivativeImage k K     = image (kcaDerivative k) univ
kcaCoefficientTripleCount  = #{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}
```

and it is proved to agree with this library's `kasamiExp`, `kasamiDelta`,
`tripleCount` (`kcaExponent_eq_kasamiExp`,
`kcaDerivativeImage_eq_kasamiDelta`, `kcaCoefficientTripleCount_eq_tripleCount`).
Consequently the library's partial result transfers verbatim to that surface
(`kca_coefficientTripleCount_of_mod_pm_one`): the two developments prove the
*same* conclusion, and the whole difference is the range of `(n, k)` covered —
here `n ≥ 2` and `k ≡ ±1 (mod n)` with no coprimality or `k < n` restriction,
there `1 ≤ k < n` with `gcd(k, n) = 1` and no residue restriction.
-/

open Finset

namespace MTuple

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The other development's statement surface -/

/-- The Kasami exponent as written in the `kasami_cyclic_additive` statement
surface: `4^k − 2^k + 1`. -/
def kcaExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The normalized Kasami derivative in direction `1`, as written there:
`δ(b) = (b+1)^d + b^d + 1`. -/
def kcaDerivative (k : ℕ) (b : F) : F :=
  (b + 1) ^ kcaExponent k + b ^ kcaExponent k + 1

/-- The derivative image `Δ`, as written there. -/
def kcaDerivativeImage (k : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.image (kcaDerivative k) Finset.univ

/-- The coefficient triple count, as written there: the count is taken over the
product `Δ ×ˢ Δ ×ˢ Δ` rather than over `F³` with membership side conditions. -/
def kcaCoefficientTripleCount (k : ℕ) (v₁ v₂ : F) : ℕ :=
  (((kcaDerivativeImage k F) ×ˢ (kcaDerivativeImage k F) ×ˢ (kcaDerivativeImage k F)).filter
    (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)).card

/-! ## The two surfaces agree -/

/-- `4^k − 2^k + 1 = 2^{2k} − 2^k + 1`. -/
theorem kcaExponent_eq_kasamiExp (k : ℕ) : kcaExponent k = kasamiExp k := by
  have h : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
    rw [pow_mul]; norm_num
  rw [kcaExponent, kasamiExp, h]

/-- The two derivative images are the same finite set. -/
theorem kcaDerivativeImage_eq_kasamiDelta (k : ℕ) :
    kcaDerivativeImage k F = kasamiDelta F (kasamiExp k) := by
  rw [kcaDerivativeImage, kasamiDelta]
  refine Finset.image_congr fun b _ => ?_
  rw [kcaDerivative, kcaExponent_eq_kasamiExp]
  ring

/-- The two triple counts are the same natural number. -/
theorem kcaCoefficientTripleCount_eq_tripleCount (k : ℕ) (v₁ v₂ : F) :
    kcaCoefficientTripleCount k v₁ v₂ = tripleCount (kasamiExp k) v₁ v₂ := by
  rw [kcaCoefficientTripleCount, tripleCount, kcaDerivativeImage_eq_kasamiDelta]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_assoc]

/-! ## The partial result, in the other development's language -/

variable [CharP F 2]

/-- **The partial `m = 3` result, transported.**  In the statement surface of the
`kasami_cyclic_additive` development, this library proves the Carlet/Kasami
cyclic-additive equality for every `n ≥ 2` and every `k` with
`k ≡ ±1 (mod n)`.  The complete development proves the same equality for every
`1 ≤ k < n` with `gcd(k, n) = 1`; this covers, in addition, all `k ≥ n`
congruent to `±1`, but only those residues. -/
theorem kca_coefficientTripleCount_of_mod_pm_one {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hk : k % n = 1 ∨ k % n = n - 1)
    {v₁ v₂ : F} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    kcaCoefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [kcaCoefficientTripleCount_eq_tripleCount]
  exact kasamiTripleConjecture_of_mod_pm_one hn hcard hk v₁ v₂ hv₁ hv₂ hne

end MTuple
