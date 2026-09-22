import MTuple.Character
import MTuple.Admissible
import MTuple.Count
import MTuple.Mean
import MTuple.Generic
import MTuple.SignFactorization
import MTuple.Rigidity
import MTuple.APN
import MTuple.Gold
import MTuple.Kasami
import MTuple.Comparison
import MTuple.Sharpness
import MTuple.GF16
import MTuple.GF32
import MTuple.GF128
import MTuple.SplitCount
import MTuple.Counterexample
import MTuple.Verification

/-!
# `MTuple`: the `m`-tuple count of a half-size set in characteristic two

Importing this module gives the whole library.  `README.md` is the road map;
each module's own header states what it contributes.

`SplitCount` adds the convolution formula for `mCount`, and `GF32` / `GF128`
add computable models of `GF(32)` and `GF(128)` alongside `GF16`; together they
make the `m = 5` counts of `MTuple/MTupleExt/KasamiFiveGF32.lean` and
`…/KasamiFiveGF128.lean` machine-checkable.

The dependency order is

`Character → Admissible → Count → Mean → Generic →`
`{ SignFactorization → { Rigidity, Gold }, APN → Gold, Sharpness, Counterexample }`
`→ Verification`.
-/
