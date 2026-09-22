import MTupleExt.ExactAffine
import MTupleExt.Normalisation
import MTupleExt.KasamiMTuple
import MTupleExt.M3Transfer
import MTupleExt.SeparationGF16
import MTupleExt.KasamiFiveGF32
import MTupleExt.KasamiFiveGF128
import MTupleExt.Checks
import MTupleExt.Pearl

/-!
# `MTupleExt`: what the `m`-tuple library gives beyond its own headline results

Nine modules, all building on `MTuple/MTuple/`:

* `ExactAffine` — the **exact** `m`-tuple count of an affine trace hyperplane
  (equivalently, of any half-size additive subgroup or coset): generic at every
  non-constant admissible coefficient vector, exactly twice generic at every
  constant one, for *every* tuple length `m ≥ 2`.
* `Normalisation` — the count depends on the coefficient vector only up to a
  nonzero scalar; at `m = 3` this is the slope normalisation `(1, ρ, 1+ρ)`.
* `KasamiMTuple` — the consequence for the Kasami derivative image at
  `k ≡ ±1 (mod n)`: the `m`-tuple form of the conjecture holds for all odd
  `m ≥ 3` and fails for all even `m ≥ 2`.
* `SeparationGF16` — a machine-checked witness that the `m = 3` conclusion does
  **not** imply the `m = 5` conclusion.
* `KasamiFiveGF32` / `KasamiFiveGF128` — machine-checked refutations of the
  `m = 5` statement in the hard residues `n = 5, k = 2` and `n = 7, k = 2, 3`:
  in each case the `m = 3` conclusion is verified exhaustively and an explicit
  admissible `5`-vector with a non-generic count is exhibited.
* `M3Transfer` — the transport of the completed `m = 3` Kasami cyclic-additive
  theorem (the `KasamiCyclicAdditive` dependency) into the `m`-tuple frame: at
  `m = 3` the conclusion then holds for *every* `k` coprime to `n`, not only
  for `k ≡ ±1 (mod n)`.
* `Checks` — kernel cross-checks of the exact formula on a computable `GF(16)`.
* `Pearl` — `#check`/`#print axioms` anchors for the statements quoted in
  `docs/sign-factorization-pearl.tex`.

`README.md` in the project root is the road map: build instructions, the
headline statements, and how the modules fit together.
-/
