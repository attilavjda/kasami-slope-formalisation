This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `m`-tuple counts of half-size sets in characteristic two

A Lean 4 / Mathlib formalization of the `m`-tuple generalization of the Kasami
cyclic-additive problem.

Let `K` be a finite field of characteristic two with `|K| = 2ⁿ` and let
`S ⊆ K` be **half-size**, `|S| = 2^{n−1}`.  For a coefficient vector
`c : Fin m → K` that is **admissible** (all entries nonzero, entries summing to
zero) put

```
mCount m S c = #{ x ∈ Sᵐ : ∑ᵢ cᵢ xᵢ = 0 }.
```

The *generic* value of this count is `2^{(m−1)n−m}`.  The library develops the
Fourier machinery around `mCount`, proves when the generic value is attained,
and settles the `m`-tuple form of the Kasami question in the cases it reaches.

## Relation to the completed `m = 3` theorem

This development builds on the completed `m = 3` result

> **Carlet's Kasami cyclic-additive conjecture**, formalized by D. S. McNeil,
> G. P. Nagy and A. Vajda — Palomar registry entry
> [`PALOMAR-2026-09-04-000005`](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-04-000005&version=1),
> source repository [`dsm054/kasami_cyclic_additive`](https://github.com/dsm054/kasami_cyclic_additive).

That development is an actual Lake dependency of this project (pinned in
`lakefile.toml` to the revision of it that is built against Lean 4.28.0 and
Mathlib `v4.28.0`, matching this project's toolchain).  Two modules interact
with it:

* `MTuple/Comparison.lean` — a statement-level bridge, machine-checking that the
  two statement surfaces really describe the same count;
* `MTupleExt/M3Transfer.lean` — the transport itself.  It contains no new
  mathematics: it identifies the surfaces and reads the completed theorem
  `KasamiCyclicAdditive.carlet_kasami_cyclic_additive_literature` as a statement
  about `mCount`/`mPhase`.  The consequence is
  `MTuple.kasamiMTupleConjecture_three_of_coprime`: the `m`-tuple conclusion at
  `m = 3` for **every** `k` coprime to `n`, not only for `k ≡ ±1 (mod n)`, which
  is as far as this library's own mechanism reaches.

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.28.0`) is pinned in `lean-toolchain`.

```bash
lake exe cache get   # optional: prebuilt Mathlib oleans
lake build
```

A full build from cold (Mathlib cached, everything else compiled, including the
exhaustive `decide` computations) takes a while — the `GF(32)` and `GF(16)`
search modules are the slow ones.

## Layout

### `MTuple/` — the core library

```
Character → Admissible → Count → Mean → Generic →
  { SignFactorization → { Rigidity, Gold }, APN → Gold,
    Sharpness, Counterexample } → Verification
```

* `Character` — the additive character `χ(x) = (−1)^{Tr x}`, its
  multiplicativity and orthogonality.
* `Admissible` — the admissible coefficient family, and its non-vacuity.
* `Count` — `mCount`, `mPhase`, `mDeficiency`, and the Fourier identity linking
  them.
* `Mean` — the mean of the phase over the admissible family.
* `Generic` — the two headline structural results: the count is generic exactly
  when the phase vanishes, and for **odd `m ≥ 3`** phase non-negativity forces
  the generic count; for **even `m ≥ 2`** the generic count always fails
  somewhere.
* `SignFactorization` — the mechanism that discharges phase non-negativity
  unconditionally: a sign factorisation `T̂_S = ε·w` with `ε` additive and
  `w ≥ 0`.
* `Rigidity` — the mechanism is exactly as strong as it looks: a half-size `S`
  admits a sign factorisation **iff** it is an affine trace hyperplane.
* `APN`, `Gold` — APN maps have half-size derivative images; Gold derivative
  images are cosets, so the odd-`m` conclusion holds for them unconditionally.
* `Kasami` — the Kasami exponent `2^{2k} − 2^k + 1`, and the triple/`m`-tuple
  conclusion for `k ≡ ±1 (mod n)`.
* `Sharpness`, `Counterexample` — the hypotheses are load-bearing: even `m`
  fails at every constant vector, `S = K` shows half-size is needed, and an
  explicit `S ⊆ GF(16)` has a negative phase.
* `GF16`, `GF32`, `GF128` — hand-built *computable* models of those fields
  (Mathlib's `GaloisField` is noncomputable, so nothing about it can be
  `decide`d).
* `SplitCount` — the convolution splitting of `mCount`, which is what makes the
  `m = 5` counts machine-checkable at all.
* `Comparison`, `Verification` — the statement bridge, an explicit `m = 2`
  computation, instantiation at `GF(2ⁿ)`, and `#print axioms` on the headline
  results.

### `MTupleExt/` — what the library gives beyond its own headline results

* `ExactAffine` — the **exact** `m`-tuple count of an affine trace hyperplane
  (equivalently of any half-size additive subgroup or coset), for every `m ≥ 2`:
  generic at every non-constant admissible vector, exactly twice generic at
  every constant one.
* `Normalisation` — the count depends on the coefficient vector only up to a
  nonzero scalar.
* `KasamiMTuple` — for `k ≡ ±1 (mod n)`: the `m`-tuple form holds for all odd
  `m ≥ 3` and fails for all even `m ≥ 2`.
* `M3Transfer` — the transport of the completed `m = 3` theorem described above.
* `SeparationGF16` — a machine-checked witness that the `m = 3` conclusion does
  **not** imply the `m = 5` conclusion.
* `KasamiFiveGF32`, `KasamiFiveGF128` — machine-checked refutations of the
  `m = 5` statement in the hard residues `n = 5, k = 2` and `n = 7, k = 2, 3`:
  in each case the `m = 3` conclusion is verified exhaustively and an explicit
  admissible `5`-vector with a non-generic count is exhibited.
* `Checks` — kernel cross-checks of the exact formula on the computable
  `GF(16)`.
* `Pearl` — `#check` / `#print axioms` anchors for the quoted statements.

## Axioms

The development contains no `sorry` and no added axioms.  Every result rests on
`propext`, `Quot.sound` and `Classical.choice` only, with one exception: the
`GF(128)` computations in `MTuple/GF128.lean` and `MTupleExt/KasamiFiveGF128.lean`,
together with some of the cross-checks in `MTupleExt/Checks.lean`, are
discharged by `native_decide` and so additionally use `Lean.ofReduceBool` and
`Lean.trustCompiler`.  Those results
are duplicated in spirit by the kernel-checked `GF(32)` refutation in
`MTupleExt/KasamiFiveGF32.lean`, which uses no compiler trust.

## Notes

Some module docstrings refer to companion write-ups and exploratory scripts
(`COMPARISON.md`, `docs/sign-factorization-pearl.tex`,
`scripts/mtuple_explore_kasami.py`) that are not part of this repository; the
Lean sources are self-contained and do not depend on them.
