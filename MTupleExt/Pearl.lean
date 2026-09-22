import MTuple
import MTupleExt.ExactAffine
import MTupleExt.KasamiMTuple

/-!
# Anchors for the sign-factorisation verification pearl

`docs/sign-factorization-pearl.tex` (and the compiled `.pdf`) quotes a small
number of statements from this project.  This module contains **no new
mathematics**: it only `#check`s the quoted declarations, so that the statements
printed in the document are exactly the statements the kernel accepted, and
`#print axioms` shows that each of them rests on the standard three axioms only.

The numbering matches the sections of the document.

* §2 the mechanism — `MTuple.prod_eps_eq_eps_sum`,
  `MTuple.mPhase_nonneg_of_sign_factorization`;
* §3 the dictionary — `MTuple.card_mul_mCount`,
  `MTuple.card_mul_mDeficiency_eq_mPhase`, `MTuple.mTupleCount_odd_of_mPhase_nonneg`;
* §4 the reach — `MTuple.sign_factorization_iff_affine_trace_hyperplane`;
* §5 the exact count — `MTuple.mCount_affineTraceHyperplane_of_not_const`,
  `MTuple.mCount_affineTraceHyperplane_const_eq_two_mul`;
* §6 the instances — `MTuple.gold_mCount_generic_odd`,
  `MTuple.kasamiTripleConjecture_of_mod_pm_one`,
  `MTuple.kasamiMTupleConjecture_odd_of_mod_pm_one`,
  `MTuple.not_kasamiMTupleConjecture_even_of_card`.
-/

namespace MTuple

-- §2  the mechanism
#check @prod_eps_eq_eps_sum
#check @mPhase_nonneg_of_sign_factorization
#print axioms mPhase_nonneg_of_sign_factorization

-- §3  the counting ⇄ phase dictionary
#check @card_mul_mCount
#check @card_mul_mDeficiency_eq_mPhase
#check @mTupleCount_odd_of_mPhase_nonneg
#print axioms mTupleCount_odd_of_mPhase_nonneg

-- §4  the reach of the mechanism
#check @HasSignFactorization
#check @sign_factorization_iff_affine_trace_hyperplane
#print axioms sign_factorization_iff_affine_trace_hyperplane

-- §5  the exact count on that reach
#check @mCount_affineTraceHyperplane_of_not_const
#check @mCount_affineTraceHyperplane_const_eq_two_mul
#print axioms mCount_affineTraceHyperplane_of_not_const
#print axioms mCount_affineTraceHyperplane_const_eq_two_mul

-- §6  the instances
#check @gold_mCount_generic_odd
#check @kasamiTripleConjecture_of_mod_pm_one
#check @kasamiMTupleConjecture_odd_of_mod_pm_one
#check @not_kasamiMTupleConjecture_even_of_card
#print axioms kasamiMTupleConjecture_odd_of_mod_pm_one
#print axioms not_kasamiMTupleConjecture_even_of_card

end MTuple
