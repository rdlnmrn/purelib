module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-!
# Ordered finite Gaussian-list proximity

The original paired entries retain their order and common rational quadrance
bound. Equally shaped lists satisfy the recursive paired bounds, while either
mismatched shape fails. Their monic extension retains the same finite tails.
-/

namespace Purelib.Data.Gaussian.List.Proximity

set_option backward.match.sparseCases false in
/-- Require equally long Gaussian lists to have each paired squared distance at most the supplied bound.

The empty lists satisfy the relation, paired heads contribute one squared-distance inequality and mismatched shapes
fail. The bound remains identical along every pair in the retained tails. -/
@[expose] public def CoefficientsClose : List Basic.Canonical → List Basic.Canonical → Fraction.Rational → Prop
  | [], [], _ => True
  | left :: leftTail, right :: rightTail, bound =>
      Norm.Basic.normSq (left - right) ≤ bound ∧
        Purelib.Data.Gaussian.List.Proximity.CoefficientsClose leftTail rightTail bound
  | _, _, _ => False

/-- Prepending one to both close Gaussian lists preserves closeness for a nonnegative bound.

The two new leading entries agree, so their squared distance is zero.
The supplied nonnegative bound admits that pair while retaining the original
paired-tail certificate. -/
public theorem monicCoefficientsClose
    {left right : List Basic.Canonical} {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound)
    (close : List.Proximity.CoefficientsClose left right bound) :
    List.Proximity.CoefficientsClose (1 :: left) (1 :: right) bound := by
  constructor
  · rw [sub_self, Norm.Basic.normSq_zero]
    exact nonnegative
  · exact close

set_option backward.match.sparseCases false in
/-- Require equal list shapes and a squared-distance bound for every paired actual and displayed entry.

Compare entries in their original order and recurse over both tails with the same target. The relation is false for
mismatched shapes and true for two empty lists. -/
@[expose] public def EntriesClose : List Basic.Canonical → List Basic.Canonical → Fraction.Rational → Prop
  | [], [], _ => True
  | actual :: actualTail, displayed :: displayedTail, target =>
      Norm.Basic.normSq (actual - displayed) ≤ target ∧
        Purelib.Data.Gaussian.List.Proximity.EntriesClose actualTail displayedTail target
  | _, _, _ => False

end Purelib.Data.Gaussian.List.Proximity
