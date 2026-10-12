module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
public section

/-!
# Products of finite scalar lists

Structural list products use the original field multiplication. Entrywise
multiplication stops at the shorter list; equal lengths give distribution
of its product over the two retained list products.
-/

namespace Purelib.Algebra.FiniteProduct.List

variable {K : Type*} [ExplicitField K]

/-- Multiply a finite list of field elements.

Structural recursion uses one for the empty product and multiplies each head by the product of its tail. -/
@[expose] def scalarProduct : List K → K
  | [] => 1
  | value :: remaining => value * Purelib.Algebra.FiniteProduct.List.scalarProduct remaining

/-- Multiply two finite scalar lists entry by entry.

Recursion stops when either list is empty; equal lengths are required separately for product-distribution theorems. -/
@[expose] def pointwiseScalarProduct : List K → List K → List K
  | left :: leftRemaining, right :: rightRemaining =>
      left * right :: Purelib.Algebra.FiniteProduct.List.pointwiseScalarProduct leftRemaining rightRemaining
  | [], _ => []
  | _ :: _, [] => []

open Purelib.Algebra in
/-- The product of an entrywise product equals the product of the two totals.

The lists must have the same length so every entry of both lists is included. -/
theorem finiteScalarProduct_pointwise
    (left right : List K) (sameLength : left.length = right.length) :
    FiniteProduct.List.scalarProduct (FiniteProduct.List.pointwiseScalarProduct left right) =
      FiniteProduct.List.scalarProduct left * FiniteProduct.List.scalarProduct right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          simp only [FiniteProduct.List.pointwiseScalarProduct, FiniteProduct.List.scalarProduct]
          ring1
      | cons right rightRemaining =>
          simp only [List.length_nil, List.length_cons] at sameLength
          exact Nat.noConfusion sameLength
  | cons left leftRemaining inductionHypothesis =>
      cases right with
      | nil =>
          simp only [List.length_cons, List.length_nil] at sameLength
          exact Nat.noConfusion sameLength
      | cons right rightRemaining =>
          have remainingLength :
              leftRemaining.length = rightRemaining.length :=
            Nat.succ.inj sameLength
          simp only [FiniteProduct.List.pointwiseScalarProduct, FiniteProduct.List.scalarProduct,
            inductionHypothesis rightRemaining remainingLength]
          ring1

end Purelib.Algebra.FiniteProduct.List

end
