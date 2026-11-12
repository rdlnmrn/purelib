module

public import Purelib.Polynomial.Laurent.Evaluation
import Purelib.Algebra.Power.Gaussian.Signed.Secant
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original finite Laurent products and their source domains

Products retain the two original Laurent owners and their common guarded
domain. Their combined finite term list is a separately certified algebraic
extension; cancelling signed powers does not erase an original zero guard.
-/

namespace Purelib.Polynomial.Laurent.Basic.LaurentTerm

open Purelib.Data
open Purelib.Algebra.Power.Gaussian

/-- Multiply the original coefficients and add their retained signed exponents. -/
@[expose] public def mul (left right : LaurentTerm) : LaurentTerm :=
  ⟨left.coefficient * right.coefficient, Int.Exponent.add left.exponent right.exponent⟩

/-- Term multiplication preserves evaluation on the common original guarded domain. -/
public theorem eval_mul (left right : LaurentTerm) (point : Gaussian.Basic.Canonical)
    (leftDefined : left.DefinedAt point) (rightDefined : right.DefinedAt point) :
    (left.mul right).eval point = left.eval point * right.eval point := by
  change (left.coefficient * right.coefficient) *
    Signed.Secant.signedPower point (Int.Exponent.add left.exponent right.exponent) =
      (left.coefficient * Signed.Secant.signedPower point left.exponent) *
        (right.coefficient * Signed.Secant.signedPower point right.exponent)
  rewrite [Signed.Secant.signedPower_add point left.exponent right.exponent leftDefined rightDefined]
  ring1

/-- The common original term domain also certifies the algebraically combined term. -/
public theorem mul_definedAt (left right : LaurentTerm) (point : Gaussian.Basic.Canonical)
    (leftDefined : left.DefinedAt point) (rightDefined : right.DefinedAt point) :
    (left.mul right).DefinedAt point := by
  intro combinedNegative
  by_cases leftZero : left.exponent.negativeMagnitude = 0
  · by_cases rightZero : right.exponent.negativeMagnitude = 0
    · exact (combinedNegative
        (Int.Exponent.negativeMagnitude_add_eq_zero left.exponent right.exponent leftZero rightZero)).elim
    · exact rightDefined rightZero
  · exact leftDefined leftZero

end Purelib.Polynomial.Laurent.Basic.LaurentTerm

namespace Purelib.Polynomial.Laurent.Arithmetic

open Purelib
open Purelib.Data
open Purelib.Polynomial.Laurent.Basic
open Purelib.Data.Gaussian.Norm.Sum.Basic.DividedDifference

/-- The actual ordered cross-product term table, retaining repeated exponent occurrences. -/
@[expose] public def productTerms (left right : List LaurentTerm) : List LaurentTerm :=
  left.flatMap (fun term => right.map term.mul)

set_option genInjectivity false in
/-- A finite product retaining both original inputs and the computed combined coefficient expression.

The symbol combines exponent pairs algebraically, while the original product
domain continues to require both input guards even after exponent cancellation. -/
public structure Product (left right : LaurentPolynomial) where
  /-- The actual finite combined Laurent expression. -/ symbol : LaurentPolynomial
  /-- The symbol retains the exact ordered source cross-product table. -/
  terms_spec : symbol.terms = productTerms left.terms right.terms

constructive_injectivity Product

/-- Construct the original finite cross-product expression once. -/
@[expose] public def multiply (left right : LaurentPolynomial) : Product left right :=
  ⟨⟨productTerms left.terms right.terms⟩, rfl⟩

namespace Product

/-- The product keeps the common domain of both original Laurent expressions. -/
@[expose] public def DefinedAt {left right : LaurentPolynomial} (_ : Product left right)
    (point : Gaussian.Basic.Canonical) : Prop := left.DefinedAt point ∧ right.DefinedAt point

/-- Evaluate the retained combined finite expression.

The comparison theorem uses the original product's common input domain. -/
@[expose] public def eval {left right : LaurentPolynomial} (product : Product left right)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical := product.symbol.eval point

/-- Evaluation preserves the original ordered concatenation of Laurent terms. -/
private theorem eval_append (point : Gaussian.Basic.Canonical) (left right : List LaurentTerm) :
    sumGaussian ((left ++ right).map fun term => term.eval point) =
      sumGaussian (left.map fun term => term.eval point) +
        sumGaussian (right.map fun term => term.eval point) := by
  induction left with
  | nil => exact (Gaussian.Basic.zero_add _).symm
  | cons term remaining inductionHypothesis =>
      change term.eval point + sumGaussian ((remaining ++ right).map fun term => term.eval point) =
        (term.eval point + sumGaussian (remaining.map fun term => term.eval point)) + _
      rewrite [inductionHypothesis]
      exact (Gaussian.Basic.add_assoc _ _ _).symm

/-- A retained product row evaluates to its original left term times the right term sum. -/
private theorem eval_row (point : Gaussian.Basic.Canonical) (left : LaurentTerm)
    (leftDefined : left.DefinedAt point) :
    ∀ (right : List LaurentTerm), (∀ term ∈ right, term.DefinedAt point) →
      sumGaussian ((right.map left.mul).map fun term => term.eval point) =
        left.eval point * sumGaussian (right.map fun term => term.eval point)
  | [], _ => (Gaussian.Basic.mul_zero _).symm
  | term :: remaining, rightDefined => by
      change (left.mul term).eval point +
        sumGaussian ((remaining.map left.mul).map fun term => term.eval point) =
          left.eval point * (term.eval point + sumGaussian (remaining.map fun term => term.eval point))
      rewrite [LaurentTerm.eval_mul left term point leftDefined (rightDefined term List.mem_cons_self),
        eval_row point left leftDefined remaining
          (fun next member => rightDefined next (List.mem_cons_of_mem term member))]
      ring1

/-- The actual cross-product table evaluates to the product of the original source sums. -/
private theorem eval_productTerms (point : Gaussian.Basic.Canonical) (right : List LaurentTerm)
    (rightDefined : ∀ term ∈ right, term.DefinedAt point) :
    ∀ (left : List LaurentTerm), (∀ term ∈ left, term.DefinedAt point) →
      sumGaussian ((productTerms left right).map fun term => term.eval point) =
        sumGaussian (left.map fun term => term.eval point) *
          sumGaussian (right.map fun term => term.eval point)
  | [], _ => (Gaussian.Basic.zero_mul _).symm
  | term :: remaining, leftDefined => by
      change sumGaussian (((right.map term.mul) ++ productTerms remaining right).map
        fun term => term.eval point) =
          (term.eval point + sumGaussian (remaining.map fun term => term.eval point)) * _
      rewrite [eval_append, eval_row point term (leftDefined term List.mem_cons_self) right rightDefined,
        eval_productTerms point right rightDefined remaining
          (fun next member => leftDefined next (List.mem_cons_of_mem term member))]
      ring1

/-- The original common product domain certifies its separately combined symbol. -/
public theorem symbol_definedAt {left right : LaurentPolynomial} (product : Product left right)
    (point : Gaussian.Basic.Canonical) (defined : product.DefinedAt point) :
    product.symbol.DefinedAt point := by
  intro term member
  rewrite [product.terms_spec] at member
  obtain ⟨leftTerm, leftMember, rowMember⟩ := List.Flatten.mem_flatMap.mp member
  obtain ⟨rightTerm, rightMember, termEq⟩ := List.Map.mem_map.mp rowMember
  cases termEq
  exact LaurentTerm.mul_definedAt leftTerm rightTerm point
    (defined.1 leftTerm leftMember) (defined.2 rightTerm rightMember)

/-- The retained symbol computes the original product on both original domains. -/
public theorem eval_eq_mul {left right : LaurentPolynomial} (product : Product left right)
    (point : Gaussian.Basic.Canonical) (defined : product.DefinedAt point) :
    product.eval point = left.eval point * right.eval point := by
  change sumGaussian (product.symbol.terms.map fun term => term.eval point) = _
  rewrite [product.terms_spec]
  exact eval_productTerms point right.terms defined.2 left.terms defined.1

end Product

end Purelib.Polynomial.Laurent.Arithmetic
