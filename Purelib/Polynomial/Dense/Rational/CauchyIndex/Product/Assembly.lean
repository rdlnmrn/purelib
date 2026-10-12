module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Degenerate.Partition
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Partition
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Product formulas for arbitrary coordinate rows

The original six Boolean zero tests retain their order and choose the
nondegenerate or coordinate-degenerate partition of the same cleared interval.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.CauchyIndex.Product

/-- Clearances certify the complete auxiliary product formula for arbitrary coordinate polynomials.

The original six finite Boolean zero tests choose the ordinary partition or
one of the retained degenerate-coordinate scenarios. Both clearances and
the displayed real and imaginary product identities are retained. -/
public theorem auxiliaryProductFormula_of_clearances
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (proper : root.lower < root.upper)
    (left : Clearance.Pair.Basic.Certificate A B root) (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Basic.AuxiliaryProductFormula A B C D E H root.lower root.upper := by
  have leftStart := left.eval_ne_zero
    (x := root.lower) ⟨le_rfl, root.valid⟩
  have rightStart := right.eval_ne_zero
    (x := root.lower) ⟨le_rfl, root.valid⟩
  have leftStop := left.eval_ne_zero
    (x := root.upper) ⟨root.valid, le_rfl⟩
  have rightStop := right.eval_ne_zero
    (x := root.upper) ⟨root.valid, le_rfl⟩
  by_cases BZero : B.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity (Or.inl BZero)
  have BNonzero : B.isZero = false := by
    cases value : B.isZero with
    | false => rfl
    | true => exact False.elim (BZero value)
  by_cases DZero : D.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inl DZero))
  have DNonzero : D.isZero = false := by
    cases value : D.isZero with
    | false => rfl
    | true => exact False.elim (DZero value)
  by_cases AZero : A.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inl AZero)))
  have ANonzero : A.isZero = false := by
    cases value : A.isZero with
    | false => rfl
    | true => exact False.elim (AZero value)
  by_cases CZero : C.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inl CZero))))
  have CNonzero : C.isZero = false := by
    cases value : C.isZero with
    | false => rfl
    | true => exact False.elim (CZero value)
  by_cases HZero : H.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl HZero)))))
  have HNonzero : H.isZero = false := by
    cases value : H.isZero with
    | false => rfl
    | true => exact False.elim (HZero value)
  by_cases EZero : E.isZero = true
  · exact Degenerate.Partition.auxiliaryProductFormula_of_degenerate_coordinates
      proper left right realIdentity imagIdentity
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr EZero)))))
  have ENonzero : E.isZero = false := by
    cases value : E.isZero with
    | false => rfl
    | true => exact False.elim (EZero value)
  exact Partition.auxiliaryProductFormula_of_nondegenerate_coordinates
    ANonzero BNonzero CNonzero DNonzero ENonzero HNonzero proper
    left right realIdentity imagIdentity
    leftStart rightStart leftStop rightStop

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
