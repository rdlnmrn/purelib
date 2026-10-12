module
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Convolution
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition
public import Purelib.Polynomial.Ascending.Rational.Jet.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Ascending.Rational.Jet.Basic (TaylorJet)

open Purelib.Algebra

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.Polynomial.Ascending.Rational.Jet.Basic.TaylorJet
section

/-- Evaluation preserves addition of Taylor jets. -/
@[simp] theorem evaluate_add (left right :
  TaylorJet)
    (increment : Gaussian.Basic.Canonical) :
    (left.add right).evaluate increment =
      left.evaluate increment + right.evaluate increment :=
  Ascending.Rational.GaussianEvaluation.eval_add
    left.polynomial right.polynomial increment

/-- Evaluation preserves multiplication of Taylor jets. -/
@[simp] theorem evaluate_mul (left right :
  TaylorJet)
    (increment : Gaussian.Basic.Canonical) :
    (left.mul right).evaluate increment =
      left.evaluate increment * right.evaluate increment :=
  Ascending.Rational.GaussianEvaluation.eval_mul
    left.polynomial right.polynomial increment

/-- Evaluation of composed jets equals successive evaluation of the inner and outer jets. -/
@[simp] theorem evaluate_compose (outer inner :
  TaylorJet)
    (increment : Gaussian.Basic.Canonical) :
    (outer.compose inner).evaluate increment =
      outer.evaluate (inner.evaluate increment) :=
  Ascending.Rational.GaussianEvaluation.Composition.eval_compose
    outer.polynomial inner.polynomial increment

/-- Every coefficient of a product is the displayed finite Cauchy row. -/
theorem coefficient_mul (left right :
  TaylorJet) (degree : Nat) :
    (left.mul right).coefficient degree =
      FiniteSum.Prefix.coordinateSum
        (fun leftDegree =>
          left.coefficient leftDegree *
            right.coefficient (degree - leftDegree))
        (degree + 1) :=
  Ascending.Rational.Convolution.coefficient_mul
    left.polynomial right.polynomial degree

/-- The finite higher-jet product rule holds coefficient by coefficient. -/
theorem derivative_mul (left right :
  TaylorJet) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (left.mul right).derivative.polynomial
      ((left.derivative.mul right).add
        (left.mul right.derivative)).polynomial :=
  Ascending.Rational.Derivative.derivative_mul
    left.polynomial right.polynomial

end

end Purelib.Polynomial.Ascending.Rational.Jet.Basic.TaylorJet

end
