module
import Purelib.Data.List.Filter
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Product.List
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Box.Conditions

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

namespace Purelib.RationalFunctions.Curve.Box

open Purelib
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
open Purelib.Data.List
open Purelib.Data.Rat

public section

/-- Filter out identically zero polynomials from the four denominator-cleared box conditions. -/
@[expose] def activeConditionPolynomials (curve : Curve.RationalCurve) (box : Rational.Box) :
    List Dense.Rational.Basic.CoordinatePolynomial :=
  (Curve.Box.conditionPolynomials curve box).filter fun polynomial =>
    polynomial.isZero = false

/-- Every retained active box-condition polynomial is nonzero.

Every member retains the acceptance certificate of the original Boolean filter.
That retained decision proves the same polynomial has a false zero test. -/
theorem activeConditionPolynomials_all_nonzero
    (curve : Curve.RationalCurve) (box : Rational.Box) :
    ∀ polynomial ∈ Curve.Box.activeConditionPolynomials curve box,
      polynomial.isZero = false := by
  intro polynomial member
  exact of_decide_eq_true (Filter.mem_filter.mp member).2

/-- Multiply all nonzero denominator-cleared box conditions into one guard polynomial.

Identically zero edge conditions are omitted, so the product remains a represented nonzero polynomial. -/
@[expose] def conditionGuard (curve : Curve.RationalCurve) (box : Rational.Box) :
    Dense.Rational.Basic.CoordinatePolynomial :=
  Dense.Rational.Product.List.polynomialProduct
    (Curve.Box.activeConditionPolynomials curve box)

/-- The common box-condition guard is a nonzero polynomial. -/
theorem conditionGuard_isZero_false (curve : Curve.RationalCurve) (box : Rational.Box) :
    (Curve.Box.conditionGuard curve box).isZero = false := by
  exact Dense.Rational.Product.List.polynomialProduct_isZero_false
    (Curve.Box.activeConditionPolynomials_all_nonzero curve box)

/-- An active box condition cannot vanish where the common guard is nonzero. -/
theorem eval_ne_zero_of_active_condition
    {curve : Curve.RationalCurve} {box : Rational.Box} {polynomial :
      Dense.Basic.RationalPolynomial}
    {parameter : Fraction.Rational}
    (member : polynomial ∈ Curve.Box.activeConditionPolynomials curve box)
    (guardNonzero : (Curve.Box.conditionGuard curve box).eval parameter ≠ 0) :
    polynomial.eval parameter ≠ 0 := by
  exact Dense.Rational.Product.List.eval_ne_zero_of_mem_of_polynomialProduct
    member guardNonzero

/-- Every box-condition polynomial is either identically zero or retained in the active list.

The original Boolean zero test selects the displayed alternative. Its false
branch retains the supplied occurrence through the same condition filter. -/
theorem condition_zero_or_active
    {curve : Curve.RationalCurve} {box : Rational.Box} {polynomial :
      Dense.Basic.RationalPolynomial}
    (member : polynomial ∈ Curve.Box.conditionPolynomials curve box) :
    polynomial.isZero = true ∨
      polynomial ∈ Curve.Box.activeConditionPolynomials curve box := by
  cases zero : polynomial.isZero with
  | true => exact Or.inl rfl
  | false =>
      exact Or.inr (Filter.mem_filter.mpr ⟨member, decide_eq_true zero⟩)

end

end Purelib.RationalFunctions.Curve.Box
