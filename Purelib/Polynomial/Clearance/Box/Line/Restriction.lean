module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Basic

/-- Restrict the retained line-clearance certificate to a refined box without recomputing its bound. -/
def VerticalLineClearance.restrict
    {p : CoefficientPolynomial} {ambient small : Box} {x : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.VerticalLineClearance p ambient x)
    (refines : small.Refines ambient) : Clearance.Box.Line.Basic.VerticalLineClearance p small x where
  bound := clearance.bound
  positive := clearance.positive
  lower := fun y lower upper => clearance.lower y
    (refines.2.2.1.trans lower) (upper.trans refines.2.2.2)

/-- Restriction retains the original line-clearance bound exactly. -/
@[simp] theorem VerticalLineClearance.restrict_bound
    {p : CoefficientPolynomial} {ambient small : Box} {x : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.VerticalLineClearance p ambient x)
    (refines : small.Refines ambient) :
    (clearance.restrict refines).bound = clearance.bound := rfl

/-- Restrict the retained line-clearance certificate to a refined box without recomputing its bound. -/
def HorizontalLineClearance.restrict
    {p : CoefficientPolynomial} {ambient small : Box} {y : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient y)
    (refines : small.Refines ambient) : Clearance.Box.Line.Basic.HorizontalLineClearance p small y where
  bound := clearance.bound
  positive := clearance.positive
  lower := fun x lower upper => clearance.lower x
    (refines.1.trans lower) (upper.trans refines.2.1)

/-- Restriction retains the original line-clearance bound exactly. -/
@[simp] theorem HorizontalLineClearance.restrict_bound
    {p : CoefficientPolynomial} {ambient small : Box} {y : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient y)
    (refines : small.Refines ambient) :
    (clearance.restrict refines).bound = clearance.bound := rfl
end Purelib.Polynomial.Clearance.Box.Line.Basic

end
