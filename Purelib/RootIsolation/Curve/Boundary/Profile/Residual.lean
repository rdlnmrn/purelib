module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
public import Purelib.RootIsolation.Curve.Boundary.Profile.Separation
public import Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Original-polynomial residuals on condition-profile CCL events

A condition profile is a further finite factor of one squarefree curve-gcd
factor.  Its Sturm request directly bounds only that final profile factor.
This module multiplies through the displayed finite cofactors, then through
the two cleared curve coordinates, to recover a coefficient-computed bound
for the original Gaussian polynomial at every displayed affine point of the
requested profile cylinder.

All parameters and coefficients are constructive rationals.  The estimates
hold pointwise throughout a finite request interval and make no root
existence assertion.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry

section Profile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

section BoundaryProfileEventEntry

/-- Coefficient-computable original-polynomial residual bound for portions
of this condition-profile boundary event lying in a displayed affine box. -/
@[expose] def
  affineResidualCoefficient
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) : Fraction.Rational :=
  Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient (targetBox := targetBox) entry.event.1

/-- The original profile event's affine residual coefficient for the supplied target box is nonnegative. -/
theorem
  affineResidualCoefficient_nonneg
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) : 0 ≤
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient entry targetBox :=
  Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient_nonneg
    (targetBox := targetBox) entry.event.1

/-- Every affine meeting of a requested profile event with `targetBox` has a
uniformly small original-polynomial residual. -/
theorem
  normSq_eval_point_requestAt_le_of_inside
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (parameterInside :
      (entry.requestAt epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.parent.chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (entry.parent.chart.parameterization.curve.point parameter)) ≤
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient entry targetBox * epsilon ^ 2
        :=
  Curve.Event.Profile.Residual.Lift.ProfileEventLeaf.normSq_eval_point_request_le_of_inside entry.event.2
    epsilon positive parameter parameterInside denominatorNonzero pointInside

/-- The explicit residual budget at the same request used for profile signs
and separated-region ownership. -/
@[expose] def
  combinedAffineResidualBudget
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) : Fraction.Rational :=
  Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient entry targetBox *
    Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
      entry boxes pairwise ^ 2

/-- The residual budget at the shared sign-and-region-separation request is nonnegative. -/
theorem
  combinedAffineResidualBudget_nonneg
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) :
    0 ≤ Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.combinedAffineResidualBudget entry boxes pairwise
      targetBox :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg entry targetBox)
    (Fraction.Order.Arithmetic.sq_nonneg_direct
      (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
        entry boxes pairwise))

/-- Event-wide original-polynomial residual bound at the shared finite
sign-and-ownership request. -/
theorem
  normSq_eval_point_combined_le_of_inside
    (entry :
      BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) (parameter : Fraction.Rational)
    (parameterInside :
      (entry.requestAt
        (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
          entry boxes pairwise)).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.parent.chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (entry.parent.chart.parameterization.curve.point parameter)) ≤
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.combinedAffineResidualBudget entry boxes pairwise
        targetBox :=
  Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.normSq_eval_point_requestAt_le_of_inside entry targetBox
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
      entry boxes pairwise)
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth_pos
      entry boxes pairwise)
    parameter parameterInside denominatorNonzero pointInside

end BoundaryProfileEventEntry
end Profile

end Purelib.RootIsolation.Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry

end
