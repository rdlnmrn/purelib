module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
public import Purelib.RootIsolation.Curve.Boundary.Profile.Located
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Located
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Boundary.Profile.Family
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Complete.Located

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}

set_option genInjectivity false in
/-- A supplied displayed rational boundary root located in the full requested
multi-chart/profile/child family. -/
structure LocatedBoundaryCompleteRequestZero
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational)
    (value : Gaussian.Basic.Canonical) where
  /-- The exact retained boundary profile child containing the supplied rational root. -/ entry :
    Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon
  /-- The retained entry belongs to the original complete requested boundary family. -/ member : entry ∈
    Curve.Boundary.Complete.Basic.boundaryCompleteRequestFamily boundary epsilon
  /-- The displayed rational parameter locating the root in the original chart. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the exact requested child interval. -/ parameterInside :
    entry.child.cell.interval.Contains parameter
  /-- The original profile factor vanishes at the retained parameter. -/ profileZero :
    entry.parent.event.1.profile.factor.polynomial.eval parameter = 0
  /-- The original chart denominator is nonzero at the retained parameter. -/ denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0
  /-- The original chart point equals the supplied Gaussian-rational root. -/ point_eq :
    entry.parent.parent.chart.parameterization.curve.point parameter = value

constructive_injectivity LocatedBoundaryCompleteRequestZero

/-- Safe pointwise completeness after full requested subdivision: start from
one supplied Gaussian-rational polynomial root and locate its retained child.
No nonzero child count is used to manufacture a root. -/
def locateBoundaryCompleteRequestZero
    (degreePositive : 0 < p.natDegree)
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (epsilon : Fraction.Rational)
    (value : Gaussian.Basic.Canonical)
    (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq
        (Geometry.Projective.Homography.Basic.denominator reference value)) :
    LocatedBoundaryCompleteRequestZero boundary epsilon value := by
  let located :=
    Curve.Boundary.Profile.Located.locateBoundaryProfileRoot
      degreePositive boundary value inside onBoundary root denominatorLower
  let childLocated := Curve.Event.Profile.Complete.Located.locateCompleteRequestZero located.entry.event.2 epsilon
    located.parameter located.parameterInside located.profileZero
  let entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon :=
    { parent := located.entry
      parentMember := located.member
      child := childLocated.entry
      childMember := childLocated.member }
  exact
    { entry := entry
      member := Curve.Boundary.Complete.Basic.mem_boundaryCompleteRequestFamily boundary epsilon
        located.entry located.member childLocated.entry childLocated.member
      parameter := located.parameter
      parameterInside := childLocated.contains
      profileZero := located.profileZero
      denominatorNonzero := located.denominatorNonzero
      point_eq := located.point_eq }

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Complete.Located

end
