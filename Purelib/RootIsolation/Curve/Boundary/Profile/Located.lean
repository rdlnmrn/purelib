module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Event.Coverage
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
public import Purelib.RootIsolation.Curve.Boundary.Profile.Family
public import Purelib.RootIsolation.Curve.Event.Profile.Located
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
import Purelib.RootIsolation.Curve.Boundary.Event.Family
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Family

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Located

set_option genInjectivity false in
/-- A supplied displayed rational polynomial root, located in the complete
condition-profile boundary family. -/
structure LocatedBoundaryProfileEvent
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian.Basic.Canonical) where
  /-- The original boundary profile-event entry containing the displayed rational root. -/ entry :
    RootIsolation.Curve.Boundary.Profile.BoundaryProfileEventEntry boundary
  /-- The retained entry belongs to the original complete boundary-profile family. -/ member : entry ∈
    Curve.Boundary.Profile.Family.boundaryProfileEventFamily boundary
  /-- The displayed rational parameter locating the root in the retained chart. -/ parameter : Fraction.Rational
  /-- The parameter belongs to the retained profile event's interval. -/ parameterInside :
    entry.event.2.cell.interval.Contains parameter
  /-- The retained parameter is an exact zero of the original profile factor. -/ profileZero :
    entry.event.1.profile.factor.polynomial.eval parameter = 0
  /-- The retained chart denominator is nonzero at the parameter. -/ denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The original chart point at the retained parameter equals the supplied affine root. -/ point_eq :
    entry.parent.chart.parameterization.curve.point parameter = value

constructive_injectivity LocatedBoundaryProfileEvent

/-- Safe pointwise completeness direction: locate a supplied rational root
in the computed boundary profile family. -/
def locateBoundaryProfileRoot
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Geometry.Projective.Hermitian.Atom}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian.Basic.Canonical) (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq
        (Geometry.Projective.Homography.Basic.denominator reference value)) :
    LocatedBoundaryProfileEvent boundary value := by
  let located :=
    Curve.Boundary.Event.Coverage.locateBoundaryRoot
      degreePositive boundary value inside onBoundary root denominatorLower
  have parameterInsideChart :
      located.entry.chart.cell.interval.Contains located.parameter := by
    have refines := located.entry.event.2.cell_refines_chart
    exact ⟨refines.1.trans located.parameterInside.1,
      located.parameterInside.2.trans refines.2⟩
  let profileLocated :=
    Curve.Event.Profile.Located.locateProfileEvent
      located.entry.event.1 located.parameter parameterInsideChart
        located.factorZero
  let entry : RootIsolation.Curve.Boundary.Profile.BoundaryProfileEventEntry boundary :=
    { parent := located.entry
      parentMember := located.member
      event := profileLocated.entry
      eventMember := profileLocated.member }
  exact
    { entry := entry
      member := Curve.Boundary.Profile.Family.mem_boundaryProfileEventFamily boundary located.entry
        located.member profileLocated.entry profileLocated.member
      parameter := located.parameter
      parameterInside := profileLocated.contains
      profileZero := profileLocated.profileZero
      denominatorNonzero := located.denominatorNonzero
      point_eq := located.point_eq }

end Purelib.RootIsolation.Curve.Boundary.Profile.Located

end
