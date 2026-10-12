module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RootIsolation.Curve.Clearance.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Exclusion.Uniform
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Uniform polynomial residual clearance on rational curve arcs

A constant cleared-coordinate gcd gives a positive coefficient-computed
lower bound for the denominator-cleared polynomial value on any displayed
finite parameter interval.  Dividing by a finite upper bound for the Horner
denominator power turns that into a positive lower bound for the original
polynomial residual at every non-pole point of the curve.

The final construction feeds that uniform residual directly to the
winding-one exclusion theorem.  One finite box refinement then excludes the
entire clear curve arc, rather than excluding only a selected rational point.
-/

namespace Purelib.RootIsolation.Curve.Clearance.Residual
namespace Certificate

/-- Refine a winding-one box far enough that no non-pole point of this clear
curve interval can remain in the box. -/
def refinePast
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
      {interval :
      Bounds}
    (clearance : Curve.Clearance.Residual.Certificate p curve interval) {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient) :
    WindingOneState p ambient :=
  Track.Exclusion.Uniform.refinePastUniformMargin
    track current clearance.bound clearance.positive

/-- Excluding the clear curve interval preserves containment in the original winding-one box. -/
theorem refinePast_refines
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
      {interval :
      Bounds}
    (clearance : Curve.Clearance.Residual.Certificate p curve interval) {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient) :
    (clearance.refinePast track current).box.Refines current.box :=
  Track.Exclusion.Uniform.refinePastUniformMargin_refines
    track current clearance.bound clearance.positive

/-- Every non-pole point on the original clear curve interval lies outside the returned refinement. -/
theorem refinePast_excludes
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
      {interval :
      Bounds}
    (clearance : Curve.Clearance.Residual.Certificate p curve interval) {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (parameter : Fraction.Rational) (inside : interval.Contains parameter)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    ¬(clearance.refinePast track current).box.Contains
      (curve.point parameter) :=
  Track.Exclusion.Uniform.refinePastUniformMargin_excludes
    degreePositive track current clearance.bound clearance.positive
      (curve.point parameter)
      (clearance.lower parameter inside denominatorNonzero)

end Certificate

end Purelib.RootIsolation.Curve.Clearance.Residual

end
