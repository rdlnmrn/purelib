module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Box.Separation
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
public import Purelib.RootIsolation.Curve.Boundary.Event.Request
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Event.Basic (BoundaryEventEntry)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Separating persistent CCL events across winding regions

Finite winding boxes and finite boundary-event cylinders now shrink in the
same squared-chordal metric.  This module supplies the missing quantitative
separation bridge: a positive coordinate gap between two rational boxes gives
a positive projective gap between all of their affine points.  Consequently a
sufficiently narrow nonzero boundary-event cylinder cannot meet both boxes.

Every bound is a displayed constructive rational.  No point at infinity,
completed root, compactness argument, or selected limiting parameter occurs.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Separation

/-- Coefficient-computed positive request width for keeping one boundary
event inside at most one of two separated winding regions. -/
@[expose] def separatedEventRequestWidth
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth entry.chart.uniformChordalVariationCoefficient
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap separated)

/-- The coefficient-computed request width for the two separated boxes is positive. -/
theorem separatedEventRequestWidth_pos
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    0 < separatedEventRequestWidth entry separated :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    entry.chart.uniformChordalVariationCoefficient_nonneg
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos separated)

/-- After requesting an event cylinder whose certified diameter is below the
positive gap between two separated boxes, that one event cannot contain
non-pole parameters whose affine images lie in both boxes.  This is the
finite keep-apart statement needed before assigning a boundary event to one
winding region. -/
theorem requested_event_not_spanning_with_gap
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (gap : Fraction.Rational)
    (gapLower : ∀ {leftPoint rightPoint : Gaussian.Basic.Canonical},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint))
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (diameterSmall :
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 < gap)
    {leftParameter rightParameter : Fraction.Rational}
    (leftParameterInside :
      (entry.request epsilon).cell.interval.Contains leftParameter)
    (rightParameterInside :
      (entry.request epsilon).cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.chart.parameterization.curve.point rightParameter)) : False := open Purelib.RationalFunctions in by
  let curve := entry.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_request_le epsilon epsilonPositive
    leftParameterInside rightParameterInside
  have leftTransport :
      Geometry.Projective.Chordal.Basic.chordalSq
          (entry.chart.projective leftParameter)
          (entry.chart.projective rightParameter) =
        Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.chart.projective rightParameter) := by
    simpa only [curve, leftPoint,
      Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.chart.projective rightParameter)
  have rightEquivalent :
      (entry.chart.projective rightParameter).Equivalent
        (Proj.affine rightPoint) := by
    simpa only [curve, rightPoint,
      Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.chart.projective rightParameter) =
        Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_right
      (entry.chart.projective_valid rightParameter)
      (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (Proj.affine leftPoint)
  have affineUpper :
      Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) ≤
        entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
    rw [← rightTransport, ← leftTransport]
    exact eventUpper
  have affineLower : gap ≤
      Geometry.Projective.Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- The computed request width keeps one event from meeting both separated
boxes.  All inputs are finite rational certificates. -/
theorem separatedEventRequest_not_spanning
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.request (separatedEventRequestWidth entry
        separated)).cell.interval.Contains
        leftParameter →
      (entry.request (separatedEventRequestWidth entry
        separated)).cell.interval.Contains
        rightParameter →
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
      leftBox.Contains
        (entry.chart.parameterization.curve.point leftParameter) →
      rightBox.Contains
        (entry.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftParameterInside rightParameterInside
    leftDenominatorNonzero rightDenominatorNonzero leftPointInside
    rightPointInside
  apply requested_event_not_spanning_with_gap entry
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap separated)
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_le_affine separated)
    (separatedEventRequestWidth entry separated)
    (separatedEventRequestWidth_pos entry separated)
    ?_ leftParameterInside rightParameterInside leftDenominatorNonzero
      rightDenominatorNonzero leftPointInside rightPointInside
  simpa only [separatedEventRequestWidth] using
    Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
      entry.chart.uniformChordalVariationCoefficient_nonneg
      (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos separated)

set_option genInjectivity false in
/-- Explicit finite evidence that one displayed parameter of a requested
event maps into a rational box.  This is Type-valued data, not a root set or
an ambient existential search. -/
structure RequestMeeting
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    (epsilon : Fraction.Rational) (box : Box) where
  /-- The displayed rational parameter witnessing the meeting. -/ parameter : Fraction.Rational
  /-- The parameter belongs to the original event's requested interval. -/ parameterInside :
    (entry.request epsilon).cell.interval.Contains parameter
  /-- The chart denominator is nonzero at the retained parameter. -/ denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The affine chart point at the retained parameter lies in the supplied box. -/ pointInside :
    box.Contains (entry.chart.parameterization.curve.point parameter)

constructive_injectivity RequestMeeting

/-- At the computed width, explicit meetings of one event with two separated
regions are incompatible. -/
theorem separatedEventRequest_meetings_incompatible
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox)
    (leftMeeting : RequestMeeting entry
      (separatedEventRequestWidth entry separated) leftBox)
    (rightMeeting : RequestMeeting entry
      (separatedEventRequestWidth entry separated) rightBox) : False :=
  separatedEventRequest_not_spanning entry separated
    leftMeeting.parameterInside rightMeeting.parameterInside
    leftMeeting.denominatorNonzero rightMeeting.denominatorNonzero
    leftMeeting.pointInside rightMeeting.pointInside

/-- Fully executable-width form of the keep-apart theorem: the coefficient
and the finite box gap compute a positive request width at which one event
cannot span the two separated regions. -/
theorem request_not_spanning_separated_boxes
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry :
      BoundaryEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∃ epsilon : Fraction.Rational, 0 < epsilon ∧
      ∀ {leftParameter rightParameter : Fraction.Rational},
        (entry.request epsilon).cell.interval.Contains leftParameter →
        (entry.request epsilon).cell.interval.Contains rightParameter →
        entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
        entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
        leftBox.Contains
          (entry.chart.parameterization.curve.point leftParameter) →
        rightBox.Contains
          (entry.chart.parameterization.curve.point rightParameter) →
        False := by
  exact ⟨separatedEventRequestWidth entry separated,
    separatedEventRequestWidth_pos entry separated,
    separatedEventRequest_not_spanning entry separated⟩

end Purelib.RootIsolation.Curve.Boundary.Event.Separation

end

section
public section

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Separation
/-- The same explicit parameter-and-containment witness for the retained boundary event and requested box. -/
abbrev SourcePersistentRegionOwnershipRequestMeetingAlias
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (epsilon :
      Fraction.Rational) (box : Box) :=
  RequestMeeting
    entry epsilon box
end Purelib.RootIsolation.Curve.Boundary.Event.Separation

end
