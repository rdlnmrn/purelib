module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Box.Interior
import Purelib.Geometry.Projective.Chordal.Box.Separation
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Nondegenerate
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Family.Search
import Purelib.Geometry.Rational.Box.Separation
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
public import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Event.Analysis
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
public import Purelib.RootIsolation.Curve.Boundary.Event.Separation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Nondegenerate
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Request
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.Geometry.Rational.Box.Separation (SourcePersistentRegionOwnershipSeparatedAlias)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Event.Basic (SourcePersistentRegionOwnershipBoundaryEventEntryAlias)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Ownership

/-! ## Keeping a complete requested event inside one owner box -/

/-- If one rational sample of a globally controlled event has the displayed
uniform interior strip, and the global diameter target is below the strip's
projective gap, then every non-pole rational point of that complete event is
inside the same box.  This upgrades sample ownership to whole-cylinder
ownership without manufacturing a parameter root. -/
theorem controlled_event_contains_of_uniform_strip
    {p : CoefficientPolynomial}
    {reference : GaussianMatrix}
    {current : Box} {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p
      reference current denominatorMargin marginPositive atom}
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry :
      Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry
        boundary
        (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth
          boundary boxes pairwise target))
    (box : Box) {radius : Fraction.Rational} (radiusPositive : 0 < radius)
    (sampleParameter : Fraction.Rational)
    (sampleInside : entry.child.cell.interval.Contains sampleParameter)
    (sampleDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        sampleParameter ≠ 0)
    (samplePointInside : box.Contains
      (entry.parent.parent.chart.parameterization.curve.point sampleParameter))
    (sampleLeft : box.xLower + radius <
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).re)
    (sampleRight :
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).re + radius < box.xUpper)
    (sampleBottom : box.yLower + radius <
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).im)
    (sampleTop :
      (entry.parent.parent.chart.parameterization.curve.point
        sampleParameter).im + radius < box.yUpper)
    (targetLeGap : target ≤ Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap box radius)
    {parameter : Fraction.Rational}
    (parameterInside : entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    box.Contains
      (entry.parent.parent.chart.parameterization.curve.point parameter) := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let samplePoint := curve.point sampleParameter
  let point := curve.point parameter
  by_cases contained : box.Contains point
  · exact contained
  · have eventUpper := entry.chordalSq_le
        (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth_pos
          boundary boxes pairwise targetPositive)
        sampleInside parameterInside
    have leftTransport :
        Geometry.Projective.Chordal.Basic.chordalSq
            (entry.parent.parent.chart.projective sampleParameter)
            (entry.parent.parent.chart.projective parameter) =
          Geometry.Projective.Chordal.Basic.chordalSq
            (Proj.affine samplePoint)
            (entry.parent.parent.chart.projective parameter) := by
      simpa only [curve, samplePoint,
        Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
        Curve.Projective.chordalSq_projective_eq_affine
          curve sampleParameter sampleDenominatorNonzero
            (entry.parent.parent.chart.projective parameter)
    have rightEquivalent :
        (entry.parent.parent.chart.projective parameter).Equivalent
          (Proj.affine point) := by
      simpa only [curve, point,
        Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
        Curve.Projective.projective_equivalent_affine
          curve parameter denominatorNonzero
    have rightTransport :
        Geometry.Projective.Chordal.Basic.chordalSq
            (Proj.affine samplePoint)
            (entry.parent.parent.chart.projective parameter) =
          Geometry.Projective.Chordal.Basic.chordalSq
            (Proj.affine samplePoint) (Proj.affine point) :=
      Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_right
        (entry.parent.parent.chart.projective_valid parameter)
        (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate point)
        rightEquivalent (Proj.affine samplePoint)
    have affineUpper :
        Geometry.Projective.Chordal.Basic.chordalSq
            (Proj.affine samplePoint) (Proj.affine point) ≤
          entry.parent.parent.chart.uniformChordalVariationCoefficient *
            Curve.Boundary.Complete.Control.boundaryControlledRequestWidth
              boundary boxes pairwise target ^ 2 := by
      rw [← rightTransport, ← leftTransport]
      exact eventUpper
    have diameterSmall :
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
            Curve.Boundary.Complete.Control.boundaryControlledRequestWidth
              boundary boxes pairwise target ^ 2 <
          Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap box radius :=
      (entry.controlled_chordal_diameter_lt targetPositive).trans_le targetLeGap
    have affineLower : Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap box radius ≤
        Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine samplePoint) (Proj.affine point) := by
      exact Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap_le_affine_of_outside radiusPositive
        (by simpa only [curve, samplePoint] using samplePointInside)
        (by simpa only [curve, samplePoint] using sampleLeft)
        (by simpa only [curve, samplePoint] using sampleRight)
        (by simpa only [curve, samplePoint] using sampleBottom)
        (by simpa only [curve, samplePoint] using sampleTop)
        (by simpa only [curve, point] using contained)
    exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall) |>.elim

end Purelib.RootIsolation.Curve.Boundary.Event.Ownership

end

section
@[expose] public section

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Ownership

/-- Every ordered distinct pair contributes its executable event request
width to one finite list.  Duplicate orientations are harmless. -/
def pairRequestWidths
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) : List Fraction.Rational :=
  (List.finRange boxes.length).flatMap fun left =>
    (List.finRange boxes.length).filterMap fun right =>
      if different : left ≠ right then
        some
          (Curve.Boundary.Event.Separation.separatedEventRequestWidth
            entry (Data.List.Pairwise.pairwise_get_separated pairwise left right different))
      else
        none

/-- Each retained ordered pair's request occurs in the finite separation-request family. -/
theorem pairRequestWidth_mem
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (left right : Fin boxes.length) (different : left ≠ right) :
    Curve.Boundary.Event.Separation.separatedEventRequestWidth
        entry (Data.List.Pairwise.pairwise_get_separated pairwise left right different) ∈
      pairRequestWidths entry boxes pairwise := by
  simp only [pairRequestWidths, -eq_self, -iff_self]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨left, Data.List.OfFn.Basic.mem_ofFn.mpr ⟨left, rfl⟩, ?_⟩
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨right, Data.List.OfFn.Basic.mem_ofFn.mpr ⟨right, rfl⟩, ?_⟩
  rewrite [dif_pos different]
  rfl

/-- Every retained pairwise event-separation width is positive. -/
theorem pairRequestWidths_positive
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) :
    ∀ width ∈ pairRequestWidths entry boxes pairwise, 0 < width := by
  intro width member
  simp only [pairRequestWidths, -eq_self, -iff_self] at member
  rcases Data.List.Flatten.mem_flatMap.mp member with ⟨left, _leftMember, member⟩
  rcases Data.List.FilterMap.mem_filterMap.mp member with ⟨right, _rightMember, selected⟩
  split at selected
  next different =>
    have equal := Option.some.inj selected
    rw [← equal]
    exact
      Curve.Boundary.Event.Separation.separatedEventRequestWidth_pos
        entry (Data.List.Pairwise.pairwise_get_separated pairwise left right different)
  next same => cases selected

/-- One positive width below every pair-specific keep-apart request. -/
def familyEventRequestWidth
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum (pairRequestWidths entry boxes
    pairwise)

/-- The shared finite family event-separation request has positive width. -/
theorem familyEventRequestWidth_pos
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) :
    0 < familyEventRequestWidth entry boxes pairwise :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (pairRequestWidths_positive entry boxes pairwise)

/-- The shared event request is no larger than any retained ordered pair's request. -/
theorem familyEventRequestWidth_le_pair
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (left right : Fin boxes.length) (different : left ≠ right) :
    familyEventRequestWidth entry boxes pairwise ≤
      Curve.Boundary.Event.Separation.separatedEventRequestWidth
        entry (Data.List.Pairwise.pairwise_get_separated pairwise left right different) :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (pairRequestWidth_mem entry boxes pairwise left right different)

/-- At the family-wide request width, one event cannot explicitly meet two
distinct members of the separated family. -/
theorem familyEventRequest_not_spanning
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.request (familyEventRequestWidth entry boxes
        pairwise)).cell.interval.Contains
        leftParameter →
      (entry.request (familyEventRequestWidth entry boxes
        pairwise)).cell.interval.Contains
        rightParameter →
      entry.chart.parameterization.curve.denominatorAt leftParameter ≠ 0 →
      entry.chart.parameterization.curve.denominatorAt rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftParameterInside rightParameterInside
    leftDenominatorNonzero rightDenominatorNonzero leftPointInside
    rightPointInside
  let separated := Data.List.Pairwise.pairwise_get_separated pairwise left right different
  let familyWidth := familyEventRequestWidth entry boxes pairwise
  let pairWidth :=
    Curve.Boundary.Event.Separation.separatedEventRequestWidth
      entry separated
  have familyPositive : 0 < familyWidth :=
    familyEventRequestWidth_pos entry boxes pairwise
  have pairPositive : 0 < pairWidth :=
    Curve.Boundary.Event.Separation.separatedEventRequestWidth_pos
      entry separated
  have widthOrder : familyWidth ≤ pairWidth := by
    simpa only [familyWidth, pairWidth, separated] using
      familyEventRequestWidth_le_pair entry boxes pairwise left right different
  have squareOrder : familyWidth ^ 2 ≤ pairWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct familyPositive.le widthOrder 2
  have coefficientNonnegative :=
    entry.chart.uniformChordalVariationCoefficient_nonneg
  have familyDiameterLe :
      entry.chart.uniformChordalVariationCoefficient * familyWidth ^ 2 ≤
        entry.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  have pairDiameterSmall :
      entry.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 <
        Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
          separated := by
    simpa only [pairWidth,
      Curve.Boundary.Event.Separation.separatedEventRequestWidth]
      using
        Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
          coefficientNonnegative
          (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos
            separated)
  exact
    Curve.Boundary.Event.Separation.requested_event_not_spanning_with_gap
      entry
      (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
        separated)
      (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_le_affine
        separated)
      familyWidth familyPositive (familyDiameterLe.trans_lt pairDiameterSmall)
      leftParameterInside rightParameterInside leftDenominatorNonzero
      rightDenominatorNonzero leftPointInside rightPointInside

set_option genInjectivity false in
/-- A finite region index together with its explicit meeting certificate. -/
structure FamilyRequestMeeting
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) where
  /-- The original family index of the met box. -/ index : Fin boxes.length
  /-- The retained rational witness that the requested event meets this indexed box. -/ meeting :
    Curve.Boundary.Event.Separation.SourcePersistentRegionOwnershipRequestMeetingAlias entry
    (familyEventRequestWidth entry boxes pairwise) (boxes.get index)

constructive_injectivity FamilyRequestMeeting

/-- The family-wide request admits at most one explicitly witnessed owner. -/
theorem FamilyRequestMeeting.index_unique
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary} {boxes : List
      Box}
    {pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias}
    (left right : FamilyRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (familyEventRequest_not_spanning entry boxes pairwise
      left.index right.index same
      left.meeting.parameterInside right.meeting.parameterInside
      left.meeting.denominatorNonzero right.meeting.denominatorNonzero
      left.meeting.pointInside right.meeting.pointInside).elim

/-! ## Executable classification of one displayed event sample -/

set_option genInjectivity false in
/-- A denominator-safe rational parameter computed inside one requested
event interval. -/
structure NonpoleRequestSample
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (epsilon :
      Fraction.Rational) where
  /-- The exact rational parameter computed within the requested event interval. -/ parameter : Fraction.Rational
  /-- The computed parameter lies inside the retained event interval. -/ parameterInside : (entry.request
    epsilon).cell.interval.Contains parameter
  /-- The original chart denominator is nonzero at the computed parameter. -/ denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0

constructive_injectivity NonpoleRequestSample

/-- Execute a bounded interior search against the represented denominator
quadrance.  Chart nondegeneracy proves that polynomial is nonzero, and the
selected nonzero evaluation is exactly a non-pole affine parameter. -/
def nonpoleRequestSample
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (epsilon :
      Fraction.Rational) :
    NonpoleRequestSample entry epsilon := open Purelib.Data in by
  let curve := entry.chart.parameterization.curve
  let interval := (entry.request epsilon).cell.interval
  let denominatorPolynomial :=
    Curve.Coordinates.denominatorNormSq curve
  have chartMember :=
    Curve.Boundary.Event.Analysis.chart_mem_of_analysis_mem
      boundary entry.analysisMember
  have nondegenerate :=
    Geometry.Projective.Hermitian.Chart.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive entry.chart
        chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [interval] using (entry.request epsilon).cell.proper
  let parameter := Dense.Rational.Nonzero.Search.Interval.interiorSearchValue
    denominatorPolynomial denominatorPolynomial.natDegree intervalProper
      nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  have specification :=
    Dense.Rational.Nonzero.Search.Interval.interiorSearchValue_spec
      denominatorPolynomial denominatorPolynomial.natDegree intervalProper
        nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  exact
    { parameter := parameter
      parameterInside := ⟨specification.2.1.le, specification.2.2.le⟩
      denominatorNonzero := by
        intro denominatorZero
        apply specification.1
        change denominatorPolynomial.eval parameter = 0
        rw [show denominatorPolynomial.eval parameter =
            Data.Gaussian.Norm.Basic.normSq
              (curve.denominatorAt parameter) by
              exact Curve.Coordinates.eval_denominatorNormSq
                curve parameter,
          denominatorZero,
          Gaussian.Norm.Basic.normSq_zero] }

set_option genInjectivity false in
/-- Total finite result for one explicit non-pole parameter in the
family-wide event request: either its affine curve point has a uniquely
determined region owner, or it is certified outside every displayed box. -/
inductive SampleRegionClassification
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (parameter : Fraction.Rational)
    (parameterInside :
      (entry.request (familyEventRequestWidth entry boxes
        pairwise)).cell.interval.Contains
        parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0) where
  /-- The retained actual sample meets a box in the original family. -/ | meeting (owner :
    FamilyRequestMeeting entry boxes pairwise)
  /-- The retained actual sample lies outside every original family box. -/ | outside (proof : ∀ index : Fin
    boxes.length,
      ¬(boxes.get index).Contains
        (entry.chart.parameterization.curve.point parameter))

constructive_injectivity SampleRegionClassification

/-- Execute all finite box-membership comparisons for one displayed event
sample and retain either its owner certificate or all negative results. -/
def classifySample
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias)
    (parameter : Fraction.Rational)
    (parameterInside :
      (entry.request (familyEventRequestWidth entry boxes
        pairwise)).cell.interval.Contains
        parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    SampleRegionClassification entry boxes pairwise parameter
      parameterInside denominatorNonzero := by
  let point := entry.chart.parameterization.curve.point parameter
  match found : Box.Family.Search.findContainingBoxIndex boxes point with
  | some index =>
      exact .meeting
        { index := index
          meeting :=
            { parameter := parameter
              parameterInside := parameterInside
              denominatorNonzero := denominatorNonzero
              pointInside := Box.Family.Search.findContainingBoxIndex_sound boxes point index
                found } }
  | none =>
      exact .outside (Box.Family.Search.findContainingBoxIndex_none boxes point found)

set_option genInjectivity false in
/-- Fully computed sample/classification pair for one family-wide event
request. -/
structure RequestedEventSampleClassification
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) where
  /-- The actual computed nonpole sample of the requested event. -/ sample :
    NonpoleRequestSample entry
    (familyEventRequestWidth entry boxes pairwise)
  /-- The classification of this exact retained sample in the original box family. -/ classification :
    SampleRegionClassification entry boxes pairwise
    sample.parameter sample.parameterInside sample.denominatorNonzero

constructive_injectivity RequestedEventSampleClassification

/-- Compute a non-pole parameter in the family-wide request and immediately
classify its affine point against every displayed region. -/
def classifyRequestedEventSample
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : SourcePersistentRegionOwnershipBoundaryEventEntryAlias boundary) (boxes : List
      Box)
    (pairwise : boxes.Pairwise SourcePersistentRegionOwnershipSeparatedAlias) :
    RequestedEventSampleClassification entry boxes pairwise :=
  let sample := nonpoleRequestSample entry
    (familyEventRequestWidth entry boxes pairwise)
  { sample := sample
    classification := classifySample entry boxes pairwise sample.parameter
      sample.parameterInside sample.denominatorNonzero }

end Purelib.RootIsolation.Curve.Boundary.Event.Ownership

end
