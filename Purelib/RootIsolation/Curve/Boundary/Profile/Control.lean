module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Family.Search
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Boundary.Profile.Residual
public import Purelib.RootIsolation.Curve.Boundary.Profile.Sample
import Purelib.RootIsolation.Curve.Boundary.Profile.Separation
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Sign
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
import Purelib.Geometry.Rational.Box.Refinement
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

open Purelib.RootIsolation.Curve.Boundary.Profile.Sample (NonpoleProfileRequestSample)
open Purelib.RootIsolation.Curve.Boundary.Profile (SourcePersistentProfileResidualBoundaryProfileEventEntryAlias)

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

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Control

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## One request below a supplied residual target in every possible owner -/

/-- Positive request width making the affine profile residual coefficient for
one displayed box smaller than `target`. -/
@[expose] def boxResidualRequestWidth
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (targetBox : Box)
    (target : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth
    (Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient entry targetBox)
    target

/-- The residual request for a positive target and a retained box has positive width. -/
theorem boxResidualRequestWidth_pos
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (targetBox : Box)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < boxResidualRequestWidth entry targetBox target :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    (Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg entry
      targetBox) targetPositive

/-- Every possible owner box contributes one executable residual width. -/
@[expose] def profileResidualRequestWidths
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (target : Fraction.Rational) : List Fraction.Rational :=
  boxes.map fun targetBox => boxResidualRequestWidth entry targetBox target

/-- Each retained box's residual width occurs in the finite family of residual requests. -/
theorem profileResidualRequestWidth_mem
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (target : Fraction.Rational) (index : Fin boxes.length) :
    boxResidualRequestWidth entry (boxes.get index) target ∈
      profileResidualRequestWidths entry boxes target :=
  Data.List.Map.mem_map.mpr ⟨boxes.get index, List.get_mem boxes index, rfl⟩

/-- Every width in the retained finite residual-request family is positive. -/
theorem profileResidualRequestWidths_positive
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    ∀ width ∈ profileResidualRequestWidths entry boxes target, 0 < width := by
  intro width member
  dsimp only [profileResidualRequestWidths] at member
  have member := Data.List.Map.mem_map.mp member
  rcases member with ⟨targetBox, _targetBoxMember, rfl⟩
  exact boxResidualRequestWidth_pos entry targetBox targetPositive

/-- A positive finite minimum below the residual width of every possible
owner box.  The empty family retains the harmless width `1`. -/
@[expose] def profileResidualFamilyRequestWidth
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (target : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    (profileResidualRequestWidths entry boxes target)

/-- The shared residual request obtained from the finite positive family has positive width. -/
theorem profileResidualFamilyRequestWidth_pos
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < profileResidualFamilyRequestWidth entry boxes target :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (profileResidualRequestWidths_positive entry boxes targetPositive)

/-- The shared residual request is no larger than the request for any retained box. -/
theorem profileResidualFamilyRequestWidth_le_box
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (target : Fraction.Rational) (index : Fin boxes.length) :
    profileResidualFamilyRequestWidth entry boxes target ≤
      boxResidualRequestWidth entry (boxes.get index) target :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (profileResidualRequestWidth_mem entry boxes target index)

/-- One request width satisfying profile signs, pairwise region separation,
and the residual target in every possible owner box. -/
@[expose] def controlledProfileRequestWidth
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) : Fraction.Rational :=
  min
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
      entry boxes pairwise)
    (profileResidualFamilyRequestWidth entry boxes target)

/-- Combining the sign, separation and residual requests preserves a positive width. -/
theorem controlledProfileRequestWidth_pos
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < controlledProfileRequestWidth entry boxes pairwise target :=
  Fraction.Order.Basic.lt_min
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth_pos
      entry boxes pairwise)
    (profileResidualFamilyRequestWidth_pos entry boxes targetPositive)

/-- The controlled profile width is no larger than the combined sign-and-separation request. -/
theorem controlledProfileRequestWidth_le_combined
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
        entry boxes pairwise :=
  Fraction.Order.Basic.min_le_left _ _

/-- The controlled profile width satisfies the retained sign request. -/
theorem controlledProfileRequestWidth_le_sign
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      Curve.Event.Profile.Sign.profileSignWidth
        entry.event.1 :=
  (controlledProfileRequestWidth_le_combined entry boxes pairwise target).trans
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth_le_sign
      entry boxes pairwise)

/-- The controlled profile width satisfies the retained family-separation request. -/
theorem controlledProfileRequestWidth_le_family
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      Curve.Boundary.Profile.Separation.profileFamilyRequestWidth
        entry boxes pairwise :=
  (controlledProfileRequestWidth_le_combined entry boxes pairwise target).trans
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth_le_family
      entry boxes pairwise)

/-- At the controlled width, the affine residual budget is strictly below
the supplied positive target for every possible owner index. -/
theorem controlledProfileResidual_lt
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (index : Fin boxes.length) :
    Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient entry
        (boxes.get index) *
      controlledProfileRequestWidth entry boxes pairwise target ^ 2 <
        target := by
  let controlled := controlledProfileRequestWidth entry boxes pairwise target
  let familyWidth := profileResidualFamilyRequestWidth entry boxes target
  let boxWidth := boxResidualRequestWidth entry (boxes.get index) target
  let coefficient := Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient
    entry (boxes.get index)
  have controlledPositive : 0 < controlled := by
    simpa only [-eq_self, -iff_self, controlled] using
      controlledProfileRequestWidth_pos entry boxes pairwise targetPositive
  have controlledLeFamily : controlled ≤ familyWidth := by
    exact (Fraction.Order.Basic.min_le_right _ _)
  have familyLeBox : familyWidth ≤ boxWidth := by
    simpa only [-eq_self, -iff_self, familyWidth, boxWidth] using
      profileResidualFamilyRequestWidth_le_box entry boxes target index
  have squareOrder : controlled ^ 2 ≤ boxWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct controlledPositive.le
      (controlledLeFamily.trans familyLeBox) 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [-eq_self, -iff_self, coefficient] using
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg entry
        (boxes.get index)
  have scaled : coefficient * controlled ^ 2 ≤
      coefficient * boxWidth ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  exact scaled.trans_lt (by
    simpa only [-eq_self, -iff_self, coefficient, boxWidth, boxResidualRequestWidth]
      using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative targetPositive)

/-- Exact affine profile classification at the controlled request width. -/
@[expose] def classifyControlledProfileEventAffine
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    Curve.Event.Profile.Classification.ProfileEventAffineClassification
      entry.event.2
        (controlledProfileRequestWidth entry boxes pairwise target) :=
  Curve.Event.Profile.Classification.classifyProfileEventAffine
    entry.event.2 (controlledProfileRequestWidth entry boxes pairwise target)
      (controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      (controlledProfileRequestWidth_le_sign entry boxes pairwise target)

/-- The controlled request remains narrow enough to meet at most one member
of the separated family. -/
theorem controlledProfileRequest_not_spanning
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.requestAt
        (controlledProfileRequestWidth entry boxes pairwise
          target)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (controlledProfileRequestWidth entry boxes pairwise
          target)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False :=
  Curve.Boundary.Profile.Separation.profileRequest_not_spanning_of_le_family
    entry boxes pairwise
      (controlledProfileRequestWidth entry boxes pairwise target)
      (controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      (controlledProfileRequestWidth_le_family entry boxes pairwise target)
      left right different

set_option genInjectivity false in
/-- An explicit owner meeting at the single sign-, separation-, and
residual-controlled request. -/
structure ControlledProfileRequestMeeting
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) where
  /-- The index of the met box in the original retained family. -/ index : Fin boxes.length
  /-- The exact rational chart parameter witnessing this meeting. -/ parameter : Fraction.Rational
  /-- The parameter lies in the retained requested child interval. -/ parameterInside : (entry.requestAt
    (controlledProfileRequestWidth entry boxes pairwise target)).cell.interval.Contains
      parameter
  /-- The original chart denominator is nonzero at the retained parameter. -/ denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The chart point at the retained parameter lies strictly inside the indexed box. -/ pointInside : (boxes.get
    index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

constructive_injectivity ControlledProfileRequestMeeting

namespace ControlledProfileRequestMeeting

/-- Two controlled meetings for the same retained child have the same original box index. -/
theorem index_unique
    {entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary}
      {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (left right : Curve.Boundary.Profile.Control.ControlledProfileRequestMeeting entry boxes pairwise
      target) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (Curve.Boundary.Profile.Control.controlledProfileRequest_not_spanning entry boxes pairwise
      targetPositive left.index right.index same left.parameterInside
      right.parameterInside left.denominatorNonzero right.denominatorNonzero
      left.pointInside right.pointInside).elim

/-- An owned displayed rational sample has original-polynomial residual
strictly below the caller's target. -/
theorem residual_lt
    {entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary}
      {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (meeting : Curve.Boundary.Profile.Control.ControlledProfileRequestMeeting entry boxes pairwise target) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.chart.parameterization.curve.point
          meeting.parameter)) < target := by
  have upper :=
    Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.normSq_eval_point_requestAt_le_of_inside
      entry (boxes.get meeting.index)
      (Curve.Boundary.Profile.Control.controlledProfileRequestWidth entry boxes pairwise target)
      (Curve.Boundary.Profile.Control.controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      meeting.parameter meeting.parameterInside meeting.denominatorNonzero
      meeting.pointInside
  exact upper.trans_lt
    (Curve.Boundary.Profile.Control.controlledProfileResidual_lt entry boxes pairwise targetPositive
      meeting.index)

/-- At the squarefree derivative threshold, every owned event sample has a
nonzero polynomial derivative.  This is the finite Newton datum needed by the
next winding-one comparison; no polynomial root is inferred. -/
theorem derivative_ne_zero
    {ambient : Box} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary}
      {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (boxesRefine : ∀ index : Fin boxes.length,
      (boxes.get index).Refines ambient)
    (meeting : Curve.Boundary.Profile.Control.ControlledProfileRequestMeeting entry boxes pairwise
      (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree
        ambient)) :
    (Dense.Gaussian.GCD.derivative p).eval
        (entry.parent.chart.parameterization.curve.point
          meeting.parameter) ≠ 0 := by
  let point := entry.parent.chart.parameterization.curve.point
    meeting.parameter
  have pointInsideAmbient : ambient.Contains point :=
    (boxesRefine meeting.index).contains meeting.pointInside
  have residualSmall :
      Data.Gaussian.Norm.Basic.normSq (p.eval point) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree
          ambient :=
    (meeting.residual_lt
      (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold_pos squarefree
        ambient)).le
  exact Dense.Gaussian.Derivative.Separation.Squarefree.derivative_ne_zero_of_small_residual
    squarefree ambient pointInsideAmbient residualSmall

end ControlledProfileRequestMeeting

set_option genInjectivity false in
/-- Total finite owner/outside result for one non-pole sample at the
residual-controlled request. -/
inductive ControlledProfileSampleClassification
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational)
    (sample : NonpoleProfileRequestSample entry
      (controlledProfileRequestWidth entry boxes pairwise target)) where
  /-- The actual retained sample meets a box of the original family. -/ | meeting
      (owner : ControlledProfileRequestMeeting entry boxes pairwise target)
  /-- The actual retained sample lies outside every box of the original family. -/ | outside (proof : ∀ index : Fin
    boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.chart.parameterization.curve.point sample.parameter))

constructive_injectivity ControlledProfileSampleClassification

/-- Search the original finite box family for the supplied nonpole sample.

Return its retained meeting witness when found, or proofs that the actual sample lies outside every retained box. -/
@[expose] def classifyControlledProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational)
    (sample : NonpoleProfileRequestSample entry
      (controlledProfileRequestWidth entry boxes pairwise target)) :
    ControlledProfileSampleClassification entry boxes pairwise target
      sample := by
  let point :=
    entry.parent.chart.parameterization.curve.point sample.parameter
  match found :
      Box.Family.Search.findContainingBoxIndex
        boxes point with
  | some index =>
      exact .meeting
        { index := index
          parameter := sample.parameter
          parameterInside := sample.parameterInside
          denominatorNonzero := sample.denominatorNonzero
          pointInside :=
            Box.Family.Search.findContainingBoxIndex_sound
              boxes point index found }
  | none =>
      exact .outside
        (Box.Family.Search.findContainingBoxIndex_none
          boxes point found)

set_option genInjectivity false in
/-- Fully computed sample/classification pair at the controlled request. -/
structure RequestedControlledProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) where
  /-- The actual computed nonpole sample of the requested child. -/ sample :
    NonpoleProfileRequestSample entry
    (controlledProfileRequestWidth entry boxes pairwise target)
  /-- The classification of this exact sample against the original retained boxes. -/ classification :
    ControlledProfileSampleClassification entry boxes pairwise
    target sample

constructive_injectivity RequestedControlledProfileSample

/-- Retain the computed nonpole child sample together with its classification in the original box family. -/
@[expose] def classifyRequestedControlledProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) :
    RequestedControlledProfileSample entry boxes pairwise target :=
  let sample := Curve.Boundary.Profile.Sample.nonpoleProfileRequestSample entry
    (controlledProfileRequestWidth entry boxes pairwise target)
  { sample := sample
    classification := classifyControlledProfileSample entry boxes pairwise
      target sample }

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Profile.Control

end
