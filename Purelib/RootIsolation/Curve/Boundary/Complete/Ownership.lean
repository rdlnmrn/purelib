module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Family.Search
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
public import Purelib.RootIsolation.Curve.Boundary.Complete.Control
public import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
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
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic

open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Complete.Basic (BoundaryCompleteRequestEntry)
open Purelib.RootIsolation.Curve.Boundary.Complete.Sample (NonpoleCompleteRequestSample)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Curve.Boundary.Complete.Ownership

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}

set_option genInjectivity false in
/-- An explicit owner meeting for one complete child at the global
controlled width. -/
structure ControlledCompleteRequestMeeting
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational)
    (entry : BoundaryCompleteRequestEntry boundary
      (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth boundary boxes pairwise target)) where
  /-- The index of the met box in the original retained family. -/ index : Fin boxes.length
  /-- The exact rational parameter witnessing the controlled child's meeting. -/ parameter : Fraction.Rational
  /-- The witness lies in the original requested child interval. -/ parameterInside : entry.child.cell.interval.Contains
    parameter
  /-- The chart denominator is nonzero at the retained witness. -/ denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0
  /-- The chart point of the retained witness lies strictly inside the indexed box. -/ pointInside : (boxes.get
    index).Contains
    (entry.parent.parent.chart.parameterization.curve.point parameter)

constructive_injectivity ControlledCompleteRequestMeeting

namespace ControlledCompleteRequestMeeting

variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}
variable {boxes : List Box}
variable {pairwise : boxes.Pairwise fun left right => left.Separated right}
variable {target : Fraction.Rational}
variable {entry : BoundaryCompleteRequestEntry boundary
  (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth boundary boxes pairwise target)}

/-- Any two displayed rational owner meetings of the same retained child
have the same finite box index. -/
theorem index_unique
  (targetPositive : 0 < target)
    (left right : Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting boxes pairwise target
      entry) : left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (entry.controlled_not_spanning targetPositive left.index
      right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim

/-- Every explicit owner meeting has original-polynomial residual below the
global target. -/
theorem residual_lt
  (targetPositive : 0 < target)
    (meeting : Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting boxes pairwise target
      entry) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          meeting.parameter)) < target :=
  entry.residual_lt_of_inside targetPositive meeting.index meeting.parameter
    meeting.parameterInside meeting.denominatorNonzero meeting.pointInside

/-- Below the squarefree derivative threshold, every owned complete-child
sample has a nonzero derivative. -/
theorem
  derivative_ne_zero
    {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (boxesRefine : ∀ index : Fin boxes.length,
      (boxes.get index).Refines ambient)
    (targetPositive : 0 < target)
    (targetLe : target ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
    (meeting : Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting boxes pairwise
      target entry) :
    (Dense.Gaussian.GCD.derivative p).eval
        (entry.parent.parent.chart.parameterization.curve.point
          meeting.parameter) ≠ 0 := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    meeting.parameter
  have pointInsideAmbient : ambient.Contains point :=
    (boxesRefine meeting.index).contains meeting.pointInside
  have residualSmall : Data.Gaussian.Norm.Basic.normSq
      (p.eval point) ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient :=
    (meeting.residual_lt targetPositive).le.trans targetLe
  exact Dense.Gaussian.Derivative.Separation.Squarefree.derivative_ne_zero_of_small_residual
    squarefree ambient pointInsideAmbient residualSmall

end ControlledCompleteRequestMeeting

set_option genInjectivity false in
/-- Total finite owner/outside classification of one non-pole sample from a
complete retained child. -/
inductive CompleteRequestSampleClassification
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational)
    (entry : BoundaryCompleteRequestEntry boundary
      (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (sample : NonpoleCompleteRequestSample entry) where
  /-- The actual complete-child sample meets a retained box. -/ | meeting
      (owner : ControlledCompleteRequestMeeting boxes pairwise target entry)
  /-- The actual complete-child sample lies outside every retained box. -/ | outside (proof : ∀ index : Fin
    boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter))

constructive_injectivity CompleteRequestSampleClassification

/-- Execute every finite box-membership comparison for one complete-child
sample. -/
@[expose] def classifyCompleteRequestSample
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational)
    (entry : BoundaryCompleteRequestEntry boundary
      (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (sample : NonpoleCompleteRequestSample entry) :
    CompleteRequestSampleClassification boxes pairwise target entry sample := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
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
/-- All executable data attached to one member of the globally controlled
complete boundary family. -/
structure ClassifiedControlledBoundaryChild
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (targetPositive : 0 < target) where
  /-- The original complete boundary child at the common controlled request. -/ entry :
    BoundaryCompleteRequestEntry boundary
    (Curve.Boundary.Complete.Control.boundaryControlledRequestWidth boundary boxes pairwise target)
  /-- The child belongs to the original complete requested boundary family. -/ member : entry ∈
    Curve.Boundary.Complete.Control.controlledBoundaryCompleteRequestFamily boundary boxes pairwise target
  /-- The original child's box-interaction classification. -/ boxClassification :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.BoxClassification entry.child
  /-- The original child's denominator classification for the retained relation. -/ denominatorClassification :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.DenominatorClassification entry.child
      (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation entry.parent.event.1)
  /-- The computed nonpole sample retained for this exact child. -/ sample :
    NonpoleCompleteRequestSample entry
  /-- The classification of this exact retained sample against the original boxes. -/ sampleClassification :
    CompleteRequestSampleClassification boxes pairwise
    target entry sample

constructive_injectivity ClassifiedControlledBoundaryChild

namespace ClassifiedControlledBoundaryChild

/-- Affine semantics derived from the retained exact per-relation
classification. -/
@[expose] def
  affineClassification
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} {targetPositive : 0 < target}
    (child : Curve.Boundary.Complete.Ownership.ClassifiedControlledBoundaryChild boundary boxes pairwise target
      targetPositive) :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.AffineClassification child.entry.child :=
  Curve.Event.Profile.Complete.Classification.CompleteRequestLeaf.BoxClassification.toAffine child.boxClassification

end ClassifiedControlledBoundaryChild

/-- Compute exact affine and sample-owner classifications for every retained
child in the complete boundary family. -/
@[expose] def classifiedControlledBoundaryFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    List (ClassifiedControlledBoundaryChild boundary boxes pairwise target
      targetPositive) :=
  (Curve.Boundary.Complete.Control.controlledBoundaryCompleteRequestFamily boundary boxes pairwise target).attach.map
    fun attached =>
      let sample := Curve.Boundary.Complete.Sample.nonpoleCompleteRequestSample attached.1
      { entry := attached.1
        member := attached.2
        boxClassification := attached.1.boxClassification targetPositive
        denominatorClassification :=
          attached.1.denominatorClassification targetPositive
        sample := sample
        sampleClassification :=
          classifyCompleteRequestSample boxes pairwise target attached.1
            sample }
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Complete.Ownership

end
