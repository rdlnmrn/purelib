module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Chart.Nondegenerate
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Family.Search
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Event.Analysis
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
public import Purelib.RootIsolation.Curve.Boundary.Profile.Residual
import Purelib.RootIsolation.Curve.Boundary.Profile.Separation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Nondegenerate
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.RootIsolation.Curve.Boundary.Profile (SourcePersistentProfileResidualBoundaryProfileEventEntryAlias)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

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

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Sample

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## Executable sampling and ownership at the combined request -/

set_option genInjectivity false in
/-- A denominator-safe rational parameter computed inside one requested
condition-profile event interval. -/
structure NonpoleProfileRequestSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (epsilon : Fraction.Rational) where
  /-- The actual rational parameter selected inside the original profile request. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the requested event interval. -/ parameterInside :
    (entry.requestAt epsilon).cell.interval.Contains parameter
  /-- The original chart denominator is nonzero at the retained sample parameter. -/ denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0

constructive_injectivity NonpoleProfileRequestSample

/-- Bounded interior search for a non-pole rational parameter in any profile
request.  Only the chart's displayed nondegeneracy certificate is used. -/
@[expose] def nonpoleProfileRequestSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (epsilon : Fraction.Rational) :
    NonpoleProfileRequestSample entry epsilon := by
  let curve := entry.parent.chart.parameterization.curve
  let interval := (entry.requestAt epsilon).cell.interval
  let denominatorPolynomial :=
    Curve.Coordinates.denominatorNormSq curve
  have chartMember :=
    Curve.Boundary.Event.Analysis.chart_mem_of_analysis_mem
      boundary entry.parent.analysisMember
  have nondegenerate :=
    Geometry.Projective.Hermitian.Chart.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [-eq_self, -iff_self, interval] using (entry.requestAt epsilon).cell.proper
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
/-- Total result of classifying one displayed non-pole profile sample against
the complete finite family of separated boxes. -/
inductive CombinedProfileSampleClassification
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (sample : NonpoleProfileRequestSample entry
      (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
        entry boxes pairwise)) where
  /-- Retain an explicit parameter and region index witnessing a meeting of the original combined profile request. -/ |
    meeting
      (owner :
        Curve.Boundary.Profile.Separation.CombinedProfileRequestMeeting
          entry boxes pairwise)
  /-- The displayed sample point is outside every box in the retained finite region family. -/ | outside (proof : ∀
    index : Fin boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.chart.parameterization.curve.point sample.parameter))

constructive_injectivity CombinedProfileSampleClassification

/-- Execute every finite box-membership comparison for a displayed combined-
request profile sample. -/
@[expose] def classifyCombinedProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (sample : NonpoleProfileRequestSample entry
      (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
        entry boxes pairwise)) :
    CombinedProfileSampleClassification entry boxes pairwise sample := by
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
/-- Fully computed non-pole sample and finite owner/outside classification
for the shared sign-and-separation request. -/
structure RequestedCombinedProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  /-- The actual bounded-search non-pole sample at the original combined request width. -/ sample :
    NonpoleProfileRequestSample entry
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
      entry boxes pairwise)
  /-- The finite region classification computed for that exact retained sample. -/ classification :
    CombinedProfileSampleClassification entry boxes pairwise sample

constructive_injectivity RequestedCombinedProfileSample

/-- Compute a denominator-safe sample at the shared sign-and-separation width and classify it against the retained
finite region family.

The same bounded-search sample is used by the finite box lookup and the retained meeting or outside certificate. -/
@[expose] def classifyRequestedCombinedProfileSample
    (entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary)
      (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    RequestedCombinedProfileSample entry boxes pairwise :=
  let sample := nonpoleProfileRequestSample entry
    (Curve.Boundary.Profile.Separation.combinedProfileRequestWidth
      entry boxes pairwise)
  { sample := sample
    classification := classifyCombinedProfileSample entry boxes pairwise
      sample }

namespace CombinedProfileRequestMeeting

/-- Every explicit owner meeting at the combined request carries the new
event-wide original-polynomial residual bound in its owning box. -/
theorem residual_le
    {entry : SourcePersistentProfileResidualBoundaryProfileEventEntryAlias
        boundary}
      {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (meeting :
      Curve.Boundary.Profile.Separation.CombinedProfileRequestMeeting
        entry boxes pairwise) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.chart.parameterization.curve.point
          meeting.parameter)) ≤
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.combinedAffineResidualBudget entry boxes
        pairwise (boxes.get meeting.index) :=
  Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.normSq_eval_point_combined_le_of_inside entry
    boxes pairwise (boxes.get meeting.index) meeting.parameter
      meeting.parameterInside meeting.denominatorNonzero meeting.pointInside

end CombinedProfileRequestMeeting
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Profile.Sample

end
