module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
public import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.SmallWidth
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
public import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Sign
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
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

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Profile (BoundaryProfileEventEntry)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Profile.Separation

/-! ## Unique ownership among separated winding regions -/

/-- Positive request width keeping one profile cylinder from spanning two
separated boxes. -/
@[expose] def separatedProfileRequestWidth
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth
    entry.parent.chart.uniformChordalVariationCoefficient
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
      separated)

/-- The chordal-gap request width for two separated boxes is positive. -/
theorem separatedProfileRequestWidth_pos
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    0 < separatedProfileRequestWidth entry separated :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    entry.parent.chart.uniformChordalVariationCoefficient_nonneg
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos
      separated)

/-- Quantitative profile-event keep-apart theorem at an arbitrary displayed
gap and width. -/
theorem requestedProfileEvent_not_spanning_with_gap
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (gap epsilon : Fraction.Rational)
    (gapLower : ∀ {leftPoint rightPoint : Gaussian.Basic.Canonical},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint))
    (epsilonPositive : 0 < epsilon)
    (diameterSmall :
      entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 <
        gap)
    {leftParameter rightParameter : Fraction.Rational}
    (leftParameterInside :
      (entry.requestAt epsilon).cell.interval.Contains leftParameter)
    (rightParameterInside :
      (entry.requestAt epsilon).cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.parent.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.parent.chart.parameterization.curve.point rightParameter)) :
    False := open Purelib.RationalFunctions in by
  let curve := entry.parent.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_requestAt_le epsilon epsilonPositive
    leftParameterInside rightParameterInside
  have leftTransport :
      Geometry.Projective.Chordal.Basic.chordalSq
          (entry.parent.chart.projective leftParameter)
          (entry.parent.chart.projective rightParameter) =
        Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.parent.chart.projective rightParameter) := by
    simpa only [-eq_self, -iff_self, curve, leftPoint,
      Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.parent.chart.projective rightParameter)
  have rightEquivalent :
      (entry.parent.chart.projective rightParameter).Equivalent
        (Proj.affine rightPoint) := by
    simpa only [-eq_self, -iff_self, curve, rightPoint,
      Geometry.Projective.Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.parent.chart.projective rightParameter) =
        Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_right
      (entry.parent.chart.projective_valid rightParameter)
      (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (Proj.affine leftPoint)
  have affineUpper :
      Geometry.Projective.Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) ≤
        entry.parent.chart.uniformChordalVariationCoefficient * epsilon ^ 2 :=
    by
      rw [← rightTransport, ← leftTransport]
      exact eventUpper
  have affineLower : gap ≤
      Geometry.Projective.Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- At the computed finite width, one profile event cannot meet both members
of a separated pair. -/
theorem separatedProfileRequest_not_spanning
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary)
    {leftBox rightBox : Box} (separated : leftBox.Separated rightBox) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.requestAt
        (separatedProfileRequestWidth entry separated)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (separatedProfileRequestWidth entry separated)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      leftBox.Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      rightBox.Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  apply requestedProfileEvent_not_spanning_with_gap entry
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
      separated)
    (separatedProfileRequestWidth entry separated)
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_le_affine
      separated)
    (separatedProfileRequestWidth_pos entry separated)
    ?_ leftInside rightInside leftDenominator rightDenominator
      leftPointInside rightPointInside
  simpa only [-eq_self, -iff_self, separatedProfileRequestWidth] using
    Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
      entry.parent.chart.uniformChordalVariationCoefficient_nonneg
      (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos
        separated)

/-- Every ordered distinct pair of a finite separated box family contributes
one profile-event keep-apart width. -/
@[expose] def profilePairRequestWidths
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    List Fraction.Rational :=
  (List.finRange boxes.length).flatMap fun left =>
    (List.finRange boxes.length).filterMap fun right =>
      if different : left ≠ right then
        some (separatedProfileRequestWidth entry
          (Data.List.Pairwise.pairwise_get_separated
            pairwise left right different))
      else none

/-- Every ordered pair of distinct retained region indices contributes its computed width to the finite list. -/
theorem profilePairRequestWidth_mem
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    separatedProfileRequestWidth entry
        (Data.List.Pairwise.pairwise_get_separated
          pairwise left right different) ∈
      profilePairRequestWidths entry boxes pairwise := by
  dsimp only [profilePairRequestWidths]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨left, (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨left, rfl⟩), ?_⟩
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨right, (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨right, rfl⟩), ?_⟩
  rewrite [dif_pos different]
  rfl

/-- Every computed pairwise separation width in the finite list is positive. -/
theorem profilePairRequestWidths_positive
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    ∀ width ∈ profilePairRequestWidths entry boxes pairwise, 0 < width := by
  intro width member
  dsimp only [profilePairRequestWidths] at member
  have member := Data.List.Flatten.mem_flatMap.mp member
  rcases member with ⟨left, _leftMember, member⟩
  have member := Data.List.FilterMap.mem_filterMap.mp member
  rcases member with ⟨right, _rightMember, selected⟩
  split at selected
  next different =>
    have equal := Option.some.inj selected
    rw [← equal]
    exact separatedProfileRequestWidth_pos entry
      (Data.List.Pairwise.pairwise_get_separated
        pairwise left right different)
  next same => nomatch selected

/-- One positive width below every pairwise keep-apart request for this
profile event. -/
@[expose] def profileFamilyRequestWidth
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    (profilePairRequestWidths entry boxes pairwise)

/-- The finite minimum of the retained pairwise separation widths is positive. -/
theorem profileFamilyRequestWidth_pos
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    0 < profileFamilyRequestWidth entry boxes pairwise :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (profilePairRequestWidths_positive entry boxes pairwise)

/-- The family-wide request width is no larger than the width for each distinct retained pair. -/
theorem profileFamilyRequestWidth_le_pair
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    profileFamilyRequestWidth entry boxes pairwise ≤
      separatedProfileRequestWidth entry
        (Data.List.Pairwise.pairwise_get_separated
          pairwise left right different) :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (profilePairRequestWidth_mem entry boxes pairwise left right different)

/-- One positive rational request width that is simultaneously narrow enough
for every profile sign and every pairwise separated winding region. -/
@[expose] def combinedProfileRequestWidth
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    Fraction.Rational :=
  min
    (Curve.Event.Profile.Sign.profileSignWidth
      entry.event.1)
    (profileFamilyRequestWidth entry boxes pairwise)

/-- The common sign-control and family-separation width is positive. -/
theorem combinedProfileRequestWidth_pos
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    0 < combinedProfileRequestWidth entry boxes pairwise := by
  exact Fraction.Order.Basic.lt_min
    (Curve.Event.Profile.Sign.profileSignWidth_pos
      entry.event.1)
    (profileFamilyRequestWidth_pos entry boxes pairwise)

/-- The combined request width meets the original profile-wide sign bound. -/
theorem combinedProfileRequestWidth_le_sign
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    combinedProfileRequestWidth entry boxes pairwise ≤
      Curve.Event.Profile.Sign.profileSignWidth
        entry.event.1 :=
  Fraction.Order.Basic.min_le_left _ _

/-- The combined request width meets the original family-wide separation bound. -/
theorem combinedProfileRequestWidth_le_family
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    combinedProfileRequestWidth entry boxes pairwise ≤
      profileFamilyRequestWidth entry boxes pairwise :=
  Fraction.Order.Basic.min_le_right _ _

/-- Exact affine box classification at the same finite request width used to
keep all separated winding regions apart.  Root hypotheses remain displayed
rational evaluations; no root existence is inferred from an event count. -/
@[expose] def classifyCombinedProfileEventAffine
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    Curve.Event.Profile.Classification.ProfileEventAffineClassification
      entry.event.2 (combinedProfileRequestWidth entry boxes pairwise) :=
  Curve.Event.Profile.Classification.classifyProfileEventAffine
    entry.event.2 (combinedProfileRequestWidth entry boxes pairwise)
      (combinedProfileRequestWidth_pos entry boxes pairwise)
      (combinedProfileRequestWidth_le_sign entry boxes pairwise)

/-- Any displayed positive width below the family bound keeps one profile
event from meeting two distinct separated winding boxes. -/
theorem profileRequest_not_spanning_of_le_family
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileFamilyRequestWidth entry boxes pairwise)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.requestAt epsilon).cell.interval.Contains leftParameter →
      (entry.requestAt epsilon).cell.interval.Contains rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  let separated :=
    Data.List.Pairwise.pairwise_get_separated
      pairwise left right different
  let pairWidth := separatedProfileRequestWidth entry separated
  have widthOrder : epsilon ≤ pairWidth :=
    epsilonLe.trans (by
      simpa only [-eq_self, -iff_self, pairWidth, separated] using
        profileFamilyRequestWidth_le_pair entry boxes pairwise left right
          different)
  have widthSquare : epsilon ^ 2 ≤ pairWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct epsilonPositive.le widthOrder 2
  have coefficientNonnegative :=
    entry.parent.chart.uniformChordalVariationCoefficient_nonneg
  have requestDiameterLe :
      entry.parent.chart.uniformChordalVariationCoefficient *
          epsilon ^ 2 ≤
        entry.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare
      coefficientNonnegative
  have pairDiameterSmall :
      entry.parent.chart.uniformChordalVariationCoefficient * pairWidth ^ 2 <
        Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
          separated := by
    simpa only [-eq_self, -iff_self, pairWidth, separatedProfileRequestWidth] using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative
        (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_pos
          separated)
  exact requestedProfileEvent_not_spanning_with_gap entry
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap
      separated)
    epsilon
    (Geometry.Projective.Chordal.Box.Separation.separatedChordalGap_le_affine
      separated)
    epsilonPositive (requestDiameterLe.trans_lt pairDiameterSmall)
    leftInside rightInside leftDenominator rightDenominator leftPointInside
      rightPointInside

/-- At the single family-wide width, one profile event cannot meet two
distinct separated winding boxes. -/
theorem profileFamilyRequest_not_spanning
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.requestAt
        (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
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
  profileRequest_not_spanning_of_le_family entry boxes pairwise
    (profileFamilyRequestWidth entry boxes pairwise)
    (profileFamilyRequestWidth_pos entry boxes pairwise) le_rfl left right
      different

/-- At the combined sign-and-separation width, one classified profile event
cannot meet two distinct winding boxes. -/
theorem combinedProfileRequest_not_spanning
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      (entry.requestAt
        (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
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
  profileRequest_not_spanning_of_le_family entry boxes pairwise
    (combinedProfileRequestWidth entry boxes pairwise)
    (combinedProfileRequestWidth_pos entry boxes pairwise)
    (combinedProfileRequestWidth_le_family entry boxes pairwise) left right
      different

set_option genInjectivity false in
/-- Explicit meeting of the family-wide profile request with one finite
winding region. -/
structure ProfileFamilyRequestMeeting
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  /-- The retained finite index of the region met by this profile request. -/ index : Fin boxes.length
  /-- The displayed rational parameter witnessing the meeting. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the original profile event's specified request interval. -/ parameterInside :
    (entry.requestAt
    (profileFamilyRequestWidth entry boxes pairwise)).cell.interval.Contains
      parameter
  /-- The original chart denominator is nonzero at the retained parameter. -/ denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The chart point at the retained parameter belongs to the region at the exact retained index. -/ pointInside :
    (boxes.get index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

constructive_injectivity ProfileFamilyRequestMeeting

/-- Any two explicit owners of the same sufficiently narrow profile event
have the same finite region index. -/
theorem ProfileFamilyRequestMeeting.index_unique
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (left right : ProfileFamilyRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (profileFamilyRequest_not_spanning entry boxes pairwise
      left.index right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim

set_option genInjectivity false in
/-- Explicit meeting at the single request width that supports both exact
profile classification and separated-region ownership. -/
structure CombinedProfileRequestMeeting
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  /-- The retained finite index of the region met by this profile request. -/ index : Fin boxes.length
  /-- The displayed rational parameter witnessing the meeting. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the original profile event's specified request interval. -/ parameterInside :
    (entry.requestAt
    (combinedProfileRequestWidth entry boxes pairwise)).cell.interval.Contains
      parameter
  /-- The original chart denominator is nonzero at the retained parameter. -/ denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The chart point at the retained parameter belongs to the region at the exact retained index. -/ pointInside :
    (boxes.get index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

constructive_injectivity CombinedProfileRequestMeeting

/-- Any two displayed rational meetings at the combined request have the
same finite winding-region index. -/
theorem CombinedProfileRequestMeeting.index_unique
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (left right : CombinedProfileRequestMeeting entry boxes pairwise) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (combinedProfileRequest_not_spanning entry boxes pairwise
      left.index right.index same left.parameterInside right.parameterInside
      left.denominatorNonzero right.denominatorNonzero left.pointInside
      right.pointInside).elim
end Purelib.RootIsolation.Curve.Boundary.Profile.Separation

end
