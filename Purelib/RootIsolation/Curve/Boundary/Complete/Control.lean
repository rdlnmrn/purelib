module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Box.Separation
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
public import Purelib.RootIsolation.Curve.Boundary.Profile.Control
import Purelib.RootIsolation.Curve.Boundary.Profile.Family
import Purelib.RootIsolation.Curve.Boundary.Profile.Residual
import Purelib.RootIsolation.Curve.Boundary.Profile.Separation
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Condition
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
import Purelib.RootIsolation.Curve.Event.Profile.Sign
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Separation
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
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Residual

open Purelib.Data.Rat.Fraction.Order

open Purelib.RootIsolation.Curve.Event.Profile.Complete

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line (Proj)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Complete.Basic (BoundaryCompleteRequestEntry)
open Purelib.RootIsolation.Curve.Boundary.Profile (SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias)
open Purelib.RootIsolation.Curve.Event.Profile.Classification (ProfileRelation)

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

namespace Purelib.RootIsolation.Curve.Boundary.Complete

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Hermitian.Atom}

/-- Per-profile widths satisfying sign stability, separated-region
ownership, the supplied original-polynomial residual target, a direct
homogeneous cylinder-diameter target, and every equality-owned condition
residual target.  Reusing the same positive rational target keeps the public
API small; callers may pass any finite minimum of their residual and
projective-clearance requirements. -/
@[expose] def Control.boundaryControlledRequestWidths
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) : List Fraction.Rational :=
  (Profile.Family.boundaryProfileEventFamily
    boundary).map fun parent =>
      min
        (Profile.Control.controlledProfileRequestWidth
          parent boxes pairwise target)
        (min
          (SmallWidth.shrinkingWidth
            parent.parent.chart.uniformChordalVariationCoefficient target)
          (Condition.profileConditionRequestWidth parent.event.1 target))

/-- Each retained profile's control request appears in the finite boundary request family. -/
theorem Control.boundaryControlledRequestWidth_mem
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Profile.Family.boundaryProfileEventFamily
        boundary) :
    min
        (Profile.Control.controlledProfileRequestWidth
          parent boxes pairwise target)
        (min
          (SmallWidth.shrinkingWidth
            parent.parent.chart.uniformChordalVariationCoefficient target)
          (Condition.profileConditionRequestWidth parent.event.1 target)) ∈
      Control.boundaryControlledRequestWidths boundary boxes pairwise target :=
  Data.List.Map.mem_map.mpr ⟨parent, parentMember, rfl⟩

/-- Every width in the retained boundary control-request family is positive. -/
theorem Control.boundaryControlledRequestWidths_positive
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    ∀ width ∈ Control.boundaryControlledRequestWidths boundary boxes pairwise target,
      0 < width := by
  intro width member
  dsimp only [Control.boundaryControlledRequestWidths] at member
  have member := Data.List.Map.mem_map.mp member
  rcases member with ⟨parent, _parentMember, rfl⟩
  exact Basic.lt_min
    (Profile.Control.controlledProfileRequestWidth_pos
      parent boxes pairwise targetPositive)
    (Basic.lt_min
      (SmallWidth.shrinkingWidth_pos
        parent.parent.chart.uniformChordalVariationCoefficient_nonneg
        targetPositive)
      (Condition.profileConditionRequestWidth_pos parent.event.1 targetPositive))

/-- One positive rational width satisfying every profile parent
simultaneously.  All sibling children are subdivided at this same width. -/
@[expose] def Control.boundaryControlledRequestWidth
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    (Control.boundaryControlledRequestWidths boundary boxes pairwise target)

/-- The common finite boundary control request has positive width. -/
theorem Control.boundaryControlledRequestWidth_pos
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < Control.boundaryControlledRequestWidth boundary boxes pairwise target :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (Control.boundaryControlledRequestWidths_positive boundary boxes pairwise
      targetPositive)

/-- The shared boundary width is no larger than the request of any retained parent profile. -/
theorem Control.boundaryControlledRequestWidth_le_parent
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Profile.Family.boundaryProfileEventFamily
        boundary) :
    Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
      Profile.Control.controlledProfileRequestWidth
        parent boxes pairwise target :=
  (Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (Control.boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans (Basic.min_le_left _ _)

/-- The global width is also below the direct homogeneous-diameter width of
every displayed profile parent. -/
theorem Control.boundaryControlledRequestWidth_le_diameter
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Profile.Family.boundaryProfileEventFamily
        boundary) :
    Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
      SmallWidth.shrinkingWidth
        parent.parent.chart.uniformChordalVariationCoefficient target :=
  (Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (Control.boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))

/-- The global width is below every equality-cofactor condition width in
every displayed profile parent. -/
theorem Control.boundaryControlledRequestWidth_le_condition
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) (parent :
      SourcePersistentProfileRequestFamilyBoundaryProfileEventEntryAlias boundary)
    (parentMember : parent ∈
      Profile.Family.boundaryProfileEventFamily
        boundary)
    (relation :
      ProfileRelation
        parent.event.1)
    (relationMember : relation ∈ parent.event.1.profile.relations) :
    Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
      Condition.relationConditionRequestWidth parent.event.1 relation target :=
  (Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (Control.boundaryControlledRequestWidth_mem boundary boxes pairwise target parent
      parentMember)).trans
    ((Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
      (Condition.profileConditionRequestWidth_le_relation parent.event.1 target relation
        relationMember)))

/-- The complete sibling-preserving boundary family at its one shared
sign-, separation-, and residual-controlled width. -/
@[expose] def Control.controlledBoundaryCompleteRequestFamily
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Fraction.Rational) :
    List (BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :=
  Basic.boundaryCompleteRequestFamily boundary
    (Control.boundaryControlledRequestWidth boundary boxes pairwise target)
namespace Basic.BoundaryCompleteRequestEntry

variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- The shared controlled boundary width satisfies this exact parent profile's sign request. -/
theorem controlledWidth_le_sign
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational}
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
      Event.Profile.Sign.profileSignWidth
        entry.parent.event.1 :=
  (Control.boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
    entry.parent entry.parentMember).trans
      (Profile.Control.controlledProfileRequestWidth_le_sign
        entry.parent boxes pairwise target)

/-- The shared controlled boundary width satisfies this exact parent profile's separation request. -/
theorem
  controlledWidth_le_family
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational}
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
      Profile.Separation.profileFamilyRequestWidth
        entry.parent boxes pairwise :=
  (Control.boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
    entry.parent entry.parentMember).trans
      (Profile.Control.controlledProfileRequestWidth_le_family
        entry.parent boxes pairwise target)

/-- Every equality-owned condition is uniformly below the shared rational
target throughout a globally controlled retained child.  The theorem is
about explicit rational parameters and does not assert a profile-factor
zero. -/
theorem
  equality_condition_eval_sq_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (condition cofactor :
      Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization : Dense.Rational.Factorization
      condition entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationMember :
      (⟨condition,
        Dense.Rational.Factorization.ConditionRelation.equality
          cofactor factorization⟩ :
        ProfileRelation
          entry.parent.event.1) ∈
        entry.parent.event.1.profile.relations)
    (parameter : Fraction.Rational)
    (inside : entry.child.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < target := by
  have globalPositive :
      0 < Control.boundaryControlledRequestWidth boundary boxes pairwise target :=
    Control.boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive
  have globalLeRelation :=
    Control.boundaryControlledRequestWidth_le_condition boundary boxes pairwise target
      entry.parent entry.parentMember
      (⟨condition,
        Dense.Rational.Factorization.ConditionRelation.equality
          cofactor factorization⟩ :
        ProfileRelation
          entry.parent.event.1)
      relationMember
  have globalLeEquality :
      Control.boundaryControlledRequestWidth boundary boxes pairwise target ≤
        Basic.CompleteRequestLeaf.equalityConditionWidth entry.parent.event.1
          cofactor target := by
    simpa only [-eq_self, -iff_self, Condition.relationConditionRequestWidth] using
      globalLeRelation
  exact entry.child.equality_condition_eval_sq_lt globalPositive condition
    cofactor factorization globalLeEquality targetPositive parameter inside

/-- The same global request directly bounds the homogeneous diameter of
each retained child by the caller's target, independently of affine poles. -/
theorem
  controlled_chordal_diameter_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    entry.parent.parent.chart.uniformChordalVariationCoefficient *
        Control.boundaryControlledRequestWidth boundary boxes pairwise target ^ 2 <
      target := by
  let globalWidth :=
    Control.boundaryControlledRequestWidth boundary boxes pairwise target
  let diameterWidth :=
    SmallWidth.shrinkingWidth
      entry.parent.parent.chart.uniformChordalVariationCoefficient target
  have globalPositive : 0 < globalWidth := by
    simpa only [-eq_self, -iff_self, globalWidth] using
      Control.boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLe : globalWidth ≤ diameterWidth := by
    simpa only [-eq_self, -iff_self, globalWidth, diameterWidth] using
      Control.boundaryControlledRequestWidth_le_diameter boundary boxes pairwise target
        entry.parent entry.parentMember
  have squareLe : globalWidth ^ 2 ≤ diameterWidth ^ 2 :=
    Arithmetic.pow_le_pow_direct globalPositive.le globalLe 2
  have coefficientNonnegative :=
    entry.parent.parent.chart.uniformChordalVariationCoefficient_nonneg
  exact
    (Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
      coefficientNonnegative).trans_lt
        (by
          simpa only [-eq_self, -iff_self, diameterWidth] using
            SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
              coefficientNonnegative targetPositive)

/-- Exact per-relation box classification for every sibling retained at the
one global controlled width.  Keeping this certificate available avoids
throwing away which conditions are equality-owned or uniformly apart. -/
@[expose] def boxClassification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    Basic.CompleteRequestLeaf.BoxClassification entry.child :=
  entry.child.classifyBox
    (Control.boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    entry.controlledWidth_le_sign

/-- Exact finite pole/apart classification for the retained profile's
homogeneous denominator relation at the global controlled width. -/
@[expose] def
  denominatorClassification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    Basic.CompleteRequestLeaf.DenominatorClassification entry.child
      (Denominator.profileDenominatorRelation entry.parent.event.1) :=
  entry.child.classifyDenominator
    (Denominator.profileDenominatorRelation entry.parent.event.1)
    (Control.boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    entry.controlledWidth_le_sign

/-- Exact affine classification derived from the retained per-relation box
certificate. -/
@[expose] def classification
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target)) :
    Basic.CompleteRequestLeaf.AffineClassification entry.child :=
  Classification.CompleteRequestLeaf.BoxClassification.toAffine (entry.boxClassification
    targetPositive)

/-- Homogeneous chordal diameter bound for one complete requested child. -/
theorem chordalSq_le
    {epsilon : Fraction.Rational}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    (positive : 0 < epsilon) {left right : Fraction.Rational}
    (leftInside : entry.child.cell.interval.Contains left)
    (rightInside : entry.child.cell.interval.Contains right) :
    Chordal.Basic.chordalSq
        (entry.parent.parent.chart.projective left)
        (entry.parent.parent.chart.projective right) ≤
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
        epsilon ^ 2 :=
  entry.child.chordalSq_le positive leftInside rightInside

/-- A retained child whose homogeneous diameter is below an affine chordal
gap cannot meet both sides of that gap. -/
theorem not_spanning_with_gap
    {epsilon : Fraction.Rational}
    (entry : BoundaryCompleteRequestEntry boundary epsilon)
    {leftBox rightBox : Box} (gap : Fraction.Rational)
    (gapLower : ∀ {leftPoint rightPoint :
        Gaussian.Basic.Canonical},
      leftBox.Contains leftPoint → rightBox.Contains rightPoint →
        gap ≤ Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint))
    (positive : 0 < epsilon)
    (diameterSmall :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
        epsilon ^ 2 < gap)
    {leftParameter rightParameter : Fraction.Rational}
    (leftParameterInside :
      entry.child.cell.interval.Contains leftParameter)
    (rightParameterInside :
      entry.child.cell.interval.Contains rightParameter)
    (leftDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0)
    (rightDenominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0)
    (leftPointInside : leftBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point leftParameter))
    (rightPointInside : rightBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        rightParameter)) : False := open Purelib.RationalFunctions in by
  let curve := entry.parent.parent.chart.parameterization.curve
  let leftPoint := curve.point leftParameter
  let rightPoint := curve.point rightParameter
  have eventUpper := entry.chordalSq_le positive leftParameterInside
    rightParameterInside
  have leftTransport :
      Chordal.Basic.chordalSq
          (entry.parent.parent.chart.projective leftParameter)
          (entry.parent.parent.chart.projective rightParameter) =
        Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.parent.parent.chart.projective rightParameter) := by
    simpa only [-eq_self, -iff_self, curve, leftPoint,
      Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.chordalSq_projective_eq_affine
        curve leftParameter leftDenominatorNonzero
          (entry.parent.parent.chart.projective rightParameter)
  have rightEquivalent :
      (entry.parent.parent.chart.projective rightParameter).Equivalent
        (Proj.affine rightPoint) := by
    simpa only [-eq_self, -iff_self, curve, rightPoint,
      Hermitian.Chart.BoundedChart.projective] using
      Curve.Projective.projective_equivalent_affine
        curve rightParameter rightDenominatorNonzero
  have rightTransport :
      Chordal.Basic.chordalSq
          (Proj.affine leftPoint)
          (entry.parent.parent.chart.projective rightParameter) =
        Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    Chordal.Equivalence.chordalSq_eq_of_equivalent_right
      (entry.parent.parent.chart.projective_valid rightParameter)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate rightPoint)
      rightEquivalent (Proj.affine leftPoint)
  have affineUpper :
      Chordal.Basic.chordalSq
          (Proj.affine leftPoint) (Proj.affine rightPoint) ≤
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
          epsilon ^ 2 := by
    rw [← rightTransport, ← leftTransport]
    exact eventUpper
  have affineLower : gap ≤
      Chordal.Basic.chordalSq
        (Proj.affine leftPoint) (Proj.affine rightPoint) :=
    gapLower leftPointInside rightPointInside
  exact (not_lt_of_ge affineLower) (affineUpper.trans_lt diameterSmall)

/-- At the global controlled width, one retained child cannot meet two
distinct members of the separated finite box family. -/
theorem controlled_not_spanning
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Fraction.Rational},
      entry.child.cell.interval.Contains leftParameter →
      entry.child.cell.interval.Contains rightParameter →
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.parent.chart.parameterization.curve.point rightParameter) →
      False := by
  intro leftParameter rightParameter leftInside rightInside leftDenominator
    rightDenominator leftPointInside rightPointInside
  let separated :=
    Data.List.Pairwise.pairwise_get_separated
      pairwise left right different
  let pairWidth :=
    Profile.Separation.separatedProfileRequestWidth
      entry.parent separated
  let globalWidth :=
    Control.boundaryControlledRequestWidth boundary boxes pairwise target
  have globalPositive : 0 < globalWidth := by
    simpa only [-eq_self, -iff_self, globalWidth] using
      Control.boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLePair : globalWidth ≤ pairWidth := by
    exact entry.controlledWidth_le_family.trans
      (by
        simpa only [-eq_self, -iff_self, pairWidth, separated] using
          Profile.Separation.profileFamilyRequestWidth_le_pair
            entry.parent boxes pairwise left right different)
  have widthSquare : globalWidth ^ 2 ≤ pairWidth ^ 2 :=
    Arithmetic.pow_le_pow_direct globalPositive.le
      globalLePair 2
  have coefficientNonnegative :=
    entry.parent.parent.chart.uniformChordalVariationCoefficient_nonneg
  have diameterLe :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
          globalWidth ^ 2 ≤
        entry.parent.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare
      coefficientNonnegative
  have pairSmall :
      entry.parent.parent.chart.uniformChordalVariationCoefficient *
          pairWidth ^ 2 <
        Chordal.Box.Separation.separatedChordalGap
          separated := by
    simpa only [-eq_self, -iff_self, pairWidth,
      Profile.Separation.separatedProfileRequestWidth] using
      SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative
        (Chordal.Box.Separation.separatedChordalGap_pos
          separated)
  exact entry.not_spanning_with_gap
    (Chordal.Box.Separation.separatedChordalGap
      separated)
    (Chordal.Box.Separation.separatedChordalGap_le_affine
      separated)
    globalPositive (diameterLe.trans_lt pairSmall) leftInside rightInside
      leftDenominator rightDenominator leftPointInside rightPointInside

/-- The original-polynomial residual budget for every possible owner is
strictly below the caller's target at the global controlled width. -/
theorem
  controlled_residual_budget_lt
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (index : Fin boxes.length) :
    Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient
        entry.parent (boxes.get index) *
      Control.boundaryControlledRequestWidth boundary boxes pairwise target ^ 2 <
        target := by
  let globalWidth :=
    Control.boundaryControlledRequestWidth boundary boxes pairwise target
  let parentWidth :=
    Profile.Control.controlledProfileRequestWidth
      entry.parent boxes pairwise target
  let coefficient :=
    Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient
      entry.parent (boxes.get index)
  have globalPositive : 0 < globalWidth := by
    simpa only [-eq_self, -iff_self, globalWidth] using
      Control.boundaryControlledRequestWidth_pos boundary boxes pairwise
        targetPositive
  have globalLeParent : globalWidth ≤ parentWidth := by
    simpa only [-eq_self, -iff_self, globalWidth, parentWidth] using
      Control.boundaryControlledRequestWidth_le_parent boundary boxes pairwise target
        entry.parent entry.parentMember
  have squareOrder : globalWidth ^ 2 ≤ parentWidth ^ 2 :=
    Arithmetic.pow_le_pow_direct globalPositive.le
      globalLeParent 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [-eq_self, -iff_self, coefficient] using
      Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg
        entry.parent (boxes.get index)
  have scaled : coefficient * globalWidth ^ 2 ≤
      coefficient * parentWidth ^ 2 :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  exact scaled.trans_lt (by
    simpa only [-eq_self, -iff_self, coefficient, parentWidth] using
      Profile.Control.controlledProfileResidual_lt
        entry.parent boxes pairwise targetPositive index)

/-- Every owned rational point of a complete retained child has original-
polynomial residual strictly below the supplied target. -/
theorem residual_lt_of_inside
    {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (entry : BoundaryCompleteRequestEntry boundary
      (Control.boundaryControlledRequestWidth boundary boxes pairwise target))
    (index : Fin boxes.length) (parameter : Fraction.Rational)
    (parameterInside : entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0)
    (pointInside : (boxes.get index).Contains
      (entry.parent.parent.chart.parameterization.curve.point parameter)) :
    Gaussian.Norm.Basic.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point parameter)) <
      target := by
  have upper := entry.child.normSq_eval_point_le_of_inside
    (Control.boundaryControlledRequestWidth_pos boundary boxes pairwise targetPositive)
    parameter parameterInside denominatorNonzero pointInside
  exact upper.trans_lt
    (entry.controlled_residual_budget_lt targetPositive index)

end Basic.BoundaryCompleteRequestEntry

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Complete

end
