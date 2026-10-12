module
import Purelib.Data.List.All
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Chart.Nondegenerate
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
import Purelib.RationalFunctions.Curve.Box.Approximation
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
public import Purelib.RootIsolation.Curve.Boundary.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Condition
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
public import Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Nondegenerate
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Refinement
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Residual

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

namespace Purelib.RootIsolation.Curve.Boundary.Complete.Sample

/-! ## Complete requested families through a dispatched boundary -/

section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {reference :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}

set_option genInjectivity false in
/-- A denominator-safe rational parameter computed inside one complete
retained child. -/
structure NonpoleCompleteRequestSample
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon) where
  /-- The actual rational parameter selected by the bounded non-pole search. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the specified original child or descendant request interval. -/ parameterInside :
    entry.child.cell.interval.Contains parameter
  /-- The original chart denominator is nonzero at the retained sample parameter. -/ denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0

constructive_injectivity NonpoleCompleteRequestSample

/-- Bounded finite search for a non-pole rational parameter in any retained
child. -/
@[expose] def nonpoleCompleteRequestSample
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon) :
    Curve.Boundary.Complete.Sample.NonpoleCompleteRequestSample entry := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let interval := entry.child.cell.interval
  let denominatorPolynomial :=
    Curve.Coordinates.denominatorNormSq curve
  have chartMember :=
    Curve.Boundary.Event.Analysis.chart_mem_of_analysis_mem
      boundary entry.parent.parent.analysisMember
  have nondegenerate :=
    Geometry.Projective.Hermitian.Chart.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [-eq_self, -iff_self, interval] using entry.child.cell.proper
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
/-- A denominator-safe rational sample computed on a later deterministic
descendant of one already retained complete child. -/
structure NonpoleCompleteRequestDescendantSample
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (target : Fraction.Rational) where
  /-- The actual rational parameter selected by the bounded non-pole search. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the specified original child or descendant request interval. -/ parameterInside :
    (entry.child.request target).cell.interval.Contains parameter
  /-- The original chart denominator is nonzero at the retained sample parameter. -/ denominatorNonzero :
    entry.parent.parent.chart.parameterization.curve.denominatorAt
      parameter ≠ 0

constructive_injectivity NonpoleCompleteRequestDescendantSample

/-- Bounded finite non-pole search on the selected descendant branch. -/
@[expose] def nonpoleCompleteRequestDescendantSample
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (target : Fraction.Rational) :
    Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample entry target := by
  let curve := entry.parent.parent.chart.parameterization.curve
  let interval := (entry.child.request target).cell.interval
  let denominatorPolynomial :=
    Curve.Coordinates.denominatorNormSq curve
  have chartMember :=
    Curve.Boundary.Event.Analysis.chart_mem_of_analysis_mem
      boundary entry.parent.parent.analysisMember
  have nondegenerate :=
    Geometry.Projective.Hermitian.Chart.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [-eq_self, -iff_self, interval] using (entry.child.request target).cell.proper
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

/-- Deterministic descendant width making every equality-owned box condition
smaller than the square of the denominator-lower-bound-scaled radius. -/
@[expose] def nearBoxDescendantRequestWidth
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Fraction.Rational) : Fraction.Rational :=
  Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth entry.parent.event.1
    ((denominator.apartLower apart * radius) ^ 2)

/-- A positive coordinate radius gives a positive condition-controlled descendant request width. -/
theorem nearBoxDescendantRequestWidth_pos
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    {radius : Fraction.Rational} (radiusPositive : 0 < radius) :
    0 < Curve.Boundary.Complete.Sample.nearBoxDescendantRequestWidth entry denominator apart radius := by
  apply Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth_pos
  exact Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (denominator.apartLower_pos apart)
      radiusPositive) 2

/-- Bounded non-pole sample on the condition-controlled descendant. -/
@[expose] def nearBoxDescendantSample
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Fraction.Rational) :
    Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample entry
      (Curve.Boundary.Complete.Sample.nearBoxDescendantRequestWidth entry denominator apart radius) :=
  Curve.Boundary.Complete.Sample.nonpoleCompleteRequestDescendantSample entry
    (Curve.Boundary.Complete.Sample.nearBoxDescendantRequestWidth entry denominator apart radius)

/-- If the retained inside-profile classification has an apart denominator,
its computed descendant sample lies within the supplied rational coordinate
radius of the profiled box.  The sample is produced by bounded search; no
profile zero or completed root is asserted. -/
theorem nearBoxDescendantSample_within_radius
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation entry.parent.event.1)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (denominatorLower : ∀ parameter : Fraction.Rational,
      entry.child.cell.interval.Contains parameter →
      denominator.apartLower apart ≤
        Data.Gaussian.Norm.Basic.normSq
          (entry.parent.parent.chart.parameterization.curve.denominatorAt
            parameter))
    (allNonnegative : ∀ relation ∈
      entry.parent.event.1.profile.relations,
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry.child relation)
    {radius : Fraction.Rational} (radiusPositive : 0 < radius) :
    let sample := Curve.Boundary.Complete.Sample.nearBoxDescendantSample entry denominator apart radius
    current.xLower - radius <
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter).re ∧
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter).re < current.xUpper + radius ∧
      current.yLower - radius <
        (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter).im ∧
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter).im < current.yUpper + radius := by
  let lower := denominator.apartLower apart
  let cap := lower * radius
  let target := Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth entry.parent.event.1 (cap ^ 2)
  let sample := Curve.Boundary.Complete.Sample.nearBoxDescendantSample entry denominator apart radius
  have capPositive : 0 < cap := by
    exact Fraction.Order.Arithmetic.mul_pos_direct
      (denominator.apartLower_pos apart) radiusPositive
  have sampleInside :
      (entry.child.request target).cell.interval.Contains sample.parameter := by
    simpa only [-eq_self, -iff_self, sample, target, cap, Curve.Boundary.Complete.Sample.nearBoxDescendantSample,
      Curve.Boundary.Complete.Sample.nearBoxDescendantRequestWidth] using sample.parameterInside
  have descendantRefines := entry.child.request_refines target
  have sampleInsideParent :
      entry.child.cell.interval.Contains sample.parameter :=
    ⟨descendantRefines.1.trans sampleInside.1,
      sampleInside.2.trans descendantRefines.2⟩
  have lowerLeDenominator : lower ≤
      Data.Gaussian.Norm.Basic.normSq
        (entry.parent.parent.chart.parameterization.curve.denominatorAt
          sample.parameter) := by
    simpa only [-eq_self, -iff_self, lower] using denominatorLower sample.parameter sampleInsideParent
  let conditionLowerPredicate := fun condition :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial =>
    -cap < condition.eval sample.parameter
  have relationsLower : Data.List.Forall (conditionLowerPredicate ∘ Sigma.fst)
      entry.parent.event.1.profile.relations :=
    Data.List.All.forall_iff_mem.mpr (by
      intro relation relationMember
      exact entry.child.request_condition_eval_gt_neg_cap allNonnegative
        relation relationMember capPositive sample.parameter (by
          simpa only [-eq_self, -iff_self, target, cap] using sampleInside))
  have mappedLower :
      Data.List.Forall conditionLowerPredicate
        (entry.parent.event.1.profile.relations.map Sigma.fst) := by
    have alignment :
        Data.List.Forall (conditionLowerPredicate ∘ Sigma.fst)
            entry.parent.event.1.profile.relations ↔
          Data.List.Forall conditionLowerPredicate
            (entry.parent.event.1.profile.relations.map Sigma.fst) :=
      (Data.List.All.forall_map_iff
        (values := entry.parent.event.1.profile.relations)
        (predicate := conditionLowerPredicate) (map := Sigma.fst)).symm
    exact alignment.mp relationsLower
  rw [entry.parent.event.1.profile.conditions_eq] at mappedLower
  have boxConditionsLower : Data.List.Forall conditionLowerPredicate
      (Curve.Box.conditionPolynomials
        entry.parent.parent.chart.parameterization.curve current) :=
    (Data.List.All.forall_cons.mp mappedLower).2
  change conditionLowerPredicate _ ∧ conditionLowerPredicate _ ∧
    conditionLowerPredicate _ ∧ conditionLowerPredicate _ at boxConditionsLower
  apply Curve.Box.point_within_radius_of_condition_lower
    entry.parent.parent.chart.parameterization.curve current sample.parameter
      radius lower radiusPositive.le sample.denominatorNonzero
        lowerLeDenominator
  · exact boxConditionsLower.1
  · exact boxConditionsLower.2.1
  · exact boxConditionsLower.2.2.1
  · exact boxConditionsLower.2.2.2

/-- Original-polynomial residual of a descendant sample once its displayed
affine point is supplied inside a target box. -/
theorem
  NonpoleCompleteRequestDescendantSample.normSq_eval_point_le_of_inside
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    {entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon}
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (sample : Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample entry target)
    (targetBox : Box)
    (pointInside : targetBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) ≤
      Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient
          (targetBox := targetBox) entry.parent.event.1 * target ^ 2 :=
  entry.child.request_normSq_eval_point_le_of_inside target targetPositive
    sample.parameter sample.parameterInside sample.denominatorNonzero
      pointInside

/-- Positive deterministic descendant width making the original-polynomial
residual smaller than a supplied target whenever the sample lies in
`targetBox`. -/
@[expose] def descendantResidualRequestWidth
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) (residualTarget : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth
    (Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient
      (targetBox := targetBox) entry.parent.event.1)
    residualTarget

/-- A positive original-polynomial residual target gives a positive descendant request width. -/
theorem descendantResidualRequestWidth_pos
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) {residualTarget : Fraction.Rational}
    (targetPositive : 0 < residualTarget) :
    0 < Curve.Boundary.Complete.Sample.descendantResidualRequestWidth entry targetBox residualTarget :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    (Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient_nonneg
      (targetBox := targetBox) entry.parent.event.1)
    targetPositive

/-- The bounded non-pole sample at the computed descendant width meets the
requested original-polynomial residual target whenever its affine point is
inside the displayed target box. -/
theorem descendant_sample_residual_lt
    {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {epsilon : Fraction.Rational}
    (entry : Curve.Boundary.Complete.Basic.BoundaryCompleteRequestEntry boundary epsilon)
    (targetBox : Box) {residualTarget : Fraction.Rational}
    (targetPositive : 0 < residualTarget)
    (sample : Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample entry
      (Curve.Boundary.Complete.Sample.descendantResidualRequestWidth entry targetBox residualTarget))
    (pointInside : targetBox.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) < residualTarget := by
  have upper := sample.normSq_eval_point_le_of_inside
    (Curve.Boundary.Complete.Sample.descendantResidualRequestWidth_pos entry targetBox targetPositive)
    targetBox pointInside
  exact upper.trans_lt
    (Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
      (Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient_nonneg
        (targetBox := targetBox) entry.parent.event.1)
      targetPositive)

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Complete.Sample

end
