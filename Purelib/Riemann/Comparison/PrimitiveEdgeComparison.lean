module

import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Riemann.Normalization.InverseRootComparison
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Geometry.Rational.Affine
public import Purelib.Polynomial.Clearance.Box.Region

public import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Quantified primitive gluing along shared model edges

The face clearance gives an inverse-model norm ceiling independent of the
Newton index.  Together with a cached numerator bound and the fixed edge
transition it controls primitive mismatch by the two residual budgets alone.
The primitive on the second face is translated to agree at the anchor;
its drift is bounded along the entire shared edge, not just at sample cuts.
-/

namespace Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

/-- The original polynomial clearance certificate on a rational Gaussian box. -/
abbrev RegionClearance := Purelib.Polynomial.Clearance.Box.Region.RegionClearance
/-- The original dense polynomial primitive certificate on its retained box. -/
abbrev DensePrimitive := Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached numerator and inverse-model squared-norm bounds for a polynomial with retained box clearance.

The exact cache equations retain the dense numerator evaluation bound and one plus four divided by the original positive
clearance bound. -/
structure PrimitiveOverlapBounds {polynomial : Polynomial} {box : Box}
    (clearance : RegionClearance polynomial box) (numerator : Polynomial) where
  /-- The cached squared-norm bound for the original numerator throughout the box. -/ numeratorUpper : Coordinate
  /-- The numerator cache equals the original dense polynomial box evaluation bound. -/ numeratorUpper_eq :
    numeratorUpper = Bounds.Box.denseEvalNormBound numerator box
  /-- The cached squared-norm bound for inverse-root model values in the cleared box. -/ inverseUpper : Coordinate
  /-- The inverse cache equals one plus four divided by the original clearance bound. -/ inverseUpper_eq : inverseUpper
    = 1 + 4 / clearance.bound

constructive_injectivity PrimitiveOverlapBounds

namespace PrimitiveOverlapBounds

variable {polynomial numerator : Polynomial} {box : Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {clearance
  : RegionClearance polynomial box}

section
open Purelib.Polynomial.Dense.Gaussian
/-- Cache the exact numerator and inverse-model bounds from the original clearance and numerator. -/
def build (clearance : RegionClearance polynomial box) (numerator : Polynomial) : PrimitiveOverlapBounds clearance
  numerator :=
  ⟨Bounds.Box.denseEvalNormBound numerator box, rfl, 1 + 4 / clearance.bound, rfl⟩

/-- The retained numerator squared-norm bound is nonnegative. -/
theorem numeratorUpper_nonnegative (bounds : PrimitiveOverlapBounds clearance numerator) : 0 ≤ bounds.numeratorUpper :=
  by
  rw [bounds.numeratorUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg numerator box).1

end

open Purelib.Data.Rat in
/-- The retained inverse-model squared-norm bound is strictly positive. -/
theorem inverseUpper_positive (bounds : PrimitiveOverlapBounds clearance numerator) : 0 < bounds.inverseUpper := by
  rw [bounds.inverseUpper_eq]
  exact (show (0 : Coordinate) < 1 by decide).trans_le
    (le_add_of_nonneg_right (Fraction.Order.Field.div_nonneg_direct (by decide) clearance.positive.le))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Every original inverse-root model value inside the cleared box satisfies the retained inverse squared-norm bound. -/
theorem inverse_norm_le (bounds : PrimitiveOverlapBounds clearance numerator) (model : Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) : normSq (model.value.eval point) ≤ bounds.inverseUpper := by
  have residual : normSq (1 - polynomial.eval point * (model.value.eval point) ^ 2) ≤ 1 / 16 := by
    rw [← model.residual_eq]
    exact (model.residualBound point inside).trans model.bound_small
  have squareBound : normSq (model.value.eval point) ^ 2 ≤ 4 / clearance.bound := by
    apply (Fraction.Order.Field.le_div_iff_pos clearance.positive).2
    calc
      _ = clearance.bound * normSq (model.value.eval point) ^ 2 := by ring1
      _ ≤ normSq (polynomial.eval point) * normSq (model.value.eval point) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          simpa only [Norm.Basic.normSq_eq_canonical] using clearance.lower point inside)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ ≤ 4 := by
        have scalar := InverseRootComparison.normalized_value_bound
          (parameter := polynomial.eval point) (value := model.value.eval point)
          (by simpa only [Norm.Basic.normSq_eq_canonical] using residual)
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
  have elementary : normSq (model.value.eval point) ≤ 1 + normSq (model.value.eval point) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have nonnegative := add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct (normSq (model.value.eval point) - 1))
      (Basic.Canonical.normSq_nonneg (model.value.eval point))
    exact nonnegative.trans_eq (by ring1)
  rw [bounds.inverseUpper_eq]
  exact elementary.trans (add_le_add le_rfl squareBound)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- The product of the original numerator evaluation and inverse-root model value satisfies the product of the two
retained bounds. -/
theorem numerator_inverse_le (bounds : PrimitiveOverlapBounds clearance numerator) (model : Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) :
    normSq (numerator.eval point * model.value.eval point) ≤ bounds.numeratorUpper * bounds.inverseUpper := by
  rw [Basic.Canonical.normSq_mul]
  have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
  rw [Norm.Basic.normSq_eq_canonical] at scalar
  apply Fraction.Order.Arithmetic.mul_le_mul_direct
    (scalar.trans_eq bounds.numeratorUpper_eq.symm)
    (bounds.inverse_norm_le model inside) (Basic.Canonical.normSq_nonneg _) bounds.numeratorUpper_nonnegative

end PrimitiveOverlapBounds

namespace EdgeTransition

variable {polynomial numerator leftCoefficient rightCoefficient : Polynomial} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {clearance : RegionClearance polynomial leftBox}

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Normalization in
/-- Bound the signed coefficient gap along the retained edge by the original residual sum and cached numerator/inverse
bounds. -/
theorem coefficient_gap_le (edge : InverseModelEdgeTransition.EdgeTransition left right start finish)
    (bounds : PrimitiveOverlapBounds clearance numerator) {parameter : Coordinate}
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (numerator.eval (Affine.line start (finish - start) parameter) *
      (left.value.eval (Affine.line start (finish - start) parameter) -
        edge.sign * right.value.eval (Affine.line start (finish - start) parameter))) ≤
      6 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) := by
  let sample := edge.sampleAt parameter inside
  have estimate := sample.coefficient_distance_le (edge.left_contains_at inside) (edge.right_contains_at inside)
    (numerator.eval (Affine.line start (finish - start) parameter))
  rw [edge.sampleAt_selected parameter inside, sample.leftValue_eq] at estimate
  have allowanceNonnegative : 0 ≤ 6 * (left.bound + right.bound) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative right.bound_nonnegative)
  have identity : numerator.eval (Affine.line start (finish - start) parameter) *
      (left.value.eval (Affine.line start (finish - start) parameter) -
        edge.sign * right.value.eval (Affine.line start (finish - start) parameter)) =
    numerator.eval (Affine.line start (finish - start) parameter) * left.value.eval (Affine.line start (finish - start)
      parameter) -
      numerator.eval (Affine.line start (finish - start) parameter) * (edge.sign * right.value.eval (Affine.line start
        (finish - start) parameter)) := by ring1
  rw [identity]
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (bounds.numerator_inverse_le left (edge.left_contains_at inside)) allowanceNonnegative)

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Normalization in
/-- Bound the signed difference of two primitive increments along the retained common model edge.

The original coefficient equations identify the numerator times each model. The estimate retains both primitive owners,
the transition sign, edge squared length and squared parameter displacement. -/
theorem primitive_increment_le (edge : InverseModelEdgeTransition.EdgeTransition left right start finish)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = numerator.eval point * left.value.eval point)
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = numerator.eval point * right.value.eval point)
    {first last : Coordinate} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((leftPrimitive.value.eval (Affine.line start (finish - start) first) -
        leftPrimitive.value.eval (Affine.line start (finish - start) last)) -
      edge.sign * (rightPrimitive.value.eval (Affine.line start (finish - start) first) -
        rightPrimitive.value.eval (Affine.line start (finish - start) last))) ≤
      12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) *
        normSq (finish - start) * (first - last) ^ 2 := by
  have gap (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      normSq (leftCoefficient.eval (Affine.line start (finish - start) parameter) -
        edge.sign * rightCoefficient.eval (Affine.line start (finish - start) parameter)) ≤
        6 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) := by
    rw [leftCoefficient_eq, rightCoefficient_eq]
    have identity : numerator.eval (Affine.line start (finish - start) parameter) * left.value.eval (Affine.line start
      (finish - start) parameter) -
        edge.sign * (numerator.eval (Affine.line start (finish - start) parameter) * right.value.eval (Affine.line start
          (finish - start) parameter)) =
      numerator.eval (Affine.line start (finish - start) parameter) *
        (left.value.eval (Affine.line start (finish - start) parameter) - edge.sign * right.value.eval (Affine.line
          start (finish - start) parameter)) := by ring1
    rw [identity]
    exact Riemann.Comparison.PrimitiveEdgeComparison.EdgeTransition.coefficient_gap_le edge bounds inside
  have scalar := Primitive.Segment.Comparison.DensePrimitive.difference_increment_le leftPrimitive rightPrimitive
    edge.sign start (finish - start)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using edge.sign_norm)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds)
    (fun _ inside => edge.left_contains_at inside) (fun _ inside => edge.right_contains_at inside)
    (6 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper))
    (fun parameter inside => by simpa only [Norm.Basic.normSq_eq_canonical] using gap parameter inside) firstInside
      lastInside
  rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar.trans_eq (by ring1)

end EdgeTransition

open Purelib.Riemann.Normalization in
set_option genInjectivity false in
/-- A retained additive offset aligning two original primitive polynomials at the transition's start.

The offset equation keeps the exact start evaluations and the original transition sign, so the resulting aligned value
has the left primitive's start reading. -/
structure PrimitiveEdgeAnchor {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    (edge : InverseModelEdgeTransition.EdgeTransition left right start finish) (leftPrimitive rightPrimitive :
      Polynomial) where
  /-- The cached signed difference of the two primitive start readings. -/ offset : Gaussian
  /-- The offset equals the original left start value minus the transition sign times the original right start value. -/
    offset_eq : offset = leftPrimitive.eval start - edge.sign * rightPrimitive.eval start

constructive_injectivity PrimitiveEdgeAnchor

namespace PrimitiveEdgeAnchor

variable {polynomial leftCoefficient rightCoefficient numerator : Polynomial} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {edge : Purelib.Riemann.Normalization.InverseModelEdgeTransition.EdgeTransition left right start finish}

open Purelib.Riemann.Normalization in
/-- Cache the exact signed primitive offset at the retained edge start. -/
def build (edge : InverseModelEdgeTransition.EdgeTransition left right start finish) (leftPrimitive rightPrimitive :
  Polynomial) :
    PrimitiveEdgeAnchor edge leftPrimitive rightPrimitive :=
  ⟨leftPrimitive.eval start - edge.sign * rightPrimitive.eval start, rfl⟩

/-- Read the original right primitive with the retained transition sign and cached additive anchor offset. -/
def alignedValue {leftPrimitive rightPrimitive : Polynomial}
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive rightPrimitive) (point : Gaussian) : Gaussian :=
  anchor.offset + edge.sign * rightPrimitive.eval point

open Purelib in
/-- The anchored right primitive agrees exactly with the original left primitive at the retained start. -/
theorem aligned_at_start {leftPrimitive rightPrimitive : Polynomial}
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive rightPrimitive) :
      Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveEdgeAnchor.alignedValue anchor start = leftPrimitive.eval
      start := by
  rw [alignedValue, anchor.offset_eq]
  ring1

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Normalization in
/-- Bound the anchored primitive discrepancy at any point of the retained edge.

The estimate keeps the original clearance bounds, both model residual bounds and the point's squared distance from the
start, with the two exact coefficient equations. -/
theorem drift_le {clearance : RegionClearance polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = numerator.eval point * left.value.eval point)
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = numerator.eval point * right.value.eval point)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (leftPrimitive.value.eval (Affine.line start (finish - start) parameter) -
      Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveEdgeAnchor.alignedValue anchor (Affine.line start (finish -
        start) parameter)) ≤
      12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) *
        normSq (Affine.line start (finish - start) parameter - start) := by
  have estimate := Riemann.Comparison.PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le edge bounds
    leftPrimitive rightPrimitive leftCoefficient_eq rightCoefficient_eq
    inside (show (0 : Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
  rw [InverseModelEdgeTransition.line_zero] at estimate
  have distance := Affine.normSq_line_sub start (finish - start) parameter 0
  rw [InverseModelEdgeTransition.line_zero, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at distance
  rw [alignedValue, anchor.offset_eq, distance]
  have identity : leftPrimitive.value.eval (Affine.line start (finish - start) parameter) -
      (leftPrimitive.value.eval start - edge.sign * rightPrimitive.value.eval start +
        edge.sign * rightPrimitive.value.eval (Affine.line start (finish - start) parameter)) =
    (leftPrimitive.value.eval (Affine.line start (finish - start) parameter) - leftPrimitive.value.eval start) -
      edge.sign * (rightPrimitive.value.eval (Affine.line start (finish - start) parameter) - rightPrimitive.value.eval
        start) := by ring1
  rw [identity]
  exact estimate.trans_eq (by ring1)

end PrimitiveEdgeAnchor

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- A cached geometric refinement index making the original edge primitive-comparison scale smaller than a requested
target.

The exact scale combines both residual bounds, numerator and inverse bounds, and the original edge squared length.
Accuracy refers to its retained quarter-radius schedule. -/
structure PrimitiveEdgeAccuracy {polynomial numerator : Polynomial} {leftBox rightBox : Box}
    {clearance : RegionClearance polynomial leftBox} (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) where
  /-- The retained nonnegative primitive-comparison scale for this original edge and model pair. -/ scale : Coordinate
  /-- The scale equals twelve times the residual sum, cached numerator and inverse bounds, and original edge squared
    length. -/ scale_eq : scale = 12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) *
    normSq (finish - start)
  /-- The retained simultaneous model-refinement index selected for the target. -/ index : Nat
  /-- The retained scale's quarter-radius at the chosen index is strictly below the target. -/ accurate :
    Geometric.Basic.quarterRadius scale index < target

constructive_injectivity PrimitiveEdgeAccuracy

namespace PrimitiveEdgeAccuracy

variable {polynomial numerator : Polynomial} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian} {target :
      Coordinate}

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Search the original nonnegative edge comparison scale for a quarter-radius index below the positive target.

The returned request retains the exact scale, chosen index and strict accuracy proof for simultaneous refinement of the
two original models. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) (positive : 0 < target) :
    PrimitiveEdgeAccuracy bounds left right start finish target :=
  let scale := 12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative
        right.bound_nonnegative))
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (Basic.Canonical.normSq_nonneg _)
  ⟨scale, rfl, Geometric.Search.firstQuarterBelow scale 0 target,
    Geometric.Search.firstQuarterBelow_accurate scale nonnegative 0 target positive⟩

open Purelib.Approximation.Rational in
/-- Refining both original models at the retained request index makes their edge comparison scale strictly smaller than
the target. -/
theorem refined_scale_lt (request : PrimitiveEdgeAccuracy bounds left right start finish target) :
    12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) < target := by
  have identity : 12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) =
      Geometric.Basic.quarterRadius request.scale request.index := by
    rw [left.refine_bound, right.refine_bound, request.scale_eq]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact identity.trans_lt request.accurate

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Normalization in
/-- The anchored primitive discrepancy for both models refined at the retained request index is strictly below the
target along the original edge.

The original primitive coefficient equations and transition certificate supply the pointwise comparison; the retained
quarter-radius search supplies the strict requested accuracy. -/
theorem drift_lt (request : PrimitiveEdgeAccuracy bounds left right start finish target)
    (edge : InverseModelEdgeTransition.EdgeTransition (left.refine request.index) (right.refine request.index) start
      finish)
    {leftCoefficient rightCoefficient : Polynomial}
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = numerator.eval point * (left.refine
      request.index).value.eval point)
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = numerator.eval point * (right.refine
      request.index).value.eval point)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (leftPrimitive.value.eval (Affine.line start (finish - start) parameter) -
      Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveEdgeAnchor.alignedValue anchor (Affine.line start (finish -
        start) parameter)) < target := by
  have estimate := Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveEdgeAnchor.drift_le bounds leftPrimitive
    rightPrimitive anchor leftCoefficient_eq rightCoefficient_eq inside
  have distance := Affine.normSq_line_sub start (finish - start) parameter 0
  rw [InverseModelEdgeTransition.line_zero, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at distance
  have parameterSquare : (parameter - 0) ^ 2 ≤ (1 : Coordinate) := by
    have squared := Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
    exact (by ring1 : (parameter - 0) ^ 2 = parameter ^ 2).trans_le (squared.trans_eq (by ring1))
  have scaleNonnegative : 0 ≤ 12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (left.refine request.index).bound_nonnegative (right.refine request.index).bound_nonnegative))
        (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
      (Basic.Canonical.normSq_nonneg _)
  apply estimate.trans_lt
  rw [distance]
  calc
    _ = (12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)) * (parameter - 0) ^ 2 := by ring1
    _ ≤ (12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parameterSquare scaleNonnegative
    _ = _ := Fraction.Field.mul_one_direct _
    _ < target := request.refined_scale_lt

end PrimitiveEdgeAccuracy

end Purelib.Riemann.Comparison.PrimitiveEdgeComparison
