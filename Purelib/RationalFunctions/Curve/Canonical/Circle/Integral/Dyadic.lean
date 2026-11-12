module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Primitive
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Path.Primitive.Polynomial
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Taylor
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

/-!
# Paid dyadic integration of retained circle primitives

The original dyadic endpoint records determine the actual ordered constant
cells on the same supplied rational curve. Their finite primitive errors
are paid by the original dyadic cell-count theorem before any operational
comparison of refinement outputs is constructed.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Path.Primitive
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Riemann.Periods
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian

/-- Read the actual ordered original dyadic edges as same-curve constant integration cells.

Every edge retains both original unit-interval endpoint records. Each cell
reads the supplied curve and coefficient at its original left parameter;
no dyadic edge or nominal endpoint owner is reconstructed by another mesh.
-/
@[expose] def model (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (depth : Nat) (left right : Endpoint) : PathModel :=
  ⟨(dyadicEdges depth left right).map fun edge =>
    coefficientCell base curve coefficient edge.left.parameter (edge.right.parameter - edge.left.parameter)⟩

/-- Exact coefficient agreement at the same actual curve points preserves the actual ordered mapped sample. -/
private theorem mapped_sample_congr (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (first last : Canonical → Canonical)
    (same : ∀ time, first (curve.val.point time) = last (curve.val.point time)) (edges : List ParameterEdge) :
    (PathModel.mk (edges.map fun edge => coefficientCell base curve first edge.left.parameter
      (edge.right.parameter - edge.left.parameter))).integralSample =
    (PathModel.mk (edges.map fun edge => coefficientCell base curve last edge.left.parameter
      (edge.right.parameter - edge.left.parameter))).integralSample := by
  induction edges with
  | nil => rfl
  | cons edge tail previous =>
      dsimp only [PathModel.integralSample] at previous
      change (coefficientCell base curve first edge.left.parameter
        (edge.right.parameter - edge.left.parameter)).integralSample + _ =
        (coefficientCell base curve last edge.left.parameter
          (edge.right.parameter - edge.left.parameter)).integralSample + _
      rewrite [coefficientCell_integralSample, coefficientCell_integralSample, same, previous]
      rfl

/-- Pointwise scalar agreement on the supplied original curve preserves its actual dyadic integral sample. -/
theorem model_sample_congr (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (first last : Canonical → Canonical)
    (same : ∀ time, first (curve.val.point time) = last (curve.val.point time))
    (depth : Nat) (left right : Endpoint) :
    (model base curve first depth left right).integralSample =
      (model base curve last depth left right).integralSample :=
  mapped_sample_congr base curve first last same (dyadicEdges depth left right)

/-- The ordered mapped sample is linear in its actual retained coefficient readings. -/
private theorem mapped_sample_linear (base : Canonical)
    (curve : { value : RationalCurve // value = circle base })
    (first last : Canonical → Canonical) (firstScale lastScale : Canonical) (edges : List ParameterEdge) :
    (PathModel.mk (edges.map fun edge => coefficientCell base curve
      (fun point => firstScale * first point + lastScale * last point) edge.left.parameter
        (edge.right.parameter - edge.left.parameter))).integralSample =
      firstScale * (PathModel.mk (edges.map fun edge => coefficientCell base curve first edge.left.parameter
        (edge.right.parameter - edge.left.parameter))).integralSample +
      lastScale * (PathModel.mk (edges.map fun edge => coefficientCell base curve last edge.left.parameter
        (edge.right.parameter - edge.left.parameter))).integralSample := by
  induction edges with
  | nil => change (0 : Canonical) = firstScale * 0 + lastScale * 0; ring1
  | cons edge tail previous =>
      dsimp only [PathModel.integralSample] at previous
      change (coefficientCell base curve (fun point => firstScale * first point + lastScale * last point)
        edge.left.parameter (edge.right.parameter - edge.left.parameter)).integralSample + _ =
        firstScale * ((coefficientCell base curve first edge.left.parameter
          (edge.right.parameter - edge.left.parameter)).integralSample + _) +
        lastScale * ((coefficientCell base curve last edge.left.parameter
          (edge.right.parameter - edge.left.parameter)).integralSample + _)
      rewrite [coefficientCell_integralSample, coefficientCell_integralSample,
        coefficientCell_integralSample, previous]
      ring1

/-- A finite linear combination of actual same-curve coefficients gives the same linear combination of dyadic samples.

Both original meshes, endpoint records and curve observations are unchanged.
The proof follows the finite ordered cell list and transports only scalar
readings; it does not identify coefficient functions or assume integrals.
-/
theorem model_sample_linear (base : Canonical)
    (curve : { value : RationalCurve // value = circle base }) (first last : Canonical → Canonical)
    (firstScale lastScale : Canonical) (depth : Nat) (left right : Endpoint) :
    (model base curve (fun point => firstScale * first point + lastScale * last point)
      depth left right).integralSample =
      firstScale * (model base curve first depth left right).integralSample +
        lastScale * (model base curve last depth left right).integralSample :=
  mapped_sample_linear base curve first last firstScale lastScale (dyadicEdges depth left right)

/-- The original zero-depth model is the complete actual singleton constant cell. -/
theorem model_zero (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (left right : Endpoint) :
    model base curve coefficient 0 left right =
      ⟨[coefficientCell base curve coefficient left.parameter (right.parameter - left.parameter)]⟩ := rfl

/-- The original midpoint subdivision retains the two same-curve models in their exact concatenation order. -/
theorem model_succ (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (depth : Nat) (left right : Endpoint) :
    let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    model base curve coefficient (depth + 1) left right =
      (model base curve coefficient depth left middle).concat (model base curve coefficient depth middle right) := by
  dsimp only
  change PathModel.mk ((dyadicEdges depth left _ ++ dyadicEdges depth _ right).map _) = _
  rewrite [Map.map_append]
  rfl

/-- The actual ordered model has exactly the original dyadic edge count. -/
theorem model_count (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (depth : Nat) (left right : Endpoint) :
    (model base curve coefficient depth left right).cells.length = 2 ^ depth := by
  change ((dyadicEdges depth left right).map _).length = _
  rewrite [Map.length_map]
  exact dyadicEdges_length depth left right

/-- Every retained exact left observation contributes zero to the original weighted allowance sum. -/
theorem model_weightedAllowance (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (depth : Nat) (left right : Endpoint) :
    (model base curve coefficient depth left right).totalWeightedAllowance = 0 := by
  have weightedZero (edges : List ParameterEdge) :
      (PathModel.mk (edges.map fun edge => coefficientCell base curve coefficient edge.left.parameter
        (edge.right.parameter - edge.left.parameter))).totalWeightedAllowance = 0 := by
    induction edges with
    | nil => rfl
    | cons edge tail previous =>
        change _ * (0 : Fraction.Rational) +
          (PathModel.mk (tail.map fun edge => coefficientCell base curve coefficient edge.left.parameter
            (edge.right.parameter - edge.left.parameter))).totalWeightedAllowance = 0
        rewrite [Fraction.Field.mul_zero_direct, previous, Fraction.Field.zero_add]
        rfl
  exact weightedZero (dyadicEdges depth left right)

/-- Every retained exact left observation has zero allowance throughout the actual ordered model. -/
theorem model_allowance (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (depth : Nat) (left right : Endpoint) :
    (model base curve coefficient depth left right).aggregateAllowance = 0 := by
  unfold PathModel.aggregateAllowance
  rewrite [model_weightedAllowance]
  exact Fraction.Field.mul_zero_direct _

/-- Evaluate the retained parameter primitive at the original cell's real coordinate. -/
private def primitiveAt (primitive : Fraction.Rational → Canonical)
    (parameter : Canonical) : Canonical := primitive parameter.re

/-- Finite primitive increments telescope along the actual original dyadic endpoint joins. -/
private theorem model_telescope (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (primitive : Fraction.Rational → Canonical)
    (depth : Nat) (left right : Endpoint) :
    Path.Primitive.incrementSum (primitiveAt primitive)
      (model base curve coefficient depth left right).cells = primitive right.parameter - primitive left.parameter := by
  induction depth generalizing left right with
  | zero =>
      change primitive (left.parameter + (right.parameter - left.parameter)) - primitive left.parameter + 0 = _
      rewrite [show left.parameter + (right.parameter - left.parameter) = right.parameter by ring1,
        Basic.add_zero]
      rfl
  | succ depth previous =>
      rewrite [model_succ]
      change Path.Primitive.incrementSum _ (_ ++ _) = _
      rewrite [Path.Primitive.incrementSum_append, previous, previous]
      ring1

/-- Actual bounded parameter-primitive errors pay the original ordered dyadic circle sample.

The same two endpoint records supply the parameter evaluations and every
local bound. Finite telescoping and the actual dyadic cell count pay the
Taylor and coefficient discrepancy terms separately. The primitive need
not be a function of the curve's spatial point.
-/
theorem model_primitive_error_le (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient : Canonical → Canonical) (primitive : Fraction.Rational → Canonical)
    (taylor coefficientError : Fraction.Rational)
    (localBound : ∀ first last : Endpoint, Norm.Basic.normSq
      (primitive last.parameter - primitive first.parameter -
        (coefficientCell base curve coefficient first.parameter (last.parameter - first.parameter)).integralSample) ≤
          taylor * (last.parameter - first.parameter) ^ 4 +
            coefficientError * (last.parameter - first.parameter) ^ 2)
    (depth : Nat) (left right : Endpoint) :
    Norm.Basic.normSq (primitive right.parameter - primitive left.parameter -
      (model base curve coefficient depth left right).integralSample) ≤
      taylor * (right.parameter - left.parameter) ^ 2 *
          quarterRadius ((right.parameter - left.parameter) ^ 2) depth +
        coefficientError * (right.parameter - left.parameter) ^ 2 := by
  have bounded (cell : Cell.Basic.CellModel)
      (member : cell ∈ (model base curve coefficient depth left right).cells) :
      Canonical.normSq (primitiveAt primitive cell.finish - primitiveAt primitive cell.start -
        cell.integralSample) ≤ taylor * quarterRadius ((right.parameter - left.parameter) ^ 2) depth ^ 2 +
          coefficientError * quarterRadius ((right.parameter - left.parameter) ^ 2) depth := by
    change cell ∈ (dyadicEdges depth left right).map _ at member
    obtain ⟨edge, edgeMember, rfl⟩ := Map.mem_map.mp member
    have original := localBound edge.left edge.right
    rewrite [Norm.Basic.normSq_eq_canonical] at original
    have width := Riemann.Meshes.UniformPrimitiveMesh.dyadicEdges_width depth left right edge edgeMember
    have fourth : (edge.right.parameter - edge.left.parameter) ^ 4 =
        quarterRadius ((right.parameter - left.parameter) ^ 2) depth ^ 2 := by
      rewrite [← width]
      ring1
    change Canonical.normSq (primitive (edge.left.parameter + (edge.right.parameter - edge.left.parameter)) -
      primitive edge.left.parameter - (coefficientCell base curve coefficient edge.left.parameter
        (edge.right.parameter - edge.left.parameter)).integralSample) ≤ _
    rewrite [show edge.left.parameter + (edge.right.parameter - edge.left.parameter) = edge.right.parameter by ring1]
    exact original.trans_eq (by rewrite [fourth, width]; rfl)
  have original := Path.Primitive.Dyadic.dyadic_integral_error_le (primitiveAt primitive)
    (model base curve coefficient depth left right)
    (start := ⟨left.parameter, 0⟩) (finish := ⟨right.parameter, 0⟩)
    (model_telescope base curve coefficient primitive depth left right) depth
    (model_count base curve coefficient depth left right) ((right.parameter - left.parameter) ^ 2)
    taylor coefficientError bounded
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact original

/-- Actual fourth-order spatial primitive bounds pay the original finite dyadic model error.

The original retained cell count, width and finite Cauchy estimate cancel
both count factors. The resulting quarter-radius bound concerns the actual
model sample and independently computed physical primitive endpoints.
-/
theorem model_error_le (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient primitive : Canonical → Canonical) (factor : Fraction.Rational)
    (localBound : ∀ time delta, Norm.Basic.normSq
      (primitive (curve.val.point (time + delta)) - primitive (curve.val.point time) -
        (coefficientCell base curve coefficient time delta).integralSample) ≤ factor * delta ^ 4)
    (depth : Nat) (left right : Endpoint) :
    Norm.Basic.normSq (primitive (curve.val.point right.parameter) - primitive (curve.val.point left.parameter) -
      (model base curve coefficient depth left right).integralSample) ≤
        quarterRadius (factor * (right.parameter - left.parameter) ^ 4) depth := by
  have bounded (first last : Endpoint) : Norm.Basic.normSq
      (primitive (curve.val.point last.parameter) - primitive (curve.val.point first.parameter) -
        (coefficientCell base curve coefficient first.parameter (last.parameter - first.parameter)).integralSample) ≤
      factor * (last.parameter - first.parameter) ^ 4 + (0 : Fraction.Rational) *
        (last.parameter - first.parameter) ^ 2 := by
    have original := localBound first.parameter (last.parameter - first.parameter)
    rewrite [show first.parameter + (last.parameter - first.parameter) = last.parameter by ring1] at original
    exact original.trans_eq (by ring1)
  have original := model_primitive_error_le base curve coefficient
    (fun time => primitive (curve.val.point time)) factor 0 bounded depth left right
  exact original.trans_eq (by
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1)

/-- The original retained zero endpoint of the unit parameter interval. -/
private def unitFirst : Endpoint := ⟨0, by decide +kernel⟩

/-- The original retained one endpoint of the unit parameter interval. -/
private def unitLast : Endpoint := ⟨1, by decide +kernel⟩

/-- The actual unit-quarter model is close to its independently computed primitive increment. -/
private theorem unit_error_le (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient primitive : Canonical → Canonical) (factor : Fraction.Rational)
    (localBound : ∀ time delta, Norm.Basic.normSq
      (primitive (curve.val.point (time + delta)) - primitive (curve.val.point time) -
        (coefficientCell base curve coefficient time delta).integralSample) ≤ factor * delta ^ 4)
    (index : Nat) :
    Norm.Basic.normSq ((model base curve coefficient index unitFirst unitLast).integralSample -
      (primitive (curve.val.point 1) - primitive (curve.val.point 0))) ≤ quarterRadius factor index := by
  have original := model_error_le base curve coefficient primitive factor localBound index unitFirst unitLast
  change Norm.Basic.normSq (primitive (curve.val.point 1) - primitive (curve.val.point 0) - _) ≤
    quarterRadius (factor * ((1 : Fraction.Rational) - 0) ^ 4) index at original
  rewrite [show ((1 : Fraction.Rational) - 0) ^ 4 = 1 by decide +kernel,
    Fraction.Field.mul_one_direct] at original
  rewrite [show (model base curve coefficient index unitFirst unitLast).integralSample -
      (primitive (curve.val.point 1) - primitive (curve.val.point 0)) =
    -(primitive (curve.val.point 1) - primitive (curve.val.point 0) -
      (model base curve coefficient index unitFirst unitLast).integralSample) by ring1,
    Norm.Basic.normSq_neg]
  exact original

/-- Construct the original refinement program from its actual same-curve cells and proved finite primitive bounds.

The supplied endpoint values are exact retained evaluations, not values
defined from integral outputs. Their difference pays the original program's
center bound; both later-sample and allowance bounds are derived internally.
-/
private def programOfBound (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient primitive : Canonical → Canonical) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (start finish : Canonical) (start_eq : start = primitive (curve.val.point 0))
    (finish_eq : finish = primitive (curve.val.point 1))
    (localBound : ∀ time delta, Norm.Basic.normSq
      (primitive (curve.val.point (time + delta)) - primitive (curve.val.point time) -
        (coefficientCell base curve coefficient time delta).integralSample) ≤ factor * delta ^ 4) :
    RefinementProgram := by
  let models := fun index => model base curve coefficient index unitFirst unitLast
  let difference := finish - start
  have error (index : Nat) : Norm.Basic.normSq ((models index).integralSample - difference) ≤
      quarterRadius factor index := by
    rewrite [show difference = primitive (curve.val.point 1) - primitive (curve.val.point 0) from
      congrArg₂ (fun last first => last - first) finish_eq start_eq]
    exact unit_error_le base curve coefficient primitive factor localBound index
  have scaleNonnegative : 0 ≤ 4 * factor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative
  have centerNonnegative : 0 ≤ 2 * (Norm.Basic.normSq difference + factor) := by
    have summed := Arithmetic.add_le_add_direct (Norm.Basic.normSq_nonneg difference) nonnegative
    rewrite [Fraction.Field.zero_add] at summed
    exact Arithmetic.mul_nonneg_direct (by decide +kernel) summed
  exact
    { model := models
      errorScale := 4 * factor
      errorScale_nonneg := scaleNonnegative
      modelAllowance_le := fun index => by
        rewrite [model_allowance]
        exact quarterRadius_nonneg scaleNonnegative index
      later_close := fun {earlier later} ordered => by
        rewrite [← Norm.Basic.normSq_eq_canonical]
        have laterError := (error later).trans (quarterRadius_antitone nonnegative ordered)
        have earlierError := error earlier
        rewrite [show (models later).integralSample - (models earlier).integralSample =
          ((models later).integralSample - difference) - ((models earlier).integralSample - difference) by ring1]
        exact (Norm.Bounds.normSq_sub_le_two _ _).trans
          ((Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct laterError earlierError) (by decide +kernel)).trans_eq
              (by rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]; ring1))
      centerBound := 2 * (Norm.Basic.normSq difference + factor)
      centerBound_nonneg := centerNonnegative
      sample_bounded := fun index => by
        rewrite [← Norm.Basic.normSq_eq_canonical]
        have bounded := (error index).trans (quarterRadius_le_scale nonnegative index)
        rewrite [show (models index).integralSample =
          ((models index).integralSample - difference) + difference by ring1]
        exact (Norm.Bounds.normSq_add_le_two _ _).trans
          ((Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct bounded (Fraction.Order.Basic.le_refl _))
            (by decide +kernel)).trans_eq (by ring1)) }

/-- Construct the original paid primitive edge from actual dyadic cell integrals and independently retained endpoints.

The two exact original endpoint sources and original program are built once.
The existing finite sample-comparison constructor supplies operational
accuracy requests while retaining all three actual input procedures.
-/
private def edgeOfBound (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient primitive : Canonical → Canonical) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (localBound : ∀ time delta, Norm.Basic.normSq
      (primitive (curve.val.point (time + delta)) - primitive (curve.val.point time) -
        (coefficientCell base curve coefficient time delta).integralSample) ≤ factor * delta ^ 4) :
    PrimitiveEdge (PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive (curve.val.point 0))))
      (PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive (curve.val.point 1)))) :=
  let start := primitive (curve.val.point 0)
  let finish := primitive (curve.val.point 1)
  let firstSource := GeometricApproximation.exact start
  let lastSource := GeometricApproximation.exact finish
  let program := programOfBound base curve coefficient primitive factor nonnegative start finish rfl rfl localBound
  PrimitiveEdge.ofSampleComparison firstSource lastSource program factor nonnegative
    (fun index => unit_error_le base curve coefficient primitive factor localBound index)

/-- The original sample-comparison constructor retains the complete same-curve dyadic model. -/
private theorem edgeOfBound_model (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (coefficient primitive : Canonical → Canonical) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (localBound : ∀ time delta, Norm.Basic.normSq
      (primitive (curve.val.point (time + delta)) - primitive (curve.val.point time) -
        (coefficientCell base curve coefficient time delta).integralSample) ≤ factor * delta ^ 4)
    (index : Nat) :
    ((edgeOfBound base curve coefficient primitive factor nonnegative localBound).program.model index) =
      model base curve coefficient index unitFirst unitLast := by
  unfold edgeOfBound
  rewrite [PrimitiveEdge.ofSampleComparison_program]
  rfl

/-- Nonnegative original Taylor and coefficient ceilings give the displayed circle-cell error factor. -/
private theorem paidFactor_nonnegative (base : Canonical) {taylor coefficient : Fraction.Rational}
    (taylorNonnegative : 0 ≤ taylor) (coefficientNonnegative : 0 ≤ coefficient) :
    0 ≤ 2 * (taylor * (4 * Norm.Basic.normSq base) ^ 2 +
      8 * Norm.Basic.normSq base * coefficient) := by
  have first := Arithmetic.mul_nonneg_direct taylorNonnegative
    (Arithmetic.sq_nonneg_direct (4 * Norm.Basic.normSq base))
  have second := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 8)
      (Norm.Basic.normSq_nonneg base)) coefficientNonnegative
  have summed := Arithmetic.add_le_add_direct first second
  rewrite [Fraction.Field.zero_add] at summed
  exact Arithmetic.mul_nonneg_direct (by decide +kernel) summed

/-- The actual retained original coefficient-Horner ceiling is nonnegative. -/
private theorem coefficient_nonnegative (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (box : Geometry.Rational.Box) (preparation : Antiderivative.BoxPreparation source retained box) :
    0 ≤ preparation.2.val := by
  rewrite [preparation.2.property]
  exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg (Dense.Evaluation.toDense source) box).1

/-- Integrate the actual regular polynomial on the supplied original circle with its retained finite primitive.

The original boxed preparation supplies its actual Taylor and coefficient
ceilings. Internally proved finite cell bounds construct the original
refinement program and its operational comparison to the two original
primitive endpoint sources; no integral agreement is an input.
-/
def polynomialEdge (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base)) :
    PrimitiveEdge
      (PeriodMatrix.geometricNamed (GeometricApproximation.exact (Evaluation.eval retained.val (curve.val.point 0))))
      (PeriodMatrix.geometricNamed (GeometricApproximation.exact (Evaluation.eval retained.val (curve.val.point 1)))) :=
  let factor : Fraction.Rational := 2 * (preparation.1.val.remainderBound * (4 * Norm.Basic.normSq base) ^ 2 +
    8 * Norm.Basic.normSq base * preparation.2.val)
  have nonnegative : 0 ≤ factor := paidFactor_nonnegative base preparation.1.val.remainderBound_nonnegative
    (coefficient_nonnegative source retained (circleBox base) preparation)
  edgeOfBound base curve (Evaluation.eval source) (Evaluation.eval retained.val) factor nonnegative
    (polynomialCell_error_le base curve source retained preparation)

/-- The regular primitive edge retains the complete actual same-curve dyadic model at every original stage. -/
theorem polynomialEdge_model (base : Canonical) (curve : { value : RationalCurve // value = circle base })
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base)) (index : Nat) :
    ((polynomialEdge base curve source retained preparation).program.model index) =
      model base curve (Evaluation.eval source) index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
  unfold polynomialEdge
  exact edgeOfBound_model _ _ _ _ _ _ _ index

/-- Integrate the same retained nonlogarithmic Laurent primitive on the supplied guarded original circle.

The original cached reversal and antiderivative determine the actual
coefficient and endpoint values. The common nonzero floor, boxed caches and
finite dyadic estimate derive the original paid operational primitive edge,
without constructing another numerator, antiderivative or circle.
-/
def reciprocalEdge (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base })
    {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero)) :
    PrimitiveEdge
      (PeriodMatrix.geometricNamed (GeometricApproximation.exact (retained.value (curve.val.point 0))))
      (PeriodMatrix.geometricNamed (GeometricApproximation.exact (retained.value (curve.val.point 1)))) :=
  let slopeBound : Fraction.Rational := preparation.2.val * (Norm.Basic.normSq base)⁻¹ ^ 2
  let taylorBound : Fraction.Rational := preparation.1.val.reciprocalFactor (Norm.Basic.normSq base) preparation.2
  let factor : Fraction.Rational := 2 * (taylorBound * (4 * Norm.Basic.normSq base) ^ 2 +
    8 * Norm.Basic.normSq base * slopeBound)
  have slopeNonnegative : 0 ≤ slopeBound := Arithmetic.mul_nonneg_direct
    (coefficient_nonnegative retained.1.val retained.2 (reciprocalBox base nonzero) preparation)
    (Arithmetic.sq_nonneg_direct _)
  have nonnegative : 0 ≤ factor := paidFactor_nonnegative base
    (preparation.1.val.reciprocalFactor_nonnegative (Norm.Basic.normSq_pos nonzero) preparation.2) slopeNonnegative
  edgeOfBound base curve retained.derivativeValue retained.value factor nonnegative
    (reciprocalCell_error_le base nonzero curve retained preparation)

/-- The polar primitive edge retains the complete actual same-curve dyadic model at every original stage. -/
theorem reciprocalEdge_model (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base })
    {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero))
    (index : Nat) :
    ((reciprocalEdge base nonzero curve retained preparation).program.model index) =
      model base curve retained.derivativeValue index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
  unfold reciprocalEdge
  exact edgeOfBound_model _ _ _ _ _ _ _ index

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic

end

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

/-- Read one same-depth dyadic path from each actual retained quarter curve in its original positive order.

The supplied coefficient is evaluated at the original left endpoints of
those four exact curves. The two balanced halves preserve the original
circuit order without rebuilding any curve or logarithmic programme.
-/
@[expose] def Entries.dyadicModel {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (coefficient : Canonical → Canonical) (depth : Nat) : PathModel :=
  let quarter (index : Fin quarters.length) :=
    let entry := entries.get index
    Dyadic.model (quarterBase base (quarters[index.val]'index.isLt)) entry.1
      coefficient depth ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  ((quarter ⟨0, by decide +kernel⟩).concat (quarter ⟨1, by decide +kernel⟩)).concat
    ((quarter ⟨2, by decide +kernel⟩).concat (quarter ⟨3, by decide +kernel⟩))

/-- The actual dyadic sample is the balanced sum of the four supplied same-curve quarter samples. -/
theorem Entries.dyadicModel_sample {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (coefficient : Canonical → Canonical) (depth : Nat) :
    (entries.dyadicModel coefficient depth).integralSample =
      (((Dyadic.model (quarterBase base (quarters[0]'(by decide +kernel)))
          (entries.get ⟨0, by decide +kernel⟩).1 coefficient depth
          ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample +
        (Dyadic.model (quarterBase base (quarters[1]'(by decide +kernel)))
          (entries.get ⟨1, by decide +kernel⟩).1 coefficient depth
          ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample) +
       ((Dyadic.model (quarterBase base (quarters[2]'(by decide +kernel)))
          (entries.get ⟨2, by decide +kernel⟩).1 coefficient depth
          ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample +
        (Dyadic.model (quarterBase base (quarters[3]'(by decide +kernel)))
          (entries.get ⟨3, by decide +kernel⟩).1 coefficient depth
          ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample)) := by
  unfold dyadicModel
  rewrite [PathModel.integralSample_concat, PathModel.integralSample_concat, PathModel.integralSample_concat]
  rfl

/-- Exact coefficient agreement on the actual four supplied curves preserves their same-mesh circuit sample. -/
theorem Entries.dyadicModel_sample_congr {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (first last : Canonical → Canonical)
    (same : ∀ quarter time, first ((entries.get quarter).1.val.point time) =
      last ((entries.get quarter).1.val.point time)) (depth : Nat) :
    (entries.dyadicModel first depth).integralSample = (entries.dyadicModel last depth).integralSample := by
  have quartersSame (quarter : Fin quarters.length) := Dyadic.model_sample_congr
    (quarterBase base (quarters[quarter.val]'quarter.isLt)) (entries.get quarter).1 first last
      (same quarter) depth ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  rewrite [entries.dyadicModel_sample first, entries.dyadicModel_sample last,
    quartersSame ⟨0, by decide +kernel⟩, quartersSame ⟨1, by decide +kernel⟩,
    quartersSame ⟨2, by decide +kernel⟩, quartersSame ⟨3, by decide +kernel⟩]
  rfl

/-- Every retained same-depth circuit path has zero total weighted allowance. -/
theorem Entries.dyadicModel_weightedAllowance {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (coefficient : Canonical → Canonical) (depth : Nat) :
    (entries.dyadicModel coefficient depth).totalWeightedAllowance = 0 := by
  unfold dyadicModel
  dsimp only
  rewrite [PathModel.totalWeightedAllowance_concat, PathModel.totalWeightedAllowance_concat,
    PathModel.totalWeightedAllowance_concat]
  have quartersZero (index : Fin quarters.length) := Dyadic.model_weightedAllowance
    (quarterBase base (quarters[index.val]'index.isLt)) (entries.get index).1
      coefficient depth ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  rewrite [quartersZero ⟨0, by decide +kernel⟩, quartersZero ⟨1, by decide +kernel⟩,
    quartersZero ⟨2, by decide +kernel⟩, quartersZero ⟨3, by decide +kernel⟩]
  ring1

/-- The aggregate allowance reads the same actual circuit path's vanishing weighted allowance. -/
theorem Entries.dyadicModel_allowance {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (coefficient : Canonical → Canonical) (depth : Nat) :
    (entries.dyadicModel coefficient depth).aggregateAllowance = 0 := by
  unfold PathModel.aggregateAllowance
  rewrite [entries.dyadicModel_weightedAllowance]
  ring1

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral

end
