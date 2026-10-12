module
import Purelib.Data.Bool.Decide
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Data.Gaussian.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Riemann.Normalization

public section

/-! In the regular reciprocal chart the sheet polynomial has no leading
derivative term. Its derivative is paid entirely by the two retained inverse
model residuals, so the bound decreases with the common sampling index. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate half)
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_mul)
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {sample : Sample comparison capSample}

/-- In the unramified reciprocal chart, the original coordinate derivative is exactly the sum of its two retained
inverse residual terms. -/
theorem CoordinatePolynomial.regular_derivative_eq (coordinate : Disk.CoordinatePolynomial sample)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) (point : InverseRootPolynomial.Gaussian) :
    (Derivative.derivative coordinate.value).eval point = InverseRootPolynomial.half *
      (capSample.inverse.value.eval point * InverseModelDifferentialResidual.differentialResidual
        (HyperellipticReciprocal.polynomial curve) sample.retained.inverse.value point +
       sample.retained.inverse.value.eval point * InverseModelDifferentialResidual.differentialResidual cap.polynomial
         capSample.inverse.value point) := by
  have polynomials : HyperellipticReciprocal.polynomial curve = cap.polynomial.normalize := by
    rw [HyperellipticReciprocal.polynomial, unramified]
    change DensePolynomial.shift 0
      (Reciprocal.reversed curve.polynomial) = cap.polynomial.normalize
    rw [← cap.polynomial_eq]
    unfold DensePolynomial.shift
    by_cases zero : cap.polynomial.isZero = true
    · rw [if_pos zero, DensePolynomial.normalize_eq_zero_of_isZero zero]
    · have zeroFalse := Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true _ zero
      rw [zeroFalse, if_neg (show (false : Bool) ≠ true by decide)]
      simp only [-eq_self, -iff_self, List.replicate_zero, Purelib.Data.List.Append.append_nil]
      rfl
  rw [coordinate.value_eq]
  simp only [-eq_self, -iff_self, Derivative.eval_derivative_mul, DensePolynomial.eval_mul,
    InverseModelDifferentialResidual.differentialResidual, polynomials,
    Derivative.derivative_normalize, DensePolynomial.eval_normalize]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne (by decide : (2 : InverseRootPolynomial.Gaussian) ≠ 0)
  have cancel (value : InverseRootPolynomial.Gaussian) : InverseRootPolynomial.half * value * 2 = value := by
    calc
      _ = (2 * InverseRootPolynomial.half) * value := by ring1
      _ = value := by rw [show (2 : InverseRootPolynomial.Gaussian) * InverseRootPolynomial.half = 1 by decide,
        Data.Gaussian.Basic.one_mul]
  rw [cancel]
  ring1

/-- Retain the actual common index in both decreasing residual bounds. -/
theorem CoordinatePolynomial.regular_derivative_bound (coordinate : Disk.CoordinatePolynomial sample)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (parameter : InverseRootPolynomial.Coordinate) (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((Derivative.derivative coordinate.value).eval (parent.edge.point
      parameter)⁻¹) ≤
      2 * (regular.inverseUpper * Geometric.Basic.quarterRadius comparison.disk.preparation.reciprocal.bound index +
        comparison.disk.inverseUpper * Geometric.Basic.quarterRadius regular.differentialUpper index) := by
  let point := (parent.edge.point parameter)⁻¹
  have boundary := data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have inside := ReciprocalExteriorCollar.inverse_inDisk curve boundary
  have lower := (collar.point_clearance boundary (show 0 ≤ (0 : InverseRootPolynomial.Coordinate) ∧ (0 :
    InverseRootPolynomial.Coordinate) ≤ 1 from ⟨le_rfl, by decide⟩)).2
  rw [collar.point_eq, ReciprocalExteriorCollar.deform_zero] at lower
  have first : Data.Gaussian.Norm.Basic.normSq (sample.retained.inverse.value.eval point) ≤
    comparison.disk.inverseUpper := by
    rw [comparison.disk.inverseUpper_eq]
    exact RegularBounds.inverse_le sample.retained.inverse (cell.contains parameter between)
      collar.radicandBound_positive lower
  have second : Data.Gaussian.Norm.Basic.normSq (capSample.inverse.value.eval point) ≤ regular.inverseUpper :=
    by
    rw [capSample.inverse_eq]
    exact regular.inverse_bound index inside
  have reciprocalError := sample.pullback.reciprocal_differential_bound (cell.contains parameter between)
  rw [sample.inverse_eq] at reciprocalError
  have regularError : Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
    cap.polynomial capSample.inverse.value point) ≤
      Geometric.Basic.quarterRadius regular.differentialUpper index := by
    rw [capSample.inverse_eq]
    exact regular.differential_bound index inside
  have left := Fraction.Order.Arithmetic.mul_le_mul_direct second reciprocalError
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) regular.inverseUpper_positive.le
  have right := Fraction.Order.Arithmetic.mul_le_mul_direct first regularError (Data.Gaussian.Norm.Basic.normSq_nonneg
    _) comparison.disk.inverseUpper_positive.le
  rw
    [CoordinatePolynomial.regular_derivative_eq
    coordinate unramified, Data.Gaussian.Norm.Basic.normSq_mul]
  have halfBound : Data.Gaussian.Norm.Basic.normSq InverseRootPolynomial.half ≤ 1 := by decide
  apply ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct halfBound (Data.Gaussian.Norm.Basic.normSq_nonneg
    _)).trans_eq (Fraction.Field.one_mul _)).trans
  apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
  simp only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left
    right) (by decide)

/-- The decreasing derivative ceiling from the two original inverse-model residuals at their shared stage. -/
@[expose] def regularDerivativeBound (comparison : ArcSamples.Data regular cell) (index : Nat) : Coordinate :=
  2 * (regular.inverseUpper * Geometric.Basic.quarterRadius comparison.disk.preparation.reciprocal.bound index +
    comparison.disk.inverseUpper * Geometric.Basic.quarterRadius regular.differentialUpper index)

/-- The original regular coordinate movement ceiling including its retained source displacement. -/
@[expose] def regularSlope (comparison : ArcSamples.Data regular cell) (index : Nat) : Coordinate :=
  2 * regularDerivativeBound comparison
    index * Data.Gaussian.Norm.Basic.normSq parent.model.displacement

/-- The fixed geometric scale of the original regular coordinate movement bound.

The two retained inverse-model ceilings and source displacement determine this stage-independent rational scale. -/
@[expose] def regularSlopeScale (comparison : ArcSamples.Data regular cell) : Coordinate :=
  4 * (regular.inverseUpper * comparison.disk.preparation.reciprocal.bound +
    comparison.disk.inverseUpper * regular.differentialUpper) * Data.Gaussian.Norm.Basic.normSq
      parent.model.displacement

/-- The retained original regular-coordinate movement scale is nonnegative.

The original positive inverse ceilings, nonnegative residual bounds and squared source displacement supply each factor.
-/
theorem regularSlopeScale_nonnegative (comparison : ArcSamples.Data regular cell) :
    0 ≤ regularSlopeScale comparison :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct regular.inverseUpper_positive.le
      comparison.disk.preparation.reciprocal.bound_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct comparison.disk.inverseUpper_positive.le
        regular.differentialUpper_nonnegative))) (Data.Gaussian.Norm.Basic.normSq_nonneg _)

/-- The original regular-coordinate slope is exactly its fixed scale's quarter-radius.

Both residual terms use the same retained stage, so their common geometric decay factors out of the original slope. -/
theorem regularSlope_eq (comparison : ArcSamples.Data regular cell) (index : Nat) :
    regularSlope comparison index =
      Geometric.Basic.quarterRadius
      (regularSlopeScale
      comparison) index := by
  unfold regularSlope
    regularDerivativeBound
    regularSlopeScale
  simp only [-eq_self, -iff_self, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Compute a sufficient model index with a certificate for every later sample. The scale depends on retained geometry,
not sampled polynomial size. -/
@[expose] def regularSlopeRequest (comparison : ArcSamples.Data regular cell) (requested :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < requested) (floor : Nat) :
    { index : Nat // floor ≤ index ∧ ∀ later, index ≤ later →
      regularSlope comparison later <
      requested } := by
  let index := Search.firstQuarterBelow
    (regularSlopeScale comparison) floor
    requested
  refine ⟨index, Search.firstQuarterBelow_ge _ _ _, ?_⟩
  intro later after
  rw [regularSlope_eq]
  exact (quarterRadius_antitone
    (regularSlopeScale_nonnegative
    comparison) after).trans_lt
    (Search.firstQuarterBelow_accurate _
      (regularSlopeScale_nonnegative
      comparison) floor requested positive)

/-- Retain a supplied polynomial as a primitive of its derivative with its exact finite-box Taylor remainder
certificate.

The original value and displayed box determine the cached Taylor bound and its increment certificate. -/
@[expose] def primitiveOfValue (value : InverseRootPolynomial.Polynomial) (box : Rational.Box) :
    Certificate.DensePrimitive (GCD.derivative value) box :=
  { value := value
    derivative_eq := fun _ => rfl
    remainderBound := Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside =>
      Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside firstInside }

/-- A decreasing bound on the sheet polynomial along the actual inverse edge, including the inverse-coordinate tangent.
-/
theorem CoordinatePolynomial.regular_increment_bound (coordinate : Disk.CoordinatePolynomial sample)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (coordinate.value.eval (parent.edge.point last)⁻¹ - coordinate.value.eval
      (parent.edge.point first)⁻¹) ≤
      regularSlope comparison index * (last
        - first)^2 := by
  let interval : Data.Rat.Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, cell.ordered.le⟩
  have within (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  let left := primitiveOfValue (⟨[]⟩ :
    InverseRootPolynomial.Polynomial) (patch.neighborhood count).base.box
  let right := primitiveOfValue
    coordinate.value (data.box edge.left.parameter)
  have coefficientBound (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq ((GCD.derivative (⟨[]⟩ : InverseRootPolynomial.Polynomial)).eval
        (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 * (GCD.derivative coordinate.value).eval (parent.edge.point parameter)⁻¹) ≤
        regularDerivativeBound comparison
          index := by
    change Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      (Derivative.derivative coordinate.value).eval (parent.edge.point parameter)⁻¹) ≤ _
    rw [Data.Gaussian.Basic.zero_sub, Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul,
      Power.normSq_pow]
    have multiplier := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve
        (data.boundary.point (within parameter inside)))) 2
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_direct multiplier

        (CoordinatePolynomial.regular_derivative_bound
        coordinate unramified parameter inside) (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 ^ 2)
    simpa only [-eq_self, -iff_self,
      regularDerivativeBound, one_pow,
      Fraction.Field.one_mul] using estimate
  have estimate := Comparison.increment_difference_le data.boundary interval within left right
    (fun parameter inside => data.source_inside (within parameter inside)) cell.contains
    (regularDerivativeBound comparison
      index) coefficientBound firstInside lastInside
  have values (parameter : InverseRootPolynomial.Coordinate) : Comparison.comparisonValue parent left right parameter =
      coordinate.value.eval (parent.edge.point parameter)⁻¹ := by
    change 0 + coordinate.value.eval (parent.edge.point parameter)⁻¹ = _
    exact Data.Gaussian.Basic.zero_add _
  rw [values last, values first] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial
