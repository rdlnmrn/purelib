module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
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
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# A retained polynomial for the intrinsic reciprocal root coordinate

The product q A B uses the existing reciprocal inverse A and cap regular
inverse B. Its derivative is controlled by their fixed initial differential
residual bounds. The resulting ceiling is independent of both the sampled
refinement index and the differential's primitive values.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial half)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_mul)
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The intrinsic reciprocal coordinate polynomial built from the original radicand and retained inverse factors.

The value cache preserves the exact local reciprocal inverse and shared cap inverse polynomials. -/
structure CoordinatePolynomial (sample : Sample comparison capSample) where
  /-- The cached intrinsic reciprocal root-coordinate polynomial. -/ value : Polynomial
  /-- The cached polynomial is exactly the original reciprocal radicand times the retained local and shared inverse
    polynomials. -/ value_eq : value = HyperellipticReciprocal.polynomial curve * sample.retained.inverse.value *
    capSample.inverse.value

constructive_injectivity CoordinatePolynomial

namespace CoordinatePolynomial

variable {sample : Sample comparison capSample}

/-- Cache the product of the original reciprocal radicand and the supplied local and shared inverse polynomials. -/
def build (sample : Sample comparison capSample) :
  CoordinatePolynomial sample :=
  ⟨HyperellipticReciprocal.polynomial curve * sample.retained.inverse.value * capSample.inverse.value, rfl⟩

/-- The retained coordinate polynomial evaluates to the product of its three original factors. -/
theorem eval (coordinate : CoordinatePolynomial sample)
  (point : Gaussian) : coordinate.value.eval point =
    (HyperellipticReciprocal.polynomial curve).eval point * sample.retained.inverse.value.eval point *
      capSample.inverse.value.eval point := by
  rw [coordinate.value_eq, eval_mul, eval_mul]

/-- On an odd-origin chart, the coordinate derivative splits into the original regular radicand term and both retained
differential residuals. -/
theorem derivative_eq (coordinate :
  CoordinatePolynomial sample) (branch :
  HyperellipticReciprocal.originOrder curve = 1)
    (point : Gaussian) : (derivative coordinate.value).eval point =
      half *
      (cap.polynomial.eval point * sample.retained.inverse.value.eval point * capSample.inverse.value.eval point +
        capSample.inverse.value.eval point * differentialResidual
          (HyperellipticReciprocal.polynomial curve) sample.retained.inverse.value point +
        point * sample.retained.inverse.value.eval point * differentialResidual
          cap.polynomial capSample.inverse.value point) := by
  have half_cancel (value : Gaussian) : half * value * 2 = value := by
    calc
      _ = (2 * half) * value := by ring1
      _ = value := by rw [show (2 : Gaussian) * half = 1 by decide,
        Basic.one_mul]
  have qValue : (HyperellipticReciprocal.polynomial curve).eval point = cap.polynomial.eval point * point := by
    rw [HyperellipticReciprocal.polynomial_eval, branch, pow_one, cap.polynomial_eq]
  have qDerivative : (derivative (HyperellipticReciprocal.polynomial curve)).eval point =
      (derivative cap.polynomial).eval point * point + cap.polynomial.eval point := by
    rw [HyperellipticReciprocal.polynomial, branch, Derivative.eval_derivative_shift_one, cap.polynomial_eq]
  rw [coordinate.value_eq]
  simp only [Derivative.eval_derivative_mul, eval_mul,
    differentialResidual, qValue, qDerivative]
  apply Field.mul_right_cancel_of_ne (by decide : (2 : Gaussian) ≠ 0)
  rw [half_cancel]
  ring1

end CoordinatePolynomial

namespace CoordinatePolynomial

set_option genInjectivity false in
/-- Fixed derivative and movement ceilings for the retained intrinsic reciprocal coordinate.

The bounds use the original initial inverse residuals and source displacement, independently of later polynomial stages.
-/
structure CoordinateBounds (comparison : Data regular cell) where
  /-- The cached original regular radicand evaluation ceiling. -/ regularUpper : Coordinate
  /-- The cached ceiling is the original regular polynomial's finite bound on the shared disk bounding box. -/
    regularUpper_eq : regularUpper = denseEvalNormBound cap.polynomial
    RegularBounds.boundingBox
  /-- The cached derivative ceiling built from the original inverse and differential residual bounds. -/ derivativeUpper
    : Coordinate
  /-- The derivative ceiling retains the exact three original radicand and residual contributions. -/ derivativeUpper_eq
    : derivativeUpper = 4 * (regularUpper * comparison.disk.inverseUpper * regular.inverseUpper +
    regular.inverseUpper * comparison.disk.preparation.reciprocal.bound + comparison.disk.inverseUpper *
      regular.differentialUpper)
  /-- The cached inverse-arc coordinate movement scale. -/ slope : Coordinate
  /-- The movement scale is twice the original derivative ceiling times squared source displacement. -/ slope_eq : slope
    = 2 * derivativeUpper * Norm.Basic.normSq parent.model.displacement

constructive_injectivity CoordinateBounds

end CoordinatePolynomial

namespace CoordinatePolynomial.CoordinateBounds

/-- Cache the fixed original regular polynomial, derivative residual and source-displacement bounds before later
sampling. -/
def build (comparison : Data regular cell) :
  CoordinateBounds comparison :=
  let regularUpper := denseEvalNormBound cap.polynomial RegularBounds.boundingBox
  let derivativeUpper := 4 * (regularUpper * comparison.disk.inverseUpper * regular.inverseUpper +
    regular.inverseUpper * comparison.disk.preparation.reciprocal.bound + comparison.disk.inverseUpper *
      regular.differentialUpper)
  ⟨regularUpper, rfl, derivativeUpper, rfl, 2 * derivativeUpper * Norm.Basic.normSq
    parent.model.displacement, rfl⟩

/-- The original regular polynomial's finite-box evaluation ceiling is nonnegative. -/
theorem regularUpper_nonnegative (bounds :
  CoordinateBounds comparison) : 0 ≤
  bounds.regularUpper := by
  rw [bounds.regularUpper_eq]
  exact (denseHornerNormBounds_nonneg _ _).1

/-- The retained original inverse and differential residual ceilings make the derivative bound nonnegative. -/
theorem derivativeUpper_nonnegative (bounds :
  CoordinateBounds comparison) : 0 ≤
  bounds.derivativeUpper := by
  rw [bounds.derivativeUpper_eq]
  exact Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct bounds.regularUpper_nonnegative
        comparison.disk.inverseUpper_positive.le)
      regular.inverseUpper_positive.le)
    (Arithmetic.mul_nonneg_direct regular.inverseUpper_positive.le
      comparison.disk.preparation.reciprocal.bound_nonnegative))
    (Arithmetic.mul_nonneg_direct comparison.disk.inverseUpper_positive.le
      regular.differentialUpper_nonnegative))

/-- The fixed coordinate derivative ceiling and original source displacement give a nonnegative slope. -/
theorem slope_nonnegative (bounds : CoordinateBounds
  comparison) : 0 ≤ bounds.slope := by
  rw [bounds.slope_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) bounds.derivativeUpper_nonnegative)
      (Norm.Basic.normSq_nonneg _)

/-- The squared norm of three original Gaussian summands is at most four times their summed squared norms. -/
private theorem sum_three (first middle last : Gaussian) :
    Norm.Basic.normSq (first + middle + last) ≤ 4 * (Norm.Basic.normSq
      first + Norm.Basic.normSq middle + Norm.Basic.normSq last) := by
  have estimate := (Norm.Bounds.normSq_add_le_two (first + middle) last).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (Norm.Bounds.normSq_add_le_two
      first middle) le_rfl) (by decide))
  exact (estimate.trans (le_add_of_nonneg_right
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2)
      (Norm.Basic.normSq_nonneg last)))).trans_eq (by ring1)

/-- The retained coordinate polynomial derivative satisfies its fixed original ceiling along the actual inverse arc. -/
theorem derivative_bound (bounds : CoordinateBounds
  comparison) {sample : Sample comparison capSample}
    (coordinate : CoordinatePolynomial sample) (branch
      : HyperellipticReciprocal.originOrder curve = 1)
    (parameter : Coordinate) (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Norm.Basic.normSq ((derivative coordinate.value).eval (parent.edge.point
      parameter)⁻¹) ≤ bounds.derivativeUpper := by
  let point := (parent.edge.point parameter)⁻¹
  have boundary := data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have inside := ReciprocalExteriorCollar.inverse_inDisk curve boundary
  have lower := (collar.point_clearance boundary (show 0 ≤ (0 : Coordinate) ∧ (0 :
    Coordinate) ≤ 1 from ⟨le_rfl, by decide⟩)).2
  rw [collar.point_eq, ReciprocalExteriorCollar.deform_zero] at lower
  have first : Norm.Basic.normSq (sample.retained.inverse.value.eval point) ≤
    comparison.disk.inverseUpper := by
    rw [comparison.disk.inverseUpper_eq]
    exact RegularBounds.inverse_le sample.retained.inverse (cell.contains parameter between)
      collar.radicandBound_positive lower
  have second : Norm.Basic.normSq (capSample.inverse.value.eval point) ≤ regular.inverseUpper :=
    by
    rw [capSample.inverse_eq]
    exact regular.inverse_bound index inside
  have radicand : Norm.Basic.normSq (cap.polynomial.eval point) ≤ bounds.regularUpper := by
    rw [bounds.regularUpper_eq]
    exact normSq_eval_le_denseEvalNormBound _ (RegularBounds.boundingBox_contains inside)
  have reciprocalError : Norm.Basic.normSq (differentialResidual
    (HyperellipticReciprocal.polynomial curve) sample.retained.inverse.value point) ≤
      comparison.disk.preparation.reciprocal.bound := by
    have estimate := sample.pullback.reciprocal_differential_bound (cell.contains parameter between)
    rw [sample.inverse_eq] at estimate
    exact estimate.trans (Geometric.Basic.quarterRadius_le_scale
      comparison.disk.preparation.reciprocal.bound_nonnegative index)
  have regularError : Norm.Basic.normSq (differentialResidual
    cap.polynomial capSample.inverse.value point) ≤ regular.differentialUpper := by
    rw [capSample.inverse_eq]
    exact (regular.differential_bound index inside).trans (Geometric.Basic.quarterRadius_le_scale
      regular.differentialUpper_nonnegative index)
  have firstTerm := Arithmetic.mul_le_mul_direct
    (Arithmetic.mul_le_mul_direct radicand first (Norm.Basic.normSq_nonneg _)
      bounds.regularUpper_nonnegative)
    second (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct
      bounds.regularUpper_nonnegative comparison.disk.inverseUpper_positive.le)
  have secondTerm := Arithmetic.mul_le_mul_direct second reciprocalError
    (Norm.Basic.normSq_nonneg _) regular.inverseUpper_positive.le
  have pointBound := Reciprocal.Bounds.disk_unit_bound inside
  have thirdTerm := Arithmetic.mul_le_mul_direct
    (Arithmetic.mul_le_mul_direct pointBound first (Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Coordinate) ≤ 1))
    regularError (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct (by decide)
      comparison.disk.inverseUpper_positive.le)
  rw [coordinate.derivative_eq branch, Norm.Basic.normSq_mul]
  have halfBound : Norm.Basic.normSq half ≤ 1 := by decide
  have scaled (value : Gaussian) : Norm.Basic.normSq
    half * Norm.Basic.normSq value ≤
    Norm.Basic.normSq value :=
    (Arithmetic.mul_le_mul_of_nonneg_right_direct halfBound (Norm.Basic.normSq_nonneg
      value)).trans_eq
      (Fraction.Field.one_mul _)
  apply (scaled _).trans
  apply (sum_three _ _ _).trans
  simp only [Norm.Basic.normSq_mul]
  rw [bounds.derivativeUpper_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (add_le_add firstTerm secondTerm) (by simpa only [Fraction.Field.one_mul] using thirdTerm)) (by decide)

/-- Taylor data is used only inside the finite substitution proof. The executable coordinate polynomial remains the
supplied cached value. -/
private def ofValue (value : Polynomial) (box : Rational.Box) :
    Certificate.DensePrimitive (GCD.derivative value) box :=
  { value := value
    derivative_eq := fun _ => rfl
    remainderBound := Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside =>
      Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside firstInside }

/-- Every coordinate increment along an original inverse-arc subinterval satisfies the fixed retained slope times
squared parameter width. -/
theorem increment_bound (bounds : CoordinateBounds
  comparison) {sample : Sample comparison capSample}
    (coordinate : CoordinatePolynomial sample) (branch
      : HyperellipticReciprocal.originOrder curve = 1)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Norm.Basic.normSq (coordinate.value.eval (parent.edge.point last)⁻¹ - coordinate.value.eval
      (parent.edge.point first)⁻¹) ≤
      bounds.slope * (last - first) ^ 2 := by
  let interval : Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, cell.ordered.le⟩
  have within (parameter : Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  let left := ofValue (⟨[]⟩ :
    Polynomial) (patch.neighborhood count).base.box
  let right := ofValue
    coordinate.value (data.box edge.left.parameter)
  have coefficientBound (parameter : Coordinate) (inside : interval.Contains parameter) :
      Norm.Basic.normSq ((GCD.derivative (⟨[]⟩ : Polynomial)).eval
        (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 * (GCD.derivative coordinate.value).eval (parent.edge.point parameter)⁻¹) ≤
        bounds.derivativeUpper := by
    change Norm.Basic.normSq ((0 : Gaussian) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      (derivative coordinate.value).eval (parent.edge.point parameter)⁻¹) ≤ _
    rw [Basic.zero_sub, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul,
      Power.normSq_pow]
    have multiplier := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _)
      (Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point (within
        parameter inside)))) 2
    have estimate := Arithmetic.mul_le_mul_direct multiplier
      (bounds.derivative_bound coordinate branch parameter inside) (Norm.Basic.normSq_nonneg _) (by
          decide : (0 : Coordinate) ≤ 1 ^ 2)
    simpa only [one_pow, Fraction.Field.one_mul] using estimate
  have estimate := Comparison.increment_difference_le data.boundary interval within left right
    (fun parameter inside => data.source_inside (within parameter inside)) cell.contains bounds.derivativeUpper
      coefficientBound firstInside lastInside
  have values (parameter : Coordinate) : Comparison.comparisonValue parent left right parameter =
      coordinate.value.eval (parent.edge.point parameter)⁻¹ := by
    change 0 + coordinate.value.eval (parent.edge.point parameter)⁻¹ = _
    exact Basic.zero_add _
  rw [values last, values first, ← bounds.slope_eq] at estimate
  exact estimate

end CoordinatePolynomial.CoordinateBounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
