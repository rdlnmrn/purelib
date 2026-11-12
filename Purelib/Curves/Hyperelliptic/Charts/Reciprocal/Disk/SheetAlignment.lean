module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Uniform

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Riemann.Normalization.InverseModelEdgeOverlap
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
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PrimitiveSamples

open Purelib.Data.Rat.Fraction.Order

section

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Dense.Rational.Sign.Interval

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelEdgeOverlap

open Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Riemann.Normalization.InverseModelOverlapCocycle

open Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-!
# One regular sheet bit on a retained reciprocal cell

The local inverse polynomial comes from the actual retained source cell.
One comparison with the shared regular inverse fixes its polynomial sheet
on every point of that cell's inverse arc. A straight segment is used only
inside the common convex domains to prove constancy of the comparison bit;
it does not replace the integration path.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseModelEdgeOverlap (overlapPolynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Geometry.Rational.Affine (line)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Rational.Box} {capSample :
    Primitives.Sample cap differential index box}

/-- The chord between two original reciprocal-disk points stays in that disk throughout the rational unit interval. -/
private theorem disk_line {first last : Gaussian}
    (firstInside : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Reciprocal.Bounds.InDisk curve.polynomial last)
    {parameter : Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    Reciprocal.Bounds.InDisk curve.polynomial (line first (last - first)
      parameter) := by
  have complement : 0 ≤ 1 - parameter := Arithmetic.sub_nonneg_direct unit.2
  have normBound : Norm.Basic.normSq (line first (last - first) parameter) ≤
      (1 - parameter) * Norm.Basic.normSq first + parameter *
        Norm.Basic.normSq last := by
    apply Arithmetic.le_of_sub_nonneg_direct
    have positive := Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct unit.1 complement) (Norm.Basic.normSq_nonneg (last -
        first))
    apply positive.trans_eq
    simp only [line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Norm.Basic.normSq, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re,
        Basic.mul_im]
    ring1
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct normBound
    (Arithmetic.sq_nonneg_direct (RootRadius.denseLargeSquareRadius curve.polynomial))
  have endpoints := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside complement)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside unit.1)
  unfold Reciprocal.Bounds.InDisk at endpoints ⊢
  exact scaled.trans ((by ring1 : RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
    ((1 - parameter) * Norm.Basic.normSq first + parameter *
      Norm.Basic.normSq last) =
      (1 - parameter) * (RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
        Norm.Basic.normSq first) +
        parameter * (RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 * Norm.Basic.normSq
          last)).trans_le
          (endpoints.trans_eq (by ring1)))

/-- The shared regular cap inverse satisfies the retained quarter-radius residual bound for the reciprocal curve
polynomial. -/
private theorem regular_residual
    (regularChart : HyperellipticReciprocal.originOrder curve = 0) {point : Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Norm.Basic.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval point *
      (capSample.inverse.value.eval point) ^ 2) ≤
      quarterRadius (1 / 256) index := by
  have same : (HyperellipticReciprocal.polynomial curve).eval point = cap.polynomial.eval point := by
    rw [HyperellipticReciprocal.polynomial_eval, regularChart, pow_zero, Basic.mul_one, cap.polynomial_eq]
  rw [same, ← capSample.inverse.residual_eq]
  exact capSample.disk_residual_bound inside

/-- The retained regular cap residual is at most one sixteenth at every stage. -/
private theorem regular_small : quarterRadius (1 / 256) index ≤ (1 / 16 :
  Coordinate) :=
  (quarterRadius_le_scale (by decide +kernel : (0 : Coordinate) ≤ 1 / 256)
    index).trans
    (by decide +kernel)

/-- The local and shared inverse models have one comparison sign on an arc.

Their residual certificates hold along the retained convex segment. A positive
squared-dot lower bound keeps the comparison bit equal at its two endpoints. -/
theorem flip_eq_points (sample : Sample comparison capSample)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0) {first last : Gaussian}
    (firstLocal : (data.box edge.left.parameter).Contains first)
    (lastLocal : (data.box edge.left.parameter).Contains last)
    (firstDisk : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastDisk : Reciprocal.Bounds.InDisk curve.polynomial last) :
    (SignAlignment.build (sample.retained.inverse.value.eval first) (capSample.inverse.value.eval first)).flip =
      (SignAlignment.build (sample.retained.inverse.value.eval last) (capSample.inverse.value.eval last)).flip := by
  let interval : Interval.Bounds := ⟨0, 1, by decide⟩
  have localInside (parameter : Coordinate) (inside : interval.Contains parameter) :
      (data.box edge.left.parameter).Contains (line first (last - first) parameter) :=
    Box.contains_line firstLocal lastLocal inside
  have leftResidual (parameter : Coordinate) (inside : interval.Contains parameter) :
      normSq (1 - (HyperellipticReciprocal.polynomial curve).eval (line first (last
        - first) parameter) *
        (sample.retained.inverse.value.eval (line first (last - first) parameter)) ^ 2) ≤
          sample.retained.inverse.bound := by
    rw [← sample.retained.inverse.residual_eq]
    exact sample.retained.inverse.residualBound _ (localInside parameter inside)
  have rightResidual (parameter : Coordinate) (inside : interval.Contains parameter) :
      normSq (1 - (HyperellipticReciprocal.polynomial curve).eval (line first (last
        - first) parameter) *
        (capSample.inverse.value.eval (line first (last - first) parameter)) ^ 2) ≤
          quarterRadius (1 / 256) index := by
    have scalar := regular_residual (capSample := capSample)
      regularChart (disk_line firstDisk lastDisk inside)
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  let majorant := Box.denseEvalNormMajorant (HyperellipticReciprocal.polynomial curve) (data.box
    edge.left.parameter)
  have majorantPositive : 0 < majorant := Box.denseEvalNormMajorant_pos _ _
  have gapPositive : (0 : Coordinate) < 1 / (768 * majorant) :=
    Field.div_pos_direct (by decide)
      (Arithmetic.mul_pos_direct (by decide +kernel) majorantPositive)
  have gap (parameter : Coordinate) (inside : interval.Contains parameter) :
      1 / (768 * majorant) ≤ (overlapPolynomial sample.retained.inverse.value
        capSample.inverse.value
        first (last - first)).eval parameter ^ 2 := by
    rw [eval_overlapPolynomial]
    exact SignAlignment.dot_squared_lower (SignAlignment.build _ _)
      (leftResidual parameter inside) (rightResidual parameter inside)
      sample.retained.inverse.bound_small regular_small
        majorantPositive
      (by
        have scalar := Box.normSq_eval_le_denseEvalNormMajorant
          (HyperellipticReciprocal.polynomial curve) (localInside parameter inside)
        rw [Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar)
  have zeroInside : interval.Contains 0 := ⟨le_rfl, by decide⟩
  have oneInside : interval.Contains 1 := ⟨by decide, le_rfl⟩
  have signs := Uniform.sign_eq_of_squared_lower
    (overlapPolynomial sample.retained.inverse.value capSample.inverse.value first (last -
      first))
    interval gapPositive gap zeroInside oneInside
  rw [eval_overlapPolynomial, eval_overlapPolynomial] at signs
  have equal :
      (SignAlignment.build (sample.retained.inverse.value.eval (line first (last - first) 0))
        (capSample.inverse.value.eval (line first (last - first) 0))).flip =
      (SignAlignment.build (sample.retained.inverse.value.eval (line first (last - first) 1))
        (capSample.inverse.value.eval (line first (last - first) 1))).flip := by
    rw [SignAlignment.flip_eq_dot_sign (SignAlignment.build _ _)
      (leftResidual 0 zeroInside) (rightResidual 0 zeroInside)
      sample.retained.inverse.bound_small regular_small,
      SignAlignment.flip_eq_dot_sign (SignAlignment.build _ _)
      (leftResidual 1 oneInside) (rightResidual 1 oneInside)
      sample.retained.inverse.bound_small regular_small,
        signs]
  have atZero : line first (last - first) 0 = first := by
    apply Basic.ext <;> simp only [line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.sub_re, Basic.sub_im] <;> ring1
  have atOne : line first (last - first) 1 = last := by
    apply Basic.ext <;> simp only [line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.sub_re, Basic.sub_im] <;> ring1
  rw [atZero, atOne] at equal
  exact equal

set_option genInjectivity false in
/-- A retained sign comparison and signed shared primitive on a reciprocal arc.

The initial comparison bit applies at every point of the covered arc. The
cached primitive uses that same bit and retains the local polynomial owners. -/
structure RegularAlignment (sample : Sample comparison capSample) where
  /-- The original reciprocal curve has a regular, unramified origin chart. -/ regular_chart :
    HyperellipticReciprocal.originOrder curve = 0
  /-- The retained sign comparison at the original left endpoint. -/ first : SignAlignment
    (sample.retained.inverse.value.eval (parent.edge.point edge.left.parameter)⁻¹)
    (capSample.inverse.value.eval (parent.edge.point edge.left.parameter)⁻¹)
  /-- The cached shared cap primitive with the retained original sign. -/ primitive : Polynomial
  /-- The cached primitive is exactly the shared cap polynomial, negated precisely when the retained bit is flipped. -/
    primitive_eq : primitive = if first.flip then -capSample.primitive.value else capSample.primitive.value
  /-- The retained initial sign is the exact comparison bit at every point of the original covered arc. -/ same_flip : ∀
    parameter, edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter →
    (SignAlignment.build (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹)
      (capSample.inverse.value.eval (parent.edge.point parameter)⁻¹)).flip = first.flip

constructive_injectivity RegularAlignment

namespace RegularAlignment

/-- Multiply both compared inverse values by the same original factor while retaining the exact sign bit and
nearest-value certificate. -/
private def scaledAlignment {reference candidate : Gaussian} (factor :
  Gaussian)
    (alignment : SignAlignment reference candidate) : SignAlignment (factor *
      reference) (factor * candidate) where
  flip := alignment.flip
  value := factor * alignment.value
  value_eq := by
    rw [alignment.value_eq]
    cases alignment.flip
    · rfl
    · change factor * (-candidate) = -(factor * candidate)
      ring1
  nearest := by
    rw [← mul_sub, ← mul_add, normSq_mul, normSq_mul]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct alignment.nearest
      (normSq_nonneg factor)

/-- Two original geometric refinement stages reduce the inverse residual to at most one two-hundred-fifty-sixth. -/
private theorem later_small {polynomial : Polynomial} {localBox : Rational.Box}
    (model : Model polynomial localBox) (later : 2 ≤ index) :
    (model.refine index).bound ≤ 1 / 256 := by
  rw [Model.refine_bound]
  apply (quarterRadius_antitone model.bound_nonnegative later).trans
  rw [quarterRadius_eq_mul_pow]
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
    (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)
  exact scaled.trans_eq (by decide +kernel : (1 / 16 : Coordinate) * (1 / 4) ^ 2 = 1 / 256)

/-- Retain the initial local-to-shared sign and its signed primitive, with sign constancy over the original reciprocal
arc. -/
@[expose] def build (sample : Sample comparison capSample) (regularChart :
  HyperellipticReciprocal.originOrder curve = 0) :
    RegularAlignment sample := by
  let first := SignAlignment.build (sample.retained.inverse.value.eval (parent.edge.point edge.left.parameter)⁻¹)
    (capSample.inverse.value.eval (parent.edge.point edge.left.parameter)⁻¹)
  let primitive := if first.flip then -capSample.primitive.value else capSample.primitive.value
  refine ⟨regularChart, first, primitive, rfl, ?_⟩
  intro parameter between
  exact flip_eq_points sample regularChart (cell.contains parameter between)
    (cell.contains edge.left.parameter ⟨le_rfl, cell.ordered.le⟩)
    (ReciprocalExteriorCollar.inverse_inDisk curve
      (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩))
    (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point edge.left.inside))

variable {sample : Sample comparison capSample}

/-- Later fine points consume the retained bit, without another sign search. -/
@[expose] def atPoint (alignment : RegularAlignment sample)
  (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    SignAlignment (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹)
      (capSample.inverse.value.eval (parent.edge.point parameter)⁻¹) where
  flip := alignment.first.flip
  value := if alignment.first.flip then -capSample.inverse.value.eval (parent.edge.point parameter)⁻¹
    else capSample.inverse.value.eval (parent.edge.point parameter)⁻¹
  value_eq := rfl
  nearest := by
    have nearest := (SignAlignment.build (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹)
      (capSample.inverse.value.eval (parent.edge.point parameter)⁻¹)).nearest
    rw [SignAlignment.value_eq, alignment.same_flip parameter between] at nearest
    exact nearest

/-- The retained signed shared inverse differs from the actual local inverse by their residual bounds and original local
inverse norm. -/
theorem distance_le (alignment : RegularAlignment sample)
  (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ -
      (alignment.atPoint parameter between).value) ≤
      6 * (sample.retained.inverse.bound + quarterRadius (1 / 256) index) *
        Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹) :=
          by
  have leftResidual : Norm.Basic.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval
    (parent.edge.point parameter)⁻¹ *
      (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹) ^ 2) ≤ sample.retained.inverse.bound := by
    rw [← sample.retained.inverse.residual_eq, Norm.Basic.normSq_eq_canonical]
    exact sample.retained.inverse.residualBound _ (cell.contains parameter between)
  have rightResidual := regular_residual (capSample :=
    capSample) alignment.regular_chart (ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩))
  rw [Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
  have scalar := (alignment.atPoint parameter between).distance_le leftResidual rightResidual
    sample.retained.inverse.bound_small
  simp only [← Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- The cached signed primitive differentiates to the signed shared inverse.

The reciprocal differential supplies the retained monomial factor. The same
initial comparison bit negates both the primitive and inverse in the flipped branch. -/
theorem primitive_derivative (alignment : RegularAlignment
  sample) (point : Gaussian) :
    (Derivative.derivative alignment.primitive).eval point =
      -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
        (if alignment.first.flip then -capSample.inverse.value.eval point else capSample.inverse.value.eval point) := by
  have canonical : (Derivative.derivative capSample.primitive.value).eval point =
      -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) * capSample.inverse.value.eval
        point := by
    rw [← GCD.derivative, capSample.primitive.derivative_eq, capSample.coefficient_eq, capSample.pulledInverse_eq]
    simp only [Primitives.coefficient, Primitives.point, Primitives.degree,
      alignment.regular_chart, Nat.zero_add, Nat.one_mul, Nat.cast_one, pow_one, -eq_self, -iff_self]
    ring1
  rw [alignment.primitive_eq]
  cases alignment.first.flip
  · exact canonical
  · change (Derivative.derivative (-capSample.primitive.value)).eval point =
      -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
        (-capSample.inverse.value.eval point)
    rw [Derivative.eval_derivative_neg, canonical]
    ring1

/-- This consumes the original cap-comparison coefficient, including its reciprocal orientation. The signed primitive
comes from the shared bank. -/
theorem coefficient_distance_le (alignment : RegularAlignment
  sample) (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Norm.Basic.normSq (sample.pullback.coefficient.eval (parent.edge.point parameter)⁻¹ -
      (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹) ≤
      6 * (sample.retained.inverse.bound + quarterRadius (1 / 256) index) *
        Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹) :=
          by
  have inside := ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩)
  have power : Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^
    (HyperellipticReciprocal.reversedDifferential differential).exponent) ≤ 1 := by
    rw [Power.normSq_pow]
    exact (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _)
      (Reciprocal.Bounds.disk_unit_bound inside) _).trans_eq
      (_root_.one_pow _)
  rw [sample.pullback.coefficient_eq, sample.inverse_eq, alignment.primitive_derivative]
  change Norm.Basic.normSq (-((parent.edge.point parameter)⁻¹ ^
    (HyperellipticReciprocal.reversedDifferential differential).exponent *
      sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹) -
      -((parent.edge.point parameter)⁻¹ ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
        (alignment.atPoint parameter between).value) ≤ _
  rw [show -((parent.edge.point parameter)⁻¹ ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
      sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹) -
      -((parent.edge.point parameter)⁻¹ ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
        (alignment.atPoint parameter between).value =
      -((parent.edge.point parameter)⁻¹ ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) *
        (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ - (alignment.atPoint parameter
          between).value) by ring1,
    Norm.Basic.normSq_mul, Norm.Basic.normSq_neg]
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct power (Norm.Basic.normSq_nonneg
    _)).trans
    ((Fraction.Field.one_mul _).trans_le (alignment.distance_le parameter between))

/-- The retained local cap polynomial and the signed shared primitive have a paid derivative discrepancy on the full
actual inverse arc. -/
theorem derivative_distance_le (alignment : RegularAlignment
  sample) (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Norm.Basic.normSq ((Derivative.derivative sample.pullback.value).eval (parent.edge.point
      parameter)⁻¹ -
      (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹) ≤
      2 * (quarterRadius comparison.disk.scale index +
        6 * (sample.retained.inverse.bound + quarterRadius (1 / 256) index) *
          Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹))
            :=
  (Norm.Bounds.normSq_sub_le_via _ _ _).trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (sample.derivative_error parameter between)
      (alignment.coefficient_distance_le parameter between)) (by decide))

/-- All constants are from the retained geometric preparation. The signed shared primitive therefore admits the same
geometric request schedule as the original local cap comparison, independently of the fine subdivision. -/
theorem derivative_error (alignment : RegularAlignment
  sample) (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Norm.Basic.normSq ((Derivative.derivative sample.pullback.value).eval (parent.edge.point
      parameter)⁻¹ -
      (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹) ≤
      quarterRadius
        (2 * (comparison.disk.scale + 6 * (cell.model.bound + 1 / 256) * comparison.disk.inverseUpper)) index := by
  have boundary := data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have lower := (collar.point_clearance boundary (show (0 : Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl,
    by decide⟩)).2
  rw [collar.point_eq, ReciprocalExteriorCollar.deform_zero] at lower
  have inverseBound : Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point
    parameter)⁻¹) ≤ comparison.disk.inverseUpper := by
    rw [comparison.disk.inverseUpper_eq]
    exact RegularBounds.inverse_le sample.retained.inverse (cell.contains parameter between)
      collar.radicandBound_positive lower
  have factorNonnegative : 0 ≤ 6 * (sample.retained.inverse.bound + quarterRadius (1 / 256) index) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg sample.retained.inverse.bound_nonnegative
        (quarterRadius_nonneg (by decide +kernel) index))
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound factorNonnegative
  have bounded := (alignment.derivative_distance_le parameter between).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct le_rfl
      paid) (by decide))
  have boundEq : sample.retained.inverse.bound = quarterRadius cell.model.bound index := by
    rw [sample.retained.inverse_eq, sample.cell_eq, Model.refine_bound]
  apply bounded.trans_eq
  rw [boundEq]
  simp only [quarterRadius_eq_mul_pow]
  ring1

/-- The cell's sign relative to the shared regular model is determined by its retained parent source polynomial. Two
ordinary preparation stages suffice for the finite sign-composition law. -/
theorem source_flip (alignment : RegularAlignment sample)
  (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) (later : 2 ≤ index) :
    (SignAlignment.build ((data.source.refine index).value.eval (parent.edge.point parameter))
      (ReciprocalRootNames.factor genus (parent.edge.point parameter) *
        capSample.inverse.value.eval (parent.edge.point parameter)⁻¹)).flip = alignment.first.flip := by
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside
  let source := (data.source.refine index).value.eval (parent.edge.point parameter)
  let factor := ReciprocalRootNames.factor genus (parent.edge.point parameter)
  let transported := factor * sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹
  let shared := factor * capSample.inverse.value.eval (parent.edge.point parameter)⁻¹
  have modelEq : sample.retained.inverse = cell.model.refine index := by
    rw [sample.retained.inverse_eq, sample.cell_eq]
  have sourceResidual : Norm.Basic.normSq (1 - curve.polynomial.eval (parent.edge.point
    parameter) * source ^ 2) ≤
      (data.source.refine index).bound := by
    rw [← (data.source.refine index).residual_eq, Norm.Basic.normSq_eq_canonical]
    exact (data.source.refine index).residualBound _ (data.source_inside inside)
  have localResidual : Norm.Basic.normSq (1 - curve.polynomial.eval (parent.edge.point parameter)
    * transported ^ 2) ≤
      sample.retained.inverse.bound :=
    ReciprocalInverseModelOverlap.residual sample.retained.inverse nonzero (cell.contains parameter between)
  have sharedResidual : Norm.Basic.normSq (1 - curve.polynomial.eval (parent.edge.point
    parameter) * shared ^ 2) ≤
      quarterRadius (1 / 256) index := by
    have identity : 1 - curve.polynomial.eval (parent.edge.point parameter) * shared ^ 2 =
        1 - (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹ *
          (capSample.inverse.value.eval (parent.edge.point parameter)⁻¹) ^ 2 := by
      rw [← ReciprocalRootNames.factor_identity curve _ nonzero]
      dsimp only [shared, factor]
      ring1
    rw [identity]
    exact regular_residual alignment.regular_chart
      (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point inside))
  have localSmall : sample.retained.inverse.bound ≤ 1 / 256 := by
    rw [modelEq]
    exact later_small cell.model later
  have sharedSmall : quarterRadius (1 / 256) index ≤ (1 / 256 : Coordinate) :=
    quarterRadius_le_scale (by decide +kernel) index
  have sourceLocal : (SignAlignment.build source transported).flip = false := by
    dsimp only [source, transported, factor]
    rw [modelEq]
    exact cell.flip_false index parameter between
  rw [Norm.Basic.normSq_eq_canonical] at sourceResidual localResidual sharedResidual
  have composed := SignAlignment.cocycle (SignAlignment.build source transported)
    (scaledAlignment factor
      (alignment.atPoint parameter between)) (SignAlignment.build source shared)
    sourceResidual localResidual sharedResidual
      (later_small data.source later)
      localSmall sharedSmall
  rw [sourceLocal] at composed
  exact composed

/-- Every adjacent cell of this same prepared parent uses one common sign for the shared cap primitive, including
nonuniform later sample cuts. -/
theorem same_parent {otherEdge : ParameterEdge}
    {otherCell : Cell data otherEdge} {otherComparison : Data regular otherCell}
    {otherSample : Sample otherComparison capSample}
    (first : RegularAlignment sample) (last :
      RegularAlignment otherSample) (parameter :
      Coordinate)
    (firstInside : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter)
    (lastInside : otherEdge.left.parameter ≤ parameter ∧ parameter ≤ otherEdge.right.parameter) (later : 2 ≤ index) :
    first.first.flip = last.first.flip :=
  (first.source_flip parameter firstInside later).symm.trans (last.source_flip parameter lastInside later)

end RegularAlignment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment

end
