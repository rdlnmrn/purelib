module
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
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

/-!
# Requested comparison with the signed shared regular-cap primitive

The retained source polynomial is compared directly with the signed shared
cap polynomial along the actual inverse source arc. Its squared parameter
width is retained for aggregation over the prepared subdivision.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {sample : Sample comparison capSample}

namespace Data

/-- The fixed derivative discrepancy scale between the original local cap polynomial and its retained signed shared
primitive. -/
@[expose] def regularDerivativeScale (comparison : ArcSamples.Data regular cell) : Coordinate :=
  2 * (comparison.disk.scale + 6 * (cell.model.bound + 1 / 256) * comparison.disk.inverseUpper)

/-- Combine the original source-to-local and local-to-shared derivative scales for the retained inverse arc. -/
@[expose] def regularCoefficientScale (comparison : ArcSamples.Data regular cell) : Coordinate :=
  2 * (2 * (comparison.sourceScale + comparison.disk.scale) +
    (regularDerivativeScale comparison))

/-- Multiply the retained coefficient discrepancy scale by twice the original source parent squared displacement. -/
@[expose] def regularScale (comparison : ArcSamples.Data regular cell) : Coordinate :=
  2 * (regularCoefficientScale comparison) *
    Data.Gaussian.Norm.Basic.normSq parent.model.displacement

/-- The original residual, inverse and displacement bounds make the retained regular comparison scale nonnegative. -/
theorem regularScale_nonnegative (comparison : ArcSamples.Data regular cell) : 0 ≤
  (regularScale comparison) := by
  have derivativeNonnegative : 0 ≤
    (regularDerivativeScale comparison) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg comparison.disk.scale_nonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg cell.model.bound_nonnegative (by decide +kernel))) comparison.disk.inverseUpper_positive.le))
  have coefficientNonnegative : 0 ≤
    (regularCoefficientScale comparison) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg comparison.sourceScale_nonnegative comparison.disk.scale_nonnegative)) derivativeNonnegative)
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)

end Data

namespace RegularAlignment

/-- The original source coefficient and signed shared cap derivative satisfy the retained geometric discrepancy on every
actual inverse-arc point. -/
theorem source_coefficient_error (alignment : SheetAlignment.RegularAlignment sample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index)
    (parameter : InverseRootPolynomial.Coordinate) (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) + (parent.edge.point
      parameter)⁻¹ ^ 2 *
      (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹) ≤
        Geometric.Basic.quarterRadius
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularCoefficientScale comparison) index
          := by
  have before := ArcComparison.Sample.coefficient_error sample source parameter between
  have after := alignment.derivative_error parameter between
  have inverseInside := ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩)
  have multiplier : Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^ 2) ≤ 1 := by
    rw [Power.normSq_pow]
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Reciprocal.Bounds.disk_unit_bound inverseInside) 2).trans_eq (_root_.one_pow _)
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct after
    (Data.Gaussian.Norm.Basic.normSq_nonneg ((parent.edge.point parameter)⁻¹ ^ 2))
  have derivativeNonnegative : 0 ≤
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularDerivativeScale comparison) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg comparison.disk.scale_nonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg cell.model.bound_nonnegative (by decide +kernel))) comparison.disk.inverseUpper_positive.le))
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct multiplier
    (Geometric.Basic.quarterRadius_nonneg derivativeNonnegative index)
  rw [Fraction.Field.one_mul] at paid
  have tail := weighted.trans paid
  rw [← Data.Gaussian.Norm.Basic.normSq_mul] at tail
  have identity : source.coefficient.eval (parent.edge.point parameter) + (parent.edge.point parameter)⁻¹ ^ 2 *
      (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹ =
      (source.coefficient.eval (parent.edge.point parameter) + (parent.edge.point parameter)⁻¹ ^ 2 *
        (Derivative.derivative sample.pullback.value).eval (parent.edge.point parameter)⁻¹) -
      (parent.edge.point parameter)⁻¹ ^ 2 *
        ((Derivative.derivative sample.pullback.value).eval (parent.edge.point parameter)⁻¹ -
          (Derivative.derivative alignment.primitive).eval (parent.edge.point parameter)⁻¹) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct before tail) (by decide)).trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularCoefficientScale,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularDerivativeScale, -eq_self, -iff_self]
      ring1))

/-- Subtract the retained signed shared primitive at the actual inverse point from the original source primitive. -/
@[expose] def comparisonValue (alignment : SheetAlignment.RegularAlignment sample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index) (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  source.primitive.value.eval (parent.edge.point parameter) - alignment.primitive.eval (parent.edge.point parameter)⁻¹

/-- Certify the supplied original polynomial as a primitive of its derivative on a finite box using the exact Taylor
remainder bound. -/
private def ofValue (value : InverseRootPolynomial.Polynomial) (box : Rational.Box) :
    Certificate.DensePrimitive (GCD.derivative value) box :=
  { value := value
    derivative_eq := fun _ => rfl
    remainderBound := Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside =>
      Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside firstInside }

/-- The same signed polynomial controls every subinterval of the actual prepared cell. The finite inverse-path
substitution retains both endpoints. -/
theorem comparison_error (alignment : SheetAlignment.RegularAlignment sample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      (comparisonValue alignment source
      last - comparisonValue alignment
      source first) ≤
      Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale
        comparison) index * (last - first) ^ 2 := by
  let interval : Data.Rat.Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, cell.ordered.le⟩
  have within (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  let right := ofValue
    (-alignment.primitive) (data.box edge.left.parameter)
  have coefficientBound (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 *
        (GCD.derivative (-alignment.primitive)).eval (parent.edge.point parameter)⁻¹) ≤
          Geometric.Basic.quarterRadius
            (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularCoefficientScale comparison)
            index := by
    have signed (first second : InverseRootPolynomial.Gaussian) : first - (-second) = first + second := by ring1
    rw [GCD.derivative, Derivative.eval_derivative_neg, Algebra.Ring.Multiplication.mul_neg, signed]
    exact source_coefficient_error
      alignment source parameter inside
  have estimate := Comparison.increment_difference_le data.boundary interval within
    source.primitive right (fun parameter inside => data.source_inside (within parameter inside)) cell.contains
    (Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularCoefficientScale comparison) index)
      coefficientBound firstInside lastInside
  have values (parameter : InverseRootPolynomial.Coordinate) :
      Comparison.comparisonValue parent source.primitive right parameter =
        comparisonValue alignment source
          parameter := by
    change source.primitive.value.eval (parent.edge.point parameter) + (-alignment.primitive).eval (parent.edge.point
      parameter)⁻¹ = _
    rw [DensePolynomial.eval_neg]
    rfl
  rw [values last, values first] at estimate
  exact estimate.trans_eq (by simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.Data.regularScale, -eq_self, -iff_self]; ring1)

end RegularAlignment

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
