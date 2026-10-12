module
import Purelib.Algebra.Ring.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
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
# Requested source-to-cap comparison along actual inverted arcs

Finite rational-path substitution compares the retained source primitive
to the shared cap comparison polynomial on each covered reciprocal cell.
The bound retains the squared source-parameter width, which is needed to
sum over a refining mesh. No inverse arc is replaced by an endpoint chord.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
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

/-- Combine source-to-reciprocal and cap derivative discrepancies when the retained multiplier has squared norm at most
one. -/
private theorem combine {source reciprocal derivative multiplier : InverseRootPolynomial.Gaussian} {first second :
  InverseRootPolynomial.Coordinate}
    (sourceBound : Data.Gaussian.Norm.Basic.normSq (source - multiplier * reciprocal) ≤ first)
    (capBound : Data.Gaussian.Norm.Basic.normSq (derivative + reciprocal) ≤ second) (multiplierBound :
      Data.Gaussian.Norm.Basic.normSq multiplier ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (source + multiplier * derivative) ≤ 2 * (first + second) := by
  have tail := Fraction.Order.Arithmetic.mul_le_mul_direct multiplierBound capBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  rw [Fraction.Field.one_mul, ← Data.Gaussian.Norm.Basic.normSq_mul] at tail
  rw [show source + multiplier * derivative = (source - multiplier * reciprocal) + multiplier * (derivative +
    reciprocal) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add sourceBound tail) (by decide))

namespace Sample

/-- Bound the actual source coefficient and inverse-arc cap derivative discrepancy by their retained geometric scales.
-/
theorem coefficient_error (sample : ArcSamples.Sample comparison capSample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index) (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) + (parent.edge.point
      parameter)⁻¹ ^ 2 *
      (Derivative.derivative sample.pullback.value).eval (parent.edge.point parameter)⁻¹) ≤
      Geometric.Basic.quarterRadius (2 * (comparison.sourceScale + comparison.disk.scale)) index := by
  have boundary := data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have inverseInside := ReciprocalExteriorCollar.inverse_inDisk curve boundary
  have multiplier : Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^ 2) ≤ 1 := by
    rw [Power.normSq_pow]
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Reciprocal.Bounds.disk_unit_bound inverseInside) 2).trans_eq (_root_.one_pow _)
  have capBound := ArcSamples.Sample.derivative_error sample parameter between
  rewrite [ArcSamples.Sample.coefficient_eq sample, Data.Gaussian.Basic.Canonical.sub_eq_add_neg, neg_neg] at capBound
  exact (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison.combine (ArcSamples.Sample.source_error sample source
    parameter between) capBound multiplier).trans_eq
    (by simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]; ring1)

/-- Subtract the retained cap polynomial at the actual inverse point from the original source primitive value. -/
@[expose] def comparisonValue (sample : ArcSamples.Sample comparison capSample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index) (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  source.primitive.value.eval (parent.edge.point parameter) - sample.pullback.value.eval (parent.edge.point parameter)⁻¹

/-- This auxiliary Taylor certificate is used only inside the finite substitution proof; execution retains the supplied
comparison polynomial. -/
private def ofValue (value : InverseRootPolynomial.Polynomial) (box : Rational.Box) :
    Certificate.DensePrimitive (GCD.derivative value) box :=
  { value := value
    derivative_eq := fun _ => rfl
    remainderBound := Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside =>
      Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside firstInside }

/-- The same estimate holds on every subinterval of the retained cell. Both primitive values are taken at actual source
and inverse-source points. -/
theorem comparison_error (sample : ArcSamples.Sample comparison capSample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      (comparisonValue sample source last -
      comparisonValue sample source first) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (last - first) ^ 2 := by
  let interval : Data.Rat.Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, cell.ordered.le⟩
  have within (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  let right := ofValue (-sample.pullback.value)
    (data.box edge.left.parameter)
  have coefficientBound (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) -
        (parent.edge.point parameter)⁻¹ ^ 2 *
        (GCD.derivative (-sample.pullback.value)).eval (parent.edge.point parameter)⁻¹) ≤
        Geometric.Basic.quarterRadius (2 * (comparison.sourceScale + comparison.disk.scale)) index := by
    rewrite [GCD.derivative, Derivative.eval_derivative_neg, Algebra.Ring.Multiplication.mul_neg,
      Data.Gaussian.Basic.Canonical.sub_eq_add_neg, neg_neg]
    exact coefficient_error sample source parameter
      inside
  have estimate := Comparison.increment_difference_le data.boundary interval within
    source.primitive right (fun parameter inside => data.source_inside (within parameter inside)) cell.contains
    (Geometric.Basic.quarterRadius (2 * (comparison.sourceScale + comparison.disk.scale)) index) coefficientBound
      firstInside lastInside
  have values (parameter : InverseRootPolynomial.Coordinate) :
      Comparison.comparisonValue parent source.primitive right parameter =
        comparisonValue sample source parameter := by
    change source.primitive.value.eval (parent.edge.point parameter) +
      (-sample.pullback.value).eval (parent.edge.point parameter)⁻¹ = _
    rw [DensePolynomial.eval_neg]
    rfl
  rw [values last, values first] at estimate
  exact estimate.trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, comparison.scale_eq, -eq_self, -iff_self];
      ring1)

/-- The cached endpoint increment has the same geometric error, with the squared cell width retained for subsequent mesh
aggregation. -/
theorem increment_error (sample : ArcSamples.Sample comparison capSample) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index) :
    Data.Gaussian.Norm.Basic.normSq (source.increment edge - sample.increment) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have identity : source.increment edge - sample.increment =
      comparisonValue sample source
        edge.right.parameter - comparisonValue sample
        source edge.left.parameter := by
    rw [SourcePrimitive.increment, sample.increment_eq, sample.firstValue_eq, sample.lastValue_eq]
    dsimp only [comparisonValue]
    ring1
  rw [identity]
  exact comparison_error sample source ⟨le_rfl,
    cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩

end Sample

set_option genInjectivity false in
/-- A computed common model stage paying an original inverse-arc comparison target.

The retained stage respects the caller's floor and caches its exact geometric error; subsequent estimates retain the
actual squared cell width. -/
structure Request (comparison : ArcSamples.Data regular cell) (target : InverseRootPolynomial.Coordinate) (floor : Nat)
  where
  /-- The cached common polynomial comparison stage. -/ index : Nat
  /-- The stage is the first geometric quarter-radius search result above the original floor. -/ index_eq : index =
    Search.firstQuarterBelow comparison.scale floor target
  /-- The retained common stage respects the original caller floor. -/ floor_le : floor ≤ index
  /-- The cached geometric comparison error at the retained stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The cached error is exactly the original comparison scale's quarter-radius at that stage. -/ error_eq : error =
    Geometric.Basic.quarterRadius comparison.scale index
  /-- The cached comparison error is strictly below the original target. -/ error_lt : error < target

constructive_injectivity Request

namespace Request

/-- Search for a common stage paying the original reciprocal comparison target and retain its exact geometric error. -/
@[expose] def build (comparison : ArcSamples.Data regular cell) (target : InverseRootPolynomial.Coordinate) (positive :
  0 < target) (floor : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison.Request comparison target floor
  :=
  let index := Search.firstQuarterBelow comparison.scale floor target
  ⟨index, rfl, Search.firstQuarterBelow_ge _ _ _, Geometric.Basic.quarterRadius comparison.scale index, rfl,
    Search.firstQuarterBelow_accurate _ comparison.scale_nonnegative _ _ positive⟩

/-- A computed stage works for the actual supplied source and reciprocal samples at every later common refinement; the
cell-width factor is paid. -/
theorem accurate {target : InverseRootPolynomial.Coordinate} {floor : Nat} (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison.Request comparison target floor)
    (sample : ArcSamples.Sample comparison capSample) (source : UniformReciprocalPrimitives.SourcePrimitive data index)
      (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (source.increment edge - sample.increment) < target * (edge.right.parameter
      - edge.left.parameter) ^ 2 := by
  have widthPositive : 0 < (edge.right.parameter - edge.left.parameter) ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct cell.ordered) 2
  have laterError := (quarterRadius_antitone comparison.scale_nonnegative later).trans_eq
    request.error_eq.symm
  exact ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison.Sample.increment_error sample source).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct laterError widthPositive.le)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct request.error_lt widthPositive)

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison
