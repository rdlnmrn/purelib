module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# Requested whole-segment cap primitive comparison

The fixed derivative-error scale controls the complete increment of the
cap comparison polynomial against any retained primitive of the reciprocal
coefficient. Finite subdivision removes the Taylor terms. Both endpoint
memberships, the displacement, the error scale and the requested stage are
retained with their certificates; later stages share the same budget.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box
open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Model)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ComparisonBounds (Bounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback (Preparation Sample)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Geometry.Rational.Affine (line)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {localBox :
    Purelib.Geometry.Rational.Box}
  {initial : Model
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) localBox}
  {preparation : Preparation cap initial}
  {clearance : RegionClearance
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) localBox} {differential :
    Differential genus}

/-- Reuse a cached polynomial value and its global derivative identity. The new Taylor ceiling is proof-local and
disappears from execution. -/
private def onBox {coefficient : InverseRootPolynomial.Polynomial} {sourceBox : Rational.Box}
    (primitive : Certificate.DensePrimitive coefficient sourceBox) (box : Rational.Box) :
      Certificate.DensePrimitive coefficient box :=
  { value := primitive.value
    derivative_eq := primitive.derivative_eq
    remainderBound := Taylor.denseTaylorRemainderBound primitive.value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside => by
      have estimate := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
        primitive.value lastInside firstInside
      rw [primitive.derivative_eq] at estimate
      exact estimate }

/-- Retain the supplied polynomial as its derivative's primitive with a certified Taylor ceiling on the original box. -/
private def ofValue (value : InverseRootPolynomial.Polynomial) (box : Rational.Box) :
  Certificate.DensePrimitive (GCD.derivative value) box :=
  { value := value
    derivative_eq := fun _ => rfl
    remainderBound := Taylor.denseTaylorRemainderBound value box
    remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
    increment_bound := fun firstInside lastInside =>
      Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound value lastInside firstInside }

set_option genInjectivity false in
/-- The retained whole segment in the common reciprocal and cap domain.

Both endpoint memberships, the exact displacement and the original comparison scale are cached for all later primitive
stages. -/
structure Segment (bounds : ComparisonBounds.Bounds preparation clearance differential) where
  /-- The original first endpoint of the retained comparison segment. -/ first : InverseRootPolynomial.Gaussian
  /-- The original last endpoint of the retained comparison segment. -/ last : InverseRootPolynomial.Gaussian
  /-- The original first endpoint lies in the local reciprocal model box. -/ firstLocal : localBox.Contains first
  /-- The original last endpoint lies in the local reciprocal model box. -/ lastLocal : localBox.Contains last
  /-- The original first endpoint lies in the retained cap box. -/ firstCap : collar.box.Contains first
  /-- The original last endpoint lies in the retained cap box. -/ lastCap : collar.box.Contains last
  /-- The cached displacement between the original segment endpoints. -/ direction : InverseRootPolynomial.Gaussian
  /-- The retained direction is exactly the last endpoint minus the first. -/ direction_eq : direction = last - first
  /-- The retained whole-segment comparison error scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale is twice the original derivative-error scale times the retained displacement squared norm. -/ scale_eq :
    scale = 2 * bounds.scale * Data.Gaussian.Norm.Basic.normSq direction

constructive_injectivity Segment

namespace Segment

/-- Cache the original segment endpoints, common-domain memberships, exact displacement and comparison scale. -/
@[expose] public def build (bounds : ComparisonBounds.Bounds preparation clearance differential) (first last :
  InverseRootPolynomial.Gaussian)
    (firstLocal : localBox.Contains first) (lastLocal : localBox.Contains last)
    (firstCap : collar.box.Contains first) (lastCap : collar.box.Contains last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds :=
  let direction := last - first
  ⟨first, last, firstLocal, lastLocal, firstCap, lastCap, direction, rfl, 2 * bounds.scale *
    Data.Gaussian.Norm.Basic.normSq direction, rfl⟩

variable {bounds : Bounds preparation clearance
  differential}

/-- The retained whole-segment comparison scale is nonnegative. -/
theorem scale_nonnegative (segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds) : 0 ≤
  segment.scale := by
  rw [segment.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.scale_nonnegative)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)

/-- Compare with the retained reciprocal primitive, including its original constant. Only the difference of endpoint
values removes that constant. -/
theorem comparison_le (segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds) {index :
  Nat} {box rightBox : Rational.Box}
    {capSample : Primitives.Sample cap differential index box} (sample : PolynomialPullback.Sample preparation
      capSample)
    {coefficient : InverseRootPolynomial.Polynomial} (right : Certificate.DensePrimitive coefficient rightBox)
    (coefficient_eq : ∀ point, coefficient.eval point = sample.coefficient.eval point) :
    Data.Gaussian.Norm.Basic.normSq ((sample.value.eval segment.last - sample.value.eval segment.first) -
      (right.value.eval segment.last - right.value.eval segment.first)) ≤ Geometric.Basic.quarterRadius segment.scale
        index := by
  let left := Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.ofValue sample.value localBox
  let rightOnBox := Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.onBox right localBox
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  have localInside (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      localBox.Contains (Affine.line segment.first segment.direction parameter) := by
    rw [segment.direction_eq]
    exact Rational.Box.contains_line segment.firstLocal segment.lastLocal inside
  have capInside (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      collar.box.Contains (Affine.line segment.first segment.direction parameter) := by
    rw [segment.direction_eq]
    exact Rational.Box.contains_line segment.firstCap segment.lastCap inside
  have coefficientBound (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq ((GCD.derivative sample.value).eval (Affine.line segment.first
        segment.direction parameter) -
        1 * coefficient.eval (Affine.line segment.first segment.direction parameter)) ≤ Geometric.Basic.quarterRadius
          bounds.scale index := by
    rw [Data.Gaussian.Basic.one_mul, coefficient_eq]
    exact bounds.derivative_error_le sample (localInside parameter inside) (capInside parameter inside)
  have estimate := Segment.Comparison.DensePrimitive.difference_increment_le left rightOnBox 1 segment.first
    segment.direction (by decide) interval
    localInside localInside (Geometric.Basic.quarterRadius bounds.scale index) coefficientBound
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have first_eq : Affine.line segment.first segment.direction 0 = segment.first := by
    change segment.first + 0 * segment.direction = segment.first
    rw [Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.add_zero]
  have last_eq : Affine.line segment.first segment.direction 1 = segment.last := by
    change segment.first + 1 * segment.direction = segment.last
    rw [segment.direction_eq]
    ring1
  change Data.Gaussian.Norm.Basic.normSq ((sample.value.eval (Affine.line segment.first segment.direction 1) -
      sample.value.eval (Affine.line segment.first segment.direction 0)) -
      1 * (right.value.eval (Affine.line segment.first segment.direction 1) - right.value.eval (Affine.line
        segment.first segment.direction 0))) ≤ _ at estimate
  rw [first_eq, last_eq, Data.Gaussian.Basic.one_mul] at estimate
  exact estimate.trans_eq (by
    rw [show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 by decide, _root_.one_pow, Fraction.Field.mul_one_direct,
      Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, segment.scale_eq]
    ring1)

set_option genInjectivity false in
/-- A retained finite comparison stage above the original floor with its certified geometric error below the requested
target. -/
structure Request (segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds) (target :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained finite stage selected for the original segment request. -/ index : Nat
  /-- The selected stage is exactly the first quarter-radius search result from the retained scale, floor and target. -/
    index_eq : index = Search.firstQuarterBelow segment.scale floor target
  /-- The retained selected stage is at least the original requested floor. -/ floor_le : floor ≤ index
  /-- The cached comparison error at the retained selected stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The cached error equals the quarter-radius of the original segment scale at the selected stage. -/ error_eq :
    error = Geometric.Basic.quarterRadius segment.scale index
  /-- The retained comparison error is strictly below the original requested target. -/ error_lt : error < target

constructive_injectivity Request

namespace Request

/-- Select and retain the first geometric comparison stage meeting the positive target above the original floor. -/
@[expose] public def build (segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds)
  (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment.Request segment target floor :=
  let index := Search.firstQuarterBelow segment.scale floor target
  ⟨index, rfl, Search.firstQuarterBelow_ge _ _ _, Geometric.Basic.quarterRadius segment.scale index, rfl,
    Search.firstQuarterBelow_accurate _ segment.scale_nonnegative _ _ positive⟩

/-- Every later retained cap stage satisfies the original whole-segment primitive comparison target. -/
theorem accurate {segment : Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment bounds} {target :
  InverseRootPolynomial.Coordinate} {floor : Nat} (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison.Segment.Request segment target floor)
    {index : Nat} {box rightBox : Rational.Box} {capSample : Primitives.Sample cap differential index
      box}
    (sample : PolynomialPullback.Sample preparation capSample) {coefficient : InverseRootPolynomial.Polynomial} (right :
      Certificate.DensePrimitive coefficient rightBox)
    (coefficient_eq : ∀ point, coefficient.eval point = sample.coefficient.eval point) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq ((sample.value.eval segment.last - sample.value.eval segment.first) -
      (right.value.eval segment.last - right.value.eval segment.first)) < target :=
  ((segment.comparison_le sample right coefficient_eq).trans
    ((quarterRadius_antitone segment.scale_nonnegative later).trans_eq request.error_eq.symm)).trans_lt
      request.error_lt

end Request
end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
