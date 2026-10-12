module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine

public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Sample-independent primitive controls on a common model edge

One cached slope and mismatch allowance serve both indexed generated traces
and the actual recursively refined mesh boundary.  Their proofs hold at all
queried rational parameters; choosing a subdivision is not part of the data.
-/

namespace Purelib.Riemann.Integration

open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
open Purelib.Data in
/-- Cached slope and drift bounds for two anchored primitives on a common model edge.

The coefficient identities link both primitives to the same numerator and their inverse-root models. The retained scalar
bounds apply throughout the edge independently of any subdivision. -/
structure PrimitiveEdgeControl {polynomial numerator leftCoefficient rightCoefficient : Polynomial}
    {leftBox rightBox : Box} {clearance : RegionClearance polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator) {left : Model polynomial leftBox} {right : Model polynomial
      rightBox}
    {start finish : Gaussian} (edge : EdgeTransition left right start finish)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value) where
  /-- The left coefficient is the numerator times the left inverse-root model. -/ leftCoefficient_eq : ∀ point,
    leftCoefficient.eval point = numerator.eval point * left.value.eval point
  /-- The right coefficient is the numerator times the right inverse-root model. -/ rightCoefficient_eq : ∀ point,
    rightCoefficient.eval point = numerator.eval point * right.value.eval point
  /-- The cached coefficient and squared-edge-length bound for increments. -/ slope : Rat.Fraction.Rational
  /-- The slope is twice the numerator and inverse bounds times squared edge length. -/ slope_eq : slope = 2 *
    (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
  /-- The cached discrepancy bound for the two aligned primitives. -/ drift : Rat.Fraction.Rational
  /-- The drift retains twelve times the summed model errors, coefficient bound and squared edge length. -/ drift_eq :
    drift = 12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)

constructive_injectivity PrimitiveEdgeControl

namespace PrimitiveEdgeControl

variable {polynomial numerator leftCoefficient rightCoefficient : Polynomial} {leftBox rightBox : Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {edge : EdgeTransition left right start finish} {leftPrimitive : DensePrimitive leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox} {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value
      rightPrimitive.value}

/-- Cache the exact slope and drift expressions for the anchored edge.

Retain both supplied coefficient identities with the same models, primitives and anchor. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator) (edge : EdgeTransition left right start finish)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = numerator.eval point * left.value.eval point)
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = numerator.eval point * right.value.eval point) :
    PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor :=
  { leftCoefficient_eq := leftCoefficient_eq
    rightCoefficient_eq := rightCoefficient_eq
    slope := 2 * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
    slope_eq := rfl
    drift := 12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
    drift_eq := rfl }

open Purelib.Data in
/-- The cached primitive discrepancy bound is nonnegative. -/
theorem drift_nonnegative (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) : 0 ≤
  control.drift := by
  rw [control.drift_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative
        right.bound_nonnegative))
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative
        bounds.inverseUpper_positive.le)) (Gaussian.Basic.Canonical.normSq_nonneg _)

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Geometry in
/-- Bound the aligned primitive discrepancy at any parameter in the unit interval by the cached drift. -/
theorem error_bound (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor)
    {parameter : Rat.Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (anchor.alignedValue (Rational.Affine.line start (finish - start) parameter) -
      leftPrimitive.value.eval (Rational.Affine.line start (finish - start) parameter)) ≤ control.drift := by
  have swap (first last : Gaussian) : normSq (first - last) = normSq (last - first) := by
    rw [show first - last = -(last - first) by ring1, Gaussian.Basic.Canonical.normSq_neg]
  rw [swap]
  have estimate := anchor.drift_le bounds leftPrimitive rightPrimitive control.leftCoefficient_eq
    control.rightCoefficient_eq inside
  have distance := Rational.Affine.normSq_line_sub start (finish - start) parameter 0
  rw [Normalization.InverseModelEdgeTransition.line_zero, Gaussian.Norm.Basic.normSq_eq_canonical,
    Gaussian.Norm.Basic.normSq_eq_canonical] at distance
  rw [distance] at estimate
  have square : (parameter - 0) ^ 2 ≤ (1 : Rat.Fraction.Rational) := by
    have scalarZero : parameter - 0 = parameter := by ring1
    simpa only [scalarZero, one_pow] using Rat.Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
  calc
    _ ≤ _ := estimate
    _ = control.drift * (parameter - 0) ^ 2 := by rw [control.drift_eq]; ring1
    _ ≤ control.drift * 1 := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
      control.drift_nonnegative
    _ = control.drift := Rat.Fraction.Field.mul_one_direct _

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Bound the left primitive's increment by cached slope times squared parameter displacement.

Both parameters must lie in the unit interval of the retained model edge. -/
theorem right_increment_bound (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor)
    {first last : Rat.Fraction.Rational} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq (leftPrimitive.value.eval (Rational.Affine.line start (finish - start) last) -
      leftPrimitive.value.eval (Rational.Affine.line start (finish - start) first)) ≤ control.slope * (last - first) ^ 2
        := by
  rw [control.slope_eq]
  have scalar := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le leftPrimitive start (finish
    - start) (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds)
    (fun _ inside => edge.left_contains_at inside) (bounds.numeratorUpper * bounds.inverseUpper)
    (fun parameter inside => by
      rw [control.leftCoefficient_eq]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bounds.numerator_inverse_le left (edge.left_contains_at
        inside)) lastInside firstInside
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Geometry in
/-- Bound the increment of aligned primitive discrepancy by cached drift times squared parameter displacement.

The two unit-interval parameters use the same anchored primitives and signed edge transition. -/
theorem drift_increment_bound (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor)
    {first last : Rat.Fraction.Rational} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((anchor.alignedValue (Rational.Affine.line start (finish - start) last) -
        leftPrimitive.value.eval (Rational.Affine.line start (finish - start) last)) -
      (anchor.alignedValue (Rational.Affine.line start (finish - start) first) -
        leftPrimitive.value.eval (Rational.Affine.line start (finish - start) first))) ≤ control.drift * (last - first)
          ^ 2 := by
  let firstPoint := Rational.Affine.line start (finish - start) first
  let lastPoint := Rational.Affine.line start (finish - start) last
  have identity : (anchor.alignedValue lastPoint - leftPrimitive.value.eval lastPoint) -
      (anchor.alignedValue firstPoint - leftPrimitive.value.eval firstPoint) =
        -((leftPrimitive.value.eval lastPoint - leftPrimitive.value.eval firstPoint) -
          edge.sign * (rightPrimitive.value.eval lastPoint - rightPrimitive.value.eval firstPoint)) := by
    unfold PrimitiveEdgeAnchor.alignedValue
    ring1
  rw [identity, Gaussian.Basic.Canonical.normSq_neg, control.drift_eq]
  exact Comparison.PrimitiveEdgeComparison.EdgeTransition.primitive_increment_le edge bounds leftPrimitive
    rightPrimitive control.leftCoefficient_eq control.rightCoefficient_eq lastInside firstInside

end PrimitiveEdgeControl

end Purelib.Riemann.Integration
