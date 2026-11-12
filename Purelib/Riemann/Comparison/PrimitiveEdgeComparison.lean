module

import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Riemann.Normalization.InverseRootComparison
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Algebra.Binomial.Parity
import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Fraction.Order

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
abbrev RegionClearance := Polynomial.Clearance.Box.Region.RegionClearance
/-- The original dense polynomial primitive certificate on its retained box. -/
abbrev DensePrimitive := Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

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

variable {polynomial numerator : Polynomial} {box : Normalization.InverseRootPolynomial.Box} {clearance
  : RegionClearance polynomial box}

section
open Purelib.Polynomial.Dense.Gaussian
/-- Cache the exact numerator and inverse-model bounds from the original clearance and numerator. -/
def build (clearance : RegionClearance polynomial box) (numerator : Polynomial) : PrimitiveOverlapBounds clearance
  numerator :=
  ⟨Bounds.Box.denseEvalNormBound numerator box, rfl, 1 + 4 / clearance.bound, rfl⟩

/-- Restrict the numerator bound to an original inner box while retaining the same inverse ceiling.

The clearance restriction keeps its original positive lower bound. Only
the numerator's finite box evaluation is recomputed; the inverse ceiling
is read from the supplied complete bound record.
-/
def restrict (bounds : PrimitiveOverlapBounds clearance numerator) {inner : Box}
    (refines : inner.Refines box) : PrimitiveOverlapBounds (clearance.restrict refines) numerator :=
  ⟨Bounds.Box.denseEvalNormBound numerator inner, rfl, bounds.inverseUpper, bounds.inverseUpper_eq⟩

/-- Restricting an overlap bound retains its exact original inverse ceiling. -/
theorem restrict_inverseUpper (bounds : PrimitiveOverlapBounds clearance numerator) {inner : Box}
    (refines : inner.Refines box) : (bounds.restrict refines).inverseUpper = bounds.inverseUpper := (rfl)

/-- The exact numerator ceiling on a retained inner box is bounded by the original outer ceiling.

Both finite Horner folds use the same polynomial coefficients. The original
box-refinement certificate bounds the inner fold by the retained outer one.
-/
theorem restrict_numeratorUpper_le (bounds : PrimitiveOverlapBounds clearance numerator) {inner : Box}
    (refines : inner.Refines box) : (bounds.restrict refines).numeratorUpper ≤ bounds.numeratorUpper := by
  have refined := (Bounds.Box.denseHornerNormBounds_mono numerator refines).1
  change Bounds.Box.denseEvalNormBound numerator inner ≤ bounds.numeratorUpper
  exact refined.trans_eq bounds.numeratorUpper_eq.symm

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
    (le_add_of_nonneg_right (Field.div_nonneg_direct (by decide) clearance.positive.le))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Any scalar inverse-root value with the original small residual obeys the retained clearance ceiling.

The coordinate belongs to this bounds cache's cleared box. The scalar may
come from another actual model box; its independent residual certificate
is retained without identifying those geometric owners.
-/
theorem inverse_norm_le_of_residual (bounds : PrimitiveOverlapBounds clearance numerator)
    {point value : Gaussian} (inside : box.Contains point)
    (residual : normSq (1 - polynomial.eval point * value ^ 2) ≤ 1 / 16) :
    normSq value ≤ bounds.inverseUpper := by
  have squareBound : normSq value ^ 2 ≤ 4 / clearance.bound := by
    apply (Field.le_div_iff_pos clearance.positive).2
    calc
      _ = clearance.bound * normSq value ^ 2 := by ring1
      _ ≤ normSq (polynomial.eval point) * normSq value ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          simpa only [Norm.Basic.normSq_eq_canonical] using clearance.lower point inside)
          (Arithmetic.sq_nonneg_direct _)
      _ ≤ 4 := by
        have scalar := InverseRootComparison.normalized_value_bound
          (parameter := polynomial.eval point) (value := value)
          (by simpa only [Norm.Basic.normSq_eq_canonical] using residual)
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
  have elementary : normSq value ≤ 1 + normSq value ^ 2 := by
    apply Arithmetic.le_of_sub_nonneg_direct
    have nonnegative : 0 ≤ (normSq value - 1) ^ 2 + normSq value := by
      calc
        0 = (0 : Coordinate) + 0 := (Fraction.Field.zero_add 0).symm
        _ ≤ _ := Arithmetic.add_le_add_direct (Arithmetic.sq_nonneg_direct (normSq value - 1))
          (normSq_nonneg value)
    exact nonnegative.trans_eq (by ring1)
  rw [bounds.inverseUpper_eq]
  exact elementary.trans (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 1) squareBound)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Every original inverse-root model value inside the cleared box satisfies the retained inverse squared-norm bound. -/
theorem inverse_norm_le (bounds : PrimitiveOverlapBounds clearance numerator) (model : Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) : normSq (model.value.eval point) ≤ bounds.inverseUpper := by
  apply bounds.inverse_norm_le_of_residual inside
  rw [← model.residual_eq]
  exact (model.residualBound point inside).trans model.bound_small

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- The product of the original numerator evaluation and inverse-root model value satisfies the product of the two
retained bounds. -/
theorem numerator_inverse_le (bounds : PrimitiveOverlapBounds clearance numerator) (model : Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) :
    normSq (numerator.eval point * model.value.eval point) ≤ bounds.numeratorUpper * bounds.inverseUpper := by
  rw [normSq_mul]
  have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
  rw [Norm.Basic.normSq_eq_canonical] at scalar
  apply Arithmetic.mul_le_mul_direct
    (scalar.trans_eq bounds.numeratorUpper_eq.symm)
    (bounds.inverse_norm_le model inside) (normSq_nonneg _) bounds.numeratorUpper_nonnegative

section PowerBounds

open Purelib.Data.Gaussian

/-- The original numerator/inverse weight, with finite sensitivity for an actual higher odd denominator power.

The zero-pair branch is the original product. Higher branches consume the
same cached inverse ceiling and the original finite power sensitivity; no
numerator, model or bound certificate is rebuilt by this scalar operation.
-/
def weight (bounds : PrimitiveOverlapBounds clearance numerator) : Nat → Coordinate
  | 0 => bounds.numeratorUpper * bounds.inverseUpper
  | remaining + 1 => (bounds.numeratorUpper * bounds.inverseUpper) *
      Norm.Power.differenceFactor (4 * bounds.inverseUpper) (2 * (remaining + 1) + 1)

/-- The zero-pair weight reads the original cached numerator and inverse-root bounds. -/
theorem weight_zero (bounds : PrimitiveOverlapBounds clearance numerator) :
    bounds.weight 0 = bounds.numeratorUpper * bounds.inverseUpper := (rfl)

open Purelib.Data.Rat in
/-- The same retained primitive-overlap weight is nonnegative at every original pair count. -/
theorem weight_nonnegative (bounds : PrimitiveOverlapBounds clearance numerator) :
    (pairs : Nat) → 0 ≤ bounds.weight pairs
  | 0 => Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le
  | remaining + 1 => Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le)
      (Norm.Power.differenceFactor_nonnegative
        (Arithmetic.mul_nonneg_direct (by decide +kernel) bounds.inverseUpper_positive.le) _)

open Purelib.Data.Rat in
/-- Every restricted odd-power weight is bounded by the same original face weight.

The restricted numerator ceiling decreases, while the cached inverse ceiling
and its finite power-sensitivity factor remain identical. The comparison
therefore retains the actual denominator pair count at every finite power.
-/
theorem restrict_weight_le (bounds : PrimitiveOverlapBounds clearance numerator) {inner : Box}
    (refines : inner.Refines box) (pairs : Nat) :
    (bounds.restrict refines).weight pairs ≤ bounds.weight pairs := by
  have product := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (bounds.restrict_numeratorUpper_le refines) bounds.inverseUpper_positive.le
  cases pairs with
  | zero => exact product
  | succ pairs =>
      exact Arithmetic.mul_le_mul_of_nonneg_right_direct product
        (Norm.Power.differenceFactor_nonnegative
          (Arithmetic.mul_nonneg_direct (by decide) bounds.inverseUpper_positive.le) _)

end PowerBounds

end PrimitiveOverlapBounds

namespace EdgeTransition

variable {polynomial numerator leftCoefficient rightCoefficient : Polynomial} {leftBox rightBox :
  Normalization.InverseRootPolynomial.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {clearance : RegionClearance polynomial leftBox}

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Normalization in
/-- Bound the actual signed odd-power coefficient gap by the original residual sum and retained overlap weight.

The zero-pair branch is the original inverse-model estimate. Higher pairs
reuse its actual retained sign sample and derived common magnitude ceiling;
the original finite power sensitivity supplies the extra scalar weight.
-/
theorem coefficient_gap_le (edge : EdgeTransition left right start finish)
    (bounds : PrimitiveOverlapBounds clearance numerator) {parameter : Coordinate}
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (pairs : optParam Nat 0) :
    normSq (numerator.eval (Affine.line start (finish - start) parameter) *
      (match pairs with
      | 0 => left.value.eval (Affine.line start (finish - start) parameter) -
          edge.sign * right.value.eval (Affine.line start (finish - start) parameter)
      | remaining + 1 => left.value.eval (Affine.line start (finish - start) parameter) ^ (2 * (remaining + 1) + 1) -
          edge.sign * right.value.eval (Affine.line start (finish - start) parameter) ^ (2 * (remaining + 1) + 1))) ≤
      6 * (left.bound + right.bound) * bounds.weight pairs := by
  cases pairs with
  | zero =>
      let sample := edge.sampleAt parameter inside
      have estimate := sample.coefficient_distance_le (edge.left_contains_at inside) (edge.right_contains_at inside)
        (numerator.eval (Affine.line start (finish - start) parameter))
      rw [edge.sampleAt_selected parameter inside, sample.leftValue_eq] at estimate
      have allowanceNonnegative : 0 ≤ 6 * (left.bound + right.bound) :=
        Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative right.bound_nonnegative)
      have identity : numerator.eval (Affine.line start (finish - start) parameter) *
          (left.value.eval (Affine.line start (finish - start) parameter) -
            edge.sign * right.value.eval (Affine.line start (finish - start) parameter)) =
        numerator.eval (Affine.line start (finish - start) parameter) *
            left.value.eval (Affine.line start (finish - start) parameter) -
          numerator.eval (Affine.line start (finish - start) parameter) *
            (edge.sign * right.value.eval (Affine.line start (finish - start) parameter)) := by ring1
      rw [identity]
      exact estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (bounds.numerator_inverse_le left (edge.left_contains_at inside)) allowanceNonnegative)
  | succ remaining =>
      let point := Affine.line start (finish - start) parameter
      let sample := edge.sampleAt parameter inside
      have leftResidual : normSq (1 - polynomial.eval point * sample.leftValue ^ 2) ≤ left.bound := by
        rewrite [sample.leftValue_eq, ← left.residual_eq]
        exact left.residualBound point (edge.left_contains_at inside)
      have rightResidual : normSq (1 - polynomial.eval point * sample.rightValue ^ 2) ≤ right.bound := by
        rewrite [sample.rightValue_eq, ← right.residual_eq]
        exact right.residualBound point (edge.right_contains_at inside)
      have referenceBound : normSq sample.leftValue ≤ bounds.inverseUpper := by
        rewrite [sample.leftValue_eq]
        exact bounds.inverse_norm_le left (edge.left_contains_at inside)
      have estimate := sample.alignment.power_distance_le leftResidual rightResidual
        left.bound_small right.bound_small referenceBound (2 * (remaining + 1) + 1)
      have signedPower : (edge.sign * right.value.eval point) ^ (2 * (remaining + 1) + 1) =
          edge.sign * right.value.eval point ^ (2 * (remaining + 1) + 1) := by
        unfold InverseModelEdgeTransition.EdgeTransition.sign
        cases edge.sample.alignment.flip with
        | false =>
            change ((1 : Gaussian) * right.value.eval point) ^ _ = 1 * right.value.eval point ^ _
            rewrite [Purelib.Data.Gaussian.Basic.one_mul, Purelib.Data.Gaussian.Basic.one_mul]
            rfl
        | true =>
            change ((-1 : Gaussian) * right.value.eval point) ^ _ = -1 * right.value.eval point ^ _
            have first : (-1 : Gaussian) * right.value.eval point = -right.value.eval point := by ring1
            rewrite [first]
            have odd := Purelib.Algebra.Binomial.Parity.neg_pow_odd (right.value.eval point) (remaining + 1)
            have exponent : remaining + 1 + (remaining + 1) + 1 = 2 * (remaining + 1) + 1 := by omega0
            rewrite [exponent] at odd
            exact odd.trans (by ring1)
      rewrite [edge.sampleAt_selected parameter inside] at estimate
      rewrite [sample.leftValue_eq, signedPower] at estimate
      have numeratorBound := Purelib.Polynomial.Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound numerator
        (edge.left_contains_at inside)
      rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical] at numeratorBound
      have product := Arithmetic.mul_le_mul_direct
        (numeratorBound.trans_eq bounds.numeratorUpper_eq.symm) estimate
        (normSq_nonneg _) bounds.numeratorUpper_nonnegative
      rewrite [normSq_mul]
      exact product.trans_eq (by unfold PrimitiveOverlapBounds.weight; ring1)

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Normalization in
/-- Bound the signed difference of two primitive increments along the retained common model edge.

The actual coefficient equations retain the numerator times each indexed
odd model power. The estimate keeps both original primitive owners, the
retained transition sign, edge squared length and parameter displacement.
The omitted zero-pair argument preserves the original inverse coefficient.
-/
theorem primitive_increment_le (edge : EdgeTransition left right start finish)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    {pairs : optParam Nat 0}
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = match pairs with
      | 0 => numerator.eval point * left.value.eval point
      | remaining + 1 => numerator.eval point * left.value.eval point ^ (2 * (remaining + 1) + 1))
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = match pairs with
      | 0 => numerator.eval point * right.value.eval point
      | remaining + 1 => numerator.eval point * right.value.eval point ^ (2 * (remaining + 1) + 1))
    {first last : Coordinate} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((leftPrimitive.value.eval (Affine.line start (finish - start) first) -
        leftPrimitive.value.eval (Affine.line start (finish - start) last)) -
      edge.sign * (rightPrimitive.value.eval (Affine.line start (finish - start) first) -
        rightPrimitive.value.eval (Affine.line start (finish - start) last))) ≤
      12 * (left.bound + right.bound) * bounds.weight pairs *
        normSq (finish - start) * (first - last) ^ 2 := by
  have gap (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      normSq (leftCoefficient.eval (Affine.line start (finish - start) parameter) -
        edge.sign * rightCoefficient.eval (Affine.line start (finish - start) parameter)) ≤
        6 * (left.bound + right.bound) * bounds.weight pairs := by
    cases pairs with
    | zero =>
        rewrite [leftCoefficient_eq, rightCoefficient_eq]
        have identity : numerator.eval (Affine.line start (finish - start) parameter) *
            left.value.eval (Affine.line start (finish - start) parameter) -
            edge.sign * (numerator.eval (Affine.line start (finish - start) parameter) *
              right.value.eval (Affine.line start (finish - start) parameter)) =
            numerator.eval (Affine.line start (finish - start) parameter) *
              (left.value.eval (Affine.line start (finish - start) parameter) -
                edge.sign * right.value.eval (Affine.line start (finish - start) parameter)) := by ring1
        rewrite [identity]
        exact coefficient_gap_le edge bounds inside
    | succ remaining =>
        rewrite [leftCoefficient_eq, rightCoefficient_eq]
        have identity : numerator.eval (Affine.line start (finish - start) parameter) *
            left.value.eval (Affine.line start (finish - start) parameter) ^ (2 * (remaining + 1) + 1) -
            edge.sign * (numerator.eval (Affine.line start (finish - start) parameter) *
              right.value.eval (Affine.line start (finish - start) parameter) ^ (2 * (remaining + 1) + 1)) =
            numerator.eval (Affine.line start (finish - start) parameter) *
              (left.value.eval (Affine.line start (finish - start) parameter) ^ (2 * (remaining + 1) + 1) -
                edge.sign * right.value.eval (Affine.line start (finish - start) parameter) ^
                  (2 * (remaining + 1) + 1)) := by ring1
        rewrite [identity]
        exact coefficient_gap_le edge bounds inside (remaining + 1)
  have scalar := Primitive.Segment.Comparison.DensePrimitive.difference_increment_le leftPrimitive rightPrimitive
    edge.sign start (finish - start)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using edge.sign_norm)
    (⟨0, 1, by decide⟩ : Interval.Bounds)
    (fun _ inside => edge.left_contains_at inside) (fun _ inside => edge.right_contains_at inside)
    (6 * (left.bound + right.bound) * bounds.weight pairs)
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
    (edge : EdgeTransition left right start finish) (leftPrimitive rightPrimitive :
      Polynomial) where
  /-- The cached signed difference of the two primitive start readings. -/ offset : Gaussian
  /-- The offset equals the original left start value minus the transition sign times the original right start value. -/
    offset_eq : offset = leftPrimitive.eval start - edge.sign * rightPrimitive.eval start

constructive_injectivity PrimitiveEdgeAnchor

namespace PrimitiveEdgeAnchor

variable {polynomial leftCoefficient rightCoefficient numerator : Polynomial} {leftBox rightBox :
  Normalization.InverseRootPolynomial.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {edge : EdgeTransition left right start finish}

open Purelib.Riemann.Normalization in
/-- Cache the exact signed primitive offset at the retained edge start. -/
def build (edge : EdgeTransition left right start finish) (leftPrimitive rightPrimitive :
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
      alignedValue anchor start = leftPrimitive.eval
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
    {pairs : optParam Nat 0}
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = match (generalizing := false) pairs with
      | 0 => numerator.eval point * left.value.eval point
      | remaining + 1 => numerator.eval point * left.value.eval point ^ (2 * (remaining + 1) + 1))
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = match (generalizing := false) pairs with
      | 0 => numerator.eval point * right.value.eval point
      | remaining + 1 => numerator.eval point * right.value.eval point ^ (2 * (remaining + 1) + 1))
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (leftPrimitive.value.eval (Affine.line start (finish - start) parameter) -
      alignedValue anchor (Affine.line start (finish -
        start) parameter)) ≤
      12 * (left.bound + right.bound) * (bounds.weight pairs) *
        normSq (Affine.line start (finish - start) parameter - start) := by
  have estimate := EdgeTransition.primitive_increment_le edge bounds
    leftPrimitive rightPrimitive (pairs := pairs) leftCoefficient_eq
    (fun point => by
      cases pairs with
      | zero => exact rightCoefficient_eq point
      | succ remaining => exact rightCoefficient_eq point)
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

The exact scale combines both residual bounds, the retained odd-power
coefficient weight and the original edge squared length. Omitted pairs
retain the literal original zero-pair scale and quarter-radius search.
Accuracy refers to its retained quarter-radius schedule. -/
structure PrimitiveEdgeAccuracy {polynomial numerator : Polynomial} {leftBox rightBox : Box}
    {clearance : RegionClearance polynomial leftBox} (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) (pairs : optParam Nat 0) where
  /-- The retained nonnegative primitive-comparison scale for this original edge and model pair. -/ scale : Coordinate
  /-- The scale equals twelve times the residual sum, retained coefficient weight and original edge squared length. -/
  scale_eq : scale = 12 * (left.bound + right.bound) * (bounds.weight pairs) * normSq (finish - start)
  /-- The retained simultaneous model-refinement index selected for the target. -/ index : Nat
  /-- The retained scale's quarter-radius at the chosen index is strictly below the target. -/ accurate :
    Geometric.Basic.quarterRadius scale index < target

constructive_injectivity PrimitiveEdgeAccuracy

namespace PrimitiveEdgeAccuracy

variable {polynomial numerator : Polynomial} {leftBox rightBox :
  Normalization.InverseRootPolynomial.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian} {target :
      Coordinate} {pairs : Nat}

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Search the original nonnegative edge comparison scale for a quarter-radius index below the positive target.

The returned request retains the exact scale, chosen index and strict accuracy proof for simultaneous refinement of the
two original models. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) (positive : 0 < target) (pairs : Nat := 0) :
    PrimitiveEdgeAccuracy bounds left right start finish target pairs :=
  let scale := 12 * (left.bound + right.bound) * (bounds.weight pairs) * normSq (finish - start)
  have nonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative
        right.bound_nonnegative))
      (bounds.weight_nonnegative pairs))
    (normSq_nonneg _)
  ⟨scale, rfl, Geometric.Search.firstQuarterBelow scale 0 target,
    Geometric.Search.firstQuarterBelow_accurate scale nonnegative 0 target positive⟩

open Purelib.Approximation.Rational in
/-- Refining both original models at the retained request index makes their edge comparison scale strictly smaller than
the target. -/
theorem refined_scale_lt (request : PrimitiveEdgeAccuracy bounds left right start finish target pairs) :
    12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      bounds.weight pairs * normSq (finish - start) < target := by
  have identity : 12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      bounds.weight pairs * normSq (finish - start) =
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
theorem drift_lt (request : PrimitiveEdgeAccuracy bounds left right start finish target pairs)
    (edge : EdgeTransition (left.refine request.index) (right.refine request.index) start
      finish)
    {leftCoefficient rightCoefficient : Polynomial}
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = match (generalizing := false) pairs with
      | 0 => numerator.eval point * (left.refine request.index).value.eval point
      | remaining + 1 => numerator.eval point *
          (left.refine request.index).value.eval point ^ (2 * (remaining + 1) + 1))
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = match (generalizing := false) pairs with
      | 0 => numerator.eval point * (right.refine request.index).value.eval point
      | remaining + 1 => numerator.eval point *
          (right.refine request.index).value.eval point ^ (2 * (remaining + 1) + 1))
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (leftPrimitive.value.eval (Affine.line start (finish - start) parameter) -
      PrimitiveEdgeAnchor.alignedValue anchor (Affine.line start (finish -
        start) parameter)) < target := by
  have estimate := PrimitiveEdgeAnchor.drift_le bounds leftPrimitive
    rightPrimitive anchor (pairs := pairs) leftCoefficient_eq rightCoefficient_eq inside
  have distance := Affine.normSq_line_sub start (finish - start) parameter 0
  rw [InverseModelEdgeTransition.line_zero, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at distance
  have parameterSquare : (parameter - 0) ^ 2 ≤ (1 : Coordinate) := by
    have squared := Arithmetic.pow_le_pow_direct inside.1 inside.2 2
    exact (by ring1 : (parameter - 0) ^ 2 = parameter ^ 2).trans_le (squared.trans_eq (by ring1))
  have scaleNonnegative : 0 ≤ 12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
      bounds.weight pairs * normSq (finish - start) :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (left.refine request.index).bound_nonnegative (right.refine request.index).bound_nonnegative))
        (bounds.weight_nonnegative pairs))
      (normSq_nonneg _)
  apply estimate.trans_lt
  rw [distance]
  calc
    _ = (12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
        bounds.weight pairs * normSq (finish - start)) * (parameter - 0) ^ 2 := by ring1
    _ ≤ (12 * ((left.refine request.index).bound + (right.refine request.index).bound) *
        bounds.weight pairs * normSq (finish - start)) * 1 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct parameterSquare scaleNonnegative
    _ = _ := Fraction.Field.mul_one_direct _
    _ < target := request.refined_scale_lt

end PrimitiveEdgeAccuracy

end Purelib.Riemann.Comparison.PrimitiveEdgeComparison
