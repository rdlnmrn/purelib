module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope.Numerators
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # A fixed six-row request and sufficient fine-layer depth before observations

One original depth-seven envelope cache computes the common request. Its
finite total bounds every original finer row allocation. The selected depth
pays both actual chart geometry and the original layer's old cofactor
accuracy; neither an old observed radius nor an old trace is relabelled.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope

namespace Numerators

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.RootContinuation
open Transport.Spatial.Factors
open Transport.Spatial.Parallel (Geometry)
open Segment.Reading

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable (data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Specification.Table.forms parameter index))
variable {regular : parameter ≠ criticalValue site} {left right : Endpoint}
variable (retained : Cache (quarter := quarter) regular 7 left right)

/-- The SAME original fixed total computes a positive common request for every actual finer row and physical query. -/
def request (target : AccuracyRequest) : AccuracyRequest :=
  (⟨target.tolerance / (1 + cost data 7 left right retained),
    Fraction.Order.Field.div_pos_direct target.positive
      (Arithmetic.add_pos_of_pos_of_nonneg_direct
        (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1)
        (cost_nonnegative data 7 left right retained))⟩ : AccuracyRequest).minimum
      (Payment.Uniform.spatialRequest site parameter regular)

/-- The common request retains the scalar minimum computed from the same stored coarse total. -/
theorem request_tolerance (target : AccuracyRequest) :
    (request data retained target).tolerance =
      min (target.tolerance / (1 + cost data 7 left right retained))
        (Payment.Uniform.spatialRequest site parameter regular).tolerance := by
  unfold request
  rfl

/-- The actual original fixed total multiplied by the computed request is paid by the original chosen tolerance. -/
theorem request_payment (target : AccuracyRequest) :
    cost data 7 left right retained * (request data retained target).tolerance ≤ target.tolerance := by
  let total := cost data 7 left right retained
  have nonnegative : 0 ≤ total := cost_nonnegative data 7 left right retained
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) nonnegative
  have ratio : total / (1 + total) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
    exact (Fraction.Field.zero_add total).symm.trans_le
      ((Arithmetic.add_le_add_direct
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) (Fraction.Order.Basic.le_refl total)).trans_eq
          (Fraction.Field.one_mul _).symm)
  have chosen : (request data retained target).tolerance ≤ target.tolerance / (1 + total) :=
    AccuracyRequest.minimum_le_left _ _
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct chosen nonnegative
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct ratio target.positive.1
  apply scaled.trans
  exact (show total * (target.tolerance / (1 + total)) =
    target.tolerance * (total / (1 + total)) by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le (paid.trans_eq (Fraction.Field.mul_one_direct _))

namespace Selected

variable {data retained} {time : Fraction.Rational}
variable (selected : Selected data retained time)

include selected

/-- The actual time lies in the selected original coarse sharp source interval with its exact depth-seven payment. -/
theorem source_paid (ordered : left.parameter ≤ right.parameter) :
    (time - selected.1.left.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := by
  have upper := Arithmetic.sub_le_sub_right_direct selected.between.2 selected.1.left.parameter
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.sub_nonneg_direct selected.between.1) upper 2
  exact squared.trans
    (dyadicEdges_width_le 7 7 (Nat.le_refl 7) left right ordered selected.1 selected.member)

variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {inside : FixedRootBoxPath.Inside time} {source : Transport.Reading actual time inside}
variable {anchor : Parameter.Anchor source.lift}

/-- The SAME fixed common request is below every actual finer original Allocation.request at the selected time. -/
theorem fine_request_le (ordered : left.parameter ≤ right.parameter) (target : AccuracyRequest) (index : Fin 6)
    (bounds : Coefficient.Bounds (data index) anchor) :
    (request data retained target).tolerance ≤ (Coefficient.Allocation.request bounds target).tolerance := by
  have costBound := selected.cost_le index
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1)
    ((selected.leaf.get index).cost_nonnegative (data index))
  have quotient := Fraction.Order.Field.div_le_div_of_nonneg_left_direct target.positive.1 denominator
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) costBound)
  have toLeaf : (request data retained target).tolerance ≤
      ((selected.leaf.get index).request (data index) target).tolerance := by
    rewrite [request_tolerance data retained target,
      (selected.leaf.get index).request_tolerance (data index) target]
    exact Fraction.Order.Basic.min_le_min quotient (Fraction.Order.Basic.le_refl _)
  exact toLeaf.trans ((selected.leaf.get index).fine_request_le
    (data index) target bounds (selected.source_paid ordered))

/-- The actual fine row's original cost is bounded by the SAME original fixed total before any finer observation. -/
theorem fine_cost_le (ordered : left.parameter ≤ right.parameter) (index : Fin 6)
    (bounds : Coefficient.Bounds (data index) anchor) :
    Coefficient.Allocation.cost bounds ≤ cost data 7 left right retained :=
  ((selected.leaf.get index).fine_cost_le (data index) bounds (selected.source_paid ordered)).trans
    (selected.cost_le index)

end Selected

/-- The original geometric finite search pays the common physical tolerance with actual finer chart widths. -/
def chartMinimum (target : AccuracyRequest) : Nat :=
  Geometry.widthMinimum site parameter (request data retained target)

/-- A separate original finite search makes the actual new layer cofactor request meet the common tolerance. -/
def cofactorMinimum (initialAccuracy target : AccuracyRequest) : Nat :=
  Geometric.Search.firstQuarterBelow initialAccuracy.tolerance 0 (request data retained target).tolerance

/-- Choose a sufficient original fine-layer depth before any new geometry, old curved sample or physical query. -/
def minimum (initialAccuracy target : AccuracyRequest) : Nat :=
  max 7 (max (chartMinimum data retained target) (cofactorMinimum data retained initialAccuracy target))

/-- The SAME chosen depth pays original sharp-box geometry. -/
theorem seven_le (initialAccuracy target : AccuracyRequest) : 7 ≤ minimum data retained initialAccuracy target :=
  Nat.Order.le_max_left _ _

/-- The SAME chosen depth pays all actual finer physical Route queries. -/
theorem chartMinimum_le (initialAccuracy target : AccuracyRequest) :
    chartMinimum data retained target ≤ minimum data retained initialAccuracy target :=
  (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)

/-- The SAME chosen depth pays actual finer original cofactor observations rather than retagging an old sample. -/
theorem cofactorMinimum_le (initialAccuracy target : AccuracyRequest) :
    cofactorMinimum data retained initialAccuracy target ≤ minimum data retained initialAccuracy target :=
  (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)

variable {row : Fin 6} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {initialAccuracy : AccuracyRequest} {initial : Differential.Refinement.Piece (data row) actual initialAccuracy}
variable {depth : Nat} (layer : Differential.Refinement.Layer initial depth)

/-- The literal original accuracy stored by a genuinely new sufficient layer is below the common computed request. -/
theorem layer_accuracy_le (target : AccuracyRequest)
    (enough : minimum data retained initialAccuracy target ≤ depth) :
    layer.accuracy.tolerance ≤ (request data retained target).tolerance := by
  rewrite [layer.accuracy_eq]
  have depthPaid := (cofactorMinimum_le data retained initialAccuracy target).trans enough
  exact (Geometric.Basic.quarterRadius_antitone initialAccuracy.positive.1 depthPaid).trans
    (Geometric.Search.firstQuarterBelow_accurate initialAccuracy.tolerance initialAccuracy.positive.1 0
      (request data retained target).tolerance (request data retained target).positive).1

/-- Every actual fine row's complete residual cost is paid on the literal new layer's original cofactor request. -/
theorem layer_cost_payment (target : AccuracyRequest)
    (enough : minimum data retained initialAccuracy target ≤ depth)
    {time : Fraction.Rational} (between : left.parameter ≤ time ∧ time ≤ right.parameter)
    {inside : FixedRootBoxPath.Inside time} {source : Transport.Reading actual time inside}
    (anchor : Parameter.Anchor source.lift) (bounds : Coefficient.Bounds (data row) anchor) :
    Coefficient.Allocation.cost bounds * layer.accuracy.tolerance ≤ target.tolerance := by
  let selected := select data 7 left right retained time between
  have costBound := selected.fine_cost_le (between.1.trans between.2) row bounds
  have paid := layer_accuracy_le data retained layer target enough
  have scaled := Arithmetic.mul_le_mul_direct costBound paid layer.accuracy.positive.1
    (cost_nonnegative data 7 left right retained)
  exact scaled.trans (request_payment data retained target)

/-- The actual unchanged old-cofactor term is paid on the newly selected original Layer request. -/
theorem layer_source_payment (target : AccuracyRequest)
    (enough : minimum data retained initialAccuracy target ≤ depth)
    {time : Fraction.Rational} (between : left.parameter ≤ time ∧ time ≤ right.parameter)
    {inside : FixedRootBoxPath.Inside time} {source : Transport.Reading actual time inside}
    (anchor : Parameter.Anchor source.lift) (bounds : Coefficient.Bounds (data row) anchor) :
    4 * (Coefficient.Allocation.sourceCoefficient bounds * layer.accuracy.tolerance) ≤ target.tolerance := by
  have coefficients := Coefficient.Allocation.coefficients_nonnegative bounds
  have residuals : Coefficient.Allocation.sourceCoefficient bounds ≤
      Coefficient.Allocation.sourceCoefficient bounds + Coefficient.Allocation.normalCoefficient bounds +
        Coefficient.Allocation.spatialCoefficient bounds := by
    have paid := Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl (Coefficient.Allocation.sourceCoefficient bounds)) coefficients.2.1)
      coefficients.2.2
    exact (show Coefficient.Allocation.sourceCoefficient bounds =
      (Coefficient.Allocation.sourceCoefficient bounds + 0) + 0 by ring1).trans_le paid
  have arithmetic := Arithmetic.add_le_add_direct
    (Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
      (Coefficient.Allocation.arithmeticCeiling_nonnegative bounds))
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 7)
  have lower := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct residuals
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)) arithmetic
  have costLower : 4 * Coefficient.Allocation.sourceCoefficient bounds ≤ Coefficient.Allocation.cost bounds := by
    apply (show 4 * Coefficient.Allocation.sourceCoefficient bounds =
      4 * Coefficient.Allocation.sourceCoefficient bounds + 0 by ring1).trans_le
    apply lower.trans_eq
    unfold Coefficient.Allocation.cost
    ring1
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct costLower layer.accuracy.positive.1
  exact (show 4 * (Coefficient.Allocation.sourceCoefficient bounds * layer.accuracy.tolerance) =
    (4 * Coefficient.Allocation.sourceCoefficient bounds) * layer.accuracy.tolerance by ring1).trans_le
      (paid.trans (layer_cost_payment data retained layer target enough between anchor bounds))

/-- The same before-observation schedule pays every edge point of the actual new neighboring-source Geometry. -/
theorem layer_next_pointBound (target : AccuracyRequest)
    (enough : minimum data retained initialAccuracy target ≤ depth)
    {start finish : Fraction.Rational}
    (chain : Integration.Partition.Interval.Chain start finish
      (Differential.Refinement.Piece.chartIntervals layer.pieces))
    (index : Nat) (bound : index < layer.pieces.length) (nextBound : index + 1 < layer.pieces.length) :
    Polynomial.Geometry.ClearPath.PointBound
      (Transport.Spatial.coordinate site parameter 2 quarter positive (layer.pieces[index]'bound).span.lower)
      (request data retained target).tolerance
      (layer.nextGeometry chain index bound nextBound regular
        ((seven_le data retained initialAccuracy target).trans enough)).route.path :=
  layer.nextGeometry_pointBound chain index bound nextBound regular
    ((seven_le data retained initialAccuracy target).trans enough) (request data retained target)
    ((chartMinimum_le data retained initialAccuracy target).trans enough)

end Numerators

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope

end
