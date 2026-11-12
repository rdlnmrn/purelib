module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual six-row allocations before curved and physical observations

Six retained original numerator folds use one original source Anchor. Their
finite nonnegative costs compute a shared old-cofactor request and a common
physical/source request before observations. The six original differential
and exponent indices remain distinct, including the quintic channels.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

open Purelib
open Purelib.Algebra
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre.Periods
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable (data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Jets.Specification.Table.forms parameter index))

/-- The six original numerator-bound caches at one SAME retained physical source Anchor. -/
abbrev Rows := Data.Vector.DependentVector (fun index => Bounds (data index) anchor)

namespace Rows

open Purelib.Data.Rat.Fraction.Order

/-- Compute and store each original numerator fold once before any later cofactor or arithmetic request. -/
def build (anchor : Parameter.Anchor source.lift) : Rows (anchor := anchor) data :=
  Data.Vector.DependentVector.ofFn (fun index => Bounds.build (data index) anchor)

/-- Every stored row is the original numerator cache factory at the SAME original source and differential index. -/
theorem build_get (anchor : Parameter.Anchor source.lift) (index : Fin 6) :
    (build data anchor).get index = Bounds.build (data index) anchor :=
  Data.Vector.DependentVector.ofFn_get _ index

variable {data} (rows : Rows (anchor := anchor) data)

/-- The six unchanged old-cofactor multipliers have one computed finite nonnegative total. -/
@[expose] def sourceCost : Fraction.Rational :=
  FiniteSum.Fin.sumFin (fun index => 4 * sourceCoefficient (rows.get index))

/-- The original retained row costs make the common old-cofactor multiplier nonnegative. -/
theorem sourceCost_nonnegative : 0 ≤ rows.sourceCost :=
  FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index =>
    Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
      (coefficients_nonnegative (rows.get index)).1)

/-- Each exact original old-cofactor multiplier is bounded by the SAME cached finite cost sum. -/
theorem sourceCost_le (index : Fin 6) :
    4 * sourceCoefficient (rows.get index) ≤ rows.sourceCost :=
  FiniteSum.Rational.Order.weight_le_sum _ (fun entry =>
    Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)
      (coefficients_nonnegative (rows.get entry)).1) index

/-- Choose a positive actual old-cofactor residual request before any of the six curved scalar values is observed. -/
def sourceRequest (target : AccuracyRequest) : AccuracyRequest :=
  ⟨target.tolerance / (1 + rows.sourceCost), Fraction.Order.Field.div_pos_direct target.positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) rows.sourceCost_nonnegative)⟩

/-- The newly chosen cofactor request pays every actual row's old-source residual contribution. -/
theorem source_payment (target : AccuracyRequest) (index : Fin 6) :
    4 * (sourceCoefficient (rows.get index) * (rows.sourceRequest target).tolerance) ≤ target.tolerance := by
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) rows.sourceCost_nonnegative
  have ratio : rows.sourceCost / (1 + rows.sourceCost) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
    exact (Fraction.Field.zero_add rows.sourceCost).symm.trans_le
      ((Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _)).trans_eq (Fraction.Field.one_mul _).symm)
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct ratio target.positive.le
  have chosen := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (rows.sourceCost_le index) (rows.sourceRequest target).positive.le
  apply (show 4 * (sourceCoefficient (rows.get index) * (rows.sourceRequest target).tolerance) =
    (4 * sourceCoefficient (rows.get index)) * (rows.sourceRequest target).tolerance by ring1).trans_le
  apply chosen.trans
  exact (show rows.sourceCost * (rows.sourceRequest target).tolerance =
    target.tolerance * (rows.sourceCost / (1 + rows.sourceCost)) by
      change rows.sourceCost * (target.tolerance / (1 + rows.sourceCost)) =
        target.tolerance * (rows.sourceCost / (1 + rows.sourceCost))
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le (paid.trans_eq (Fraction.Field.mul_one_direct _))

/-- The same six existing fine-work multipliers have a computed finite nonnegative total. -/
@[expose] def workCost : Fraction.Rational := FiniteSum.Fin.sumFin (fun index => cost (rows.get index))

/-- The common fine-work cost is nonnegative before every physical/query observation. -/
theorem workCost_nonnegative : 0 ≤ rows.workCost :=
  FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index => cost_nonnegative (rows.get index))

/-- Every actual original row's work cost is bounded by the SAME finite total. -/
theorem workCost_le (index : Fin 6) : cost (rows.get index) ≤ rows.workCost :=
  FiniteSum.Rational.Order.weight_le_sum _ (fun entry => cost_nonnegative (rows.get entry)) index

/-- A common positive physical/source accuracy is computed before selecting any six-channel source model. -/
def commonRequest (target : AccuracyRequest) : AccuracyRequest :=
  (⟨target.tolerance / (1 + rows.workCost), Fraction.Order.Field.div_pos_direct target.positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) rows.workCost_nonnegative)⟩ : AccuracyRequest).minimum
    (Segment.Reading.Payment.spatialRequest anchor)

/-- The SAME common accuracy pays every original row's own independent Fine.work request. -/
theorem common_le (target : AccuracyRequest) (index : Fin 6) :
    (rows.commonRequest target).tolerance ≤ (request (rows.get index) target).tolerance := by
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (cost_nonnegative (rows.get index))
  have increasing := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) (rows.workCost_le index)
  have quotient := Fraction.Order.Field.div_le_div_of_nonneg_left_direct target.positive.le
    denominator increasing
  rewrite [request_tolerance]
  change min (target.tolerance / (1 + rows.workCost))
      (Segment.Reading.Payment.spatialRequest anchor).tolerance ≤
    min (target.tolerance / (1 + cost (rows.get index)))
      (Segment.Reading.Payment.spatialRequest anchor).tolerance
  exact Fraction.Order.Basic.min_le_min quotient (Fraction.Order.Basic.le_refl _)

end Rows

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

end
