module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # The retained source model bound paid by its actual uniform query

The original value-zero reading request has a positive source-patch scale.
Its existing stage payment controls the SAME selected inverse model bound
in terms of the SAME local allowance, without another source request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Polynomial.Dense.Gaussian.Basic (constantOnePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)

variable {parameter : Canonical} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {cell : Cell (parameter := parameter) lifted} (query : Query cell)

/-- The actual value-zero uniform scale dominates twice the same patch's positive inverse-error scale. -/
theorem valueZero_scale_lower :
    2 * cell.patch.inverseErrorScale ≤ query.requests.valueZero.scale := by
  have ceiling := Bounds.Box.twice_normSq_eval_zero_le_denseEvalNormBound constantOnePolynomial cell.patch.box
  rewrite [Evaluation.constantOnePolynomial_eval, Norm.Basic.normSq_one, Field.mul_one_direct] at ceiling
  have numerator : (1 : Rational) ≤ query.requests.valueZero.numeratorUpper :=
    (show (1 : Rational) ≤ 2 by decide +kernel).trans
      (ceiling.trans_eq query.requests.valueZero.numeratorUpper_eq.symm)
  have extra := Order.Arithmetic.mul_nonneg_direct query.bounds.lowerInverse_nonnegative
    (show (0 : Rational) ≤ 1 / 4096 by decide +kernel)
  have inner : cell.patch.inverseErrorScale ≤
      cell.patch.inverseErrorScale + query.bounds.lowerInverse * (1 / 4096) :=
    ((Field.add_comm cell.patch.inverseErrorScale 0).trans
      (Field.zero_add cell.patch.inverseErrorScale)).symm.trans_le
      (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) extra)
  have inverse : 2 * cell.patch.inverseErrorScale ≤ query.bounds.inverseScale :=
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner
      (show (0 : Rational) ≤ 2 by decide +kernel)).trans_eq query.bounds.inverseScale_eq.symm
  have product : query.bounds.inverseScale ≤
      query.requests.valueZero.numeratorUpper * query.bounds.inverseScale :=
    (Field.one_mul query.bounds.inverseScale).symm.trans_le
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numerator query.bounds.inverseScale_nonnegative)
  have scale := (congrArg (fun scale : Rational => query.requests.valueZero.numeratorUpper * scale)
    (show query.bounds.inverseScale = query.bounds.scale 0 by rfl)).trans query.requests.valueZero.scale_eq.symm
  exact inverse.trans (product.trans_eq scale)

include query in
/-- The SAME original selected source model bound is paid by its actual cell allowance.

The given Query already pays its retained value-zero selection at the
model's actual depth. Its positive patch scale and the exact original
Newton bound law give the displayed ratio, with no stage change, later
model, new Point or numerical-bound premise.
-/
theorem model_bound_le_allowance :
    cell.request.model.bound ≤
      (cell.patch.base.model.bound / (2 * cell.patch.inverseErrorScale)) * (cell.allowance / 4) := by
  let scale := 2 * cell.patch.inverseErrorScale
  let ratio := cell.patch.base.model.bound / scale
  let stage := cell.request.selection.stage
  have positive : (0 : Rational) < scale :=
    Order.Arithmetic.mul_pos_direct (by decide +kernel) cell.patch.inverseErrorScale_positive
  have ratioNonnegative : (0 : Rational) ≤ ratio :=
    Order.Field.div_nonneg_direct cell.patch.base.model.bound_nonnegative positive.le
  have paid := query.requests.valueZero.selection.later_accurate
    (query.requests.valueZero_stage_le.trans query.stage)
  have common : Geometric.Basic.quarterRadius scale stage ≤ cell.allowance / 4 :=
    (Geometric.Basic.quarterRadius_scale_mono (valueZero_scale_lower query) stage).trans paid.le
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct common ratioNonnegative
  have cancelled : ratio * scale = cell.patch.base.model.bound :=
    Field.div_mul_cancel_of_ne cell.patch.base.model.bound scale positive.ne'
  have radius : ratio * Geometric.Basic.quarterRadius scale stage =
      Geometric.Basic.quarterRadius cell.patch.base.model.bound stage := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    exact (Field.mul_assoc ratio scale ((1 / 4 : Rational) ^ stage)).symm.trans
      (congrArg (fun value : Rational => value * (1 / 4 : Rational) ^ stage) cancelled)
  have original : cell.request.model.bound =
      Geometric.Basic.quarterRadius cell.patch.base.model.bound stage :=
    (congrArg (fun model : Model (Paths.polynomial parameter) cell.patch.base.box => model.bound)
      cell.request.model_eq).trans (cell.patch.base.model.refine_bound stage)
  exact (original.trans radius.symm).trans_le scaled

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

end
