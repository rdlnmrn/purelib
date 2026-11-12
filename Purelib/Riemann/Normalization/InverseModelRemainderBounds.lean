module

public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Weighted square-residual remainders at an original inverse model

The original Newton model supplies one square residual and inverse-value
ceiling. A retained coefficient bounds the linear and cubic weighted
remainders; combination with the same primitive mismatch gives certified
finite refinement budgets for both differential-relation shapes.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelRemainderBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Approximation.Rational.Geometric

set_option genInjectivity false in
/-- Retain weighted linear and cubic square-residual budgets at one original inverse model.

The coefficient ceiling is computed once on the original box. Both scales
reuse that ceiling, the original square-residual bound and the same cached
inverse-model norm ceiling.
-/
structure RemainderBounds {polynomial : Polynomial} {box : Box} {clearance : RegionClearance polynomial box}
    {initial : Model polynomial box} (root : DerivativeBounds clearance initial) (coefficient : Polynomial) where
  /-- The retained coefficient squared-norm ceiling on the original box. -/
  coefficientUpper : Coordinate
  /-- The coefficient ceiling is the original exact box calculation. -/
  coefficientUpper_eq : coefficientUpper = Bounds.Box.denseEvalNormBound coefficient box
  /-- The cached cube of the original inverse-value norm ceiling. -/
  inverseCube : Coordinate
  /-- The cube uses the original retained inverse-value ceiling. -/
  inverseCube_eq : inverseCube = root.inverseUpper ^ 3
  /-- The cached geometric scale for the coefficient times inverse value times square residual. -/
  linearScale : Coordinate
  /-- The linear scale retains the original coefficient, inverse and residual ceilings. -/
  linearScale_eq : linearScale = coefficientUpper * root.inverseUpper * initial.bound
  /-- The cached geometric scale for the cubic square-residual discrepancy. -/
  cubicScale : Coordinate
  /-- The cubic scale includes the original uniform one-sixteenth residual ceiling. -/
  cubicScale_eq : cubicScale =
    2 * (coefficientUpper * inverseCube + (2 * (4 + 1 / 16)) * root.inverseUpper) * initial.bound

constructive_injectivity RemainderBounds

namespace RemainderBounds

variable {polynomial coefficient : Polynomial} {box : Box} {clearance : RegionClearance polynomial box}
  {initial : Model polynomial box} {root : DerivativeBounds clearance initial}

/-- Compute the coefficient ceiling and both source-derived square-residual scales once. -/
@[expose] def build (root : DerivativeBounds clearance initial) (coefficient : Polynomial) :
    RemainderBounds root coefficient :=
  let upper := Bounds.Box.denseEvalNormBound coefficient box
  let cube := root.inverseUpper ^ 3
  ⟨upper, rfl, cube, rfl, upper * root.inverseUpper * initial.bound, rfl,
    2 * (upper * cube + (2 * (4 + 1 / 16)) * root.inverseUpper) * initial.bound, rfl⟩

/-- The retained coefficient ceiling is nonnegative. -/
theorem coefficientUpper_nonnegative (bounds : RemainderBounds root coefficient) : 0 ≤ bounds.coefficientUpper := by
  rewrite [bounds.coefficientUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The retained inverse-value cube is nonnegative. -/
theorem inverseCube_nonnegative (bounds : RemainderBounds root coefficient) : 0 ≤ bounds.inverseCube := by
  rewrite [bounds.inverseCube_eq]
  exact Arithmetic.pow_nonneg_direct root.inverseUpper_positive.le 3

/-- The retained linear square-residual scale is nonnegative. -/
theorem linearScale_nonnegative (bounds : RemainderBounds root coefficient) : 0 ≤ bounds.linearScale := by
  rewrite [bounds.linearScale_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct bounds.coefficientUpper_nonnegative root.inverseUpper_positive.le)
    initial.bound_nonnegative

/-- The retained cubic square-residual scale is nonnegative. -/
theorem cubicScale_nonnegative (bounds : RemainderBounds root coefficient) : 0 ≤ bounds.cubicScale := by
  rewrite [bounds.cubicScale_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Arithmetic.mul_nonneg_direct bounds.coefficientUpper_nonnegative bounds.inverseCube_nonnegative)
      (Arithmetic.mul_nonneg_direct (by decide) root.inverseUpper_positive.le)))
    initial.bound_nonnegative

/-- The original weighted linear square-residual remainder decays at the retained geometric rate. -/
theorem linear_bound (bounds : RemainderBounds root coefficient) (stage : Nat) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (coefficient.eval point * (initial.refine stage).value.eval point *
      (initial.refine stage).residual.eval point) ≤ quarterRadius bounds.linearScale stage := by
  let model := initial.refine stage
  have coefficientLe : normSq (coefficient.eval point) ≤ bounds.coefficientUpper := by
    have bound := Bounds.Box.normSq_eval_le_denseEvalNormBound coefficient inside
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans_eq bounds.coefficientUpper_eq.symm
  have residualLe : normSq (model.residual.eval point) ≤ quarterRadius initial.bound stage := by
    have bound := initial.refine_residualBound stage point inside
    rewrite [← model.residual_eq] at bound
    exact bound
  rewrite [normSq_mul, normSq_mul]
  have product := Arithmetic.mul_le_mul_direct coefficientLe (root.value_le model inside)
    (normSq_nonneg _) bounds.coefficientUpper_nonnegative
  have total := Arithmetic.mul_le_mul_direct product residualLe (normSq_nonneg _)
    (Arithmetic.mul_nonneg_direct bounds.coefficientUpper_nonnegative root.inverseUpper_positive.le)
  apply total.trans_eq
  rewrite [bounds.linearScale_eq, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  ring1

/-- A scalar within the displayed residual ceiling gives the exact two-minus-residual norm budget. -/
private theorem two_sub_norm_le (value : Gaussian) (small : normSq value ≤ (1 / 16 : Coordinate)) :
    normSq (2 - value) ≤ (2 * (4 + 1 / 16) : Coordinate) := by
  have bound := Norm.Bounds.normSq_sub_le_two (2 : Gaussian) value
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
    show normSq (2 : Gaussian) = 4 by decide] at bound
  have added : (4 : Coordinate) + normSq value ≤ 4 + (1 / 16 : Coordinate) :=
    Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 4) small
  have scaled : (2 : Coordinate) * (4 + normSq value) ≤ 2 * (4 + (1 / 16 : Coordinate)) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct added (by decide)
  exact bound.trans scaled

/-- The original weighted cubic discrepancy decays at the retained geometric rate.

The expression is `e(Bq³-q(2-e))`, with the same original finite value `q`
and its actual square residual `e`. The uniform one-sixteenth residual
ceiling supplies the fixed `65/8` squared-norm bound for `2-e`.
-/
theorem cubic_bound (bounds : RemainderBounds root coefficient) (stage : Nat) {point : Gaussian}
    (inside : box.Contains point) :
    normSq ((initial.refine stage).residual.eval point *
      (coefficient.eval point * (initial.refine stage).value.eval point ^ 3 -
        (initial.refine stage).value.eval point * (2 - (initial.refine stage).residual.eval point))) ≤
      quarterRadius bounds.cubicScale stage := by
  let model := initial.refine stage
  have coefficientLe : normSq (coefficient.eval point) ≤ bounds.coefficientUpper := by
    have bound := Bounds.Box.normSq_eval_le_denseEvalNormBound coefficient inside
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans_eq bounds.coefficientUpper_eq.symm
  have valueLe := root.value_le model inside
  have residualLe : normSq (model.residual.eval point) ≤ quarterRadius initial.bound stage := by
    have bound := initial.refine_residualBound stage point inside
    rewrite [← model.residual_eq] at bound
    exact bound
  have residualSmall : normSq (model.residual.eval point) ≤ (1 / 16 : Coordinate) :=
    (model.residualBound point inside).trans model.bound_small
  have factorLe := two_sub_norm_le (model.residual.eval point) residualSmall
  have cubeNorm : normSq (model.value.eval point ^ 3) = normSq (model.value.eval point) ^ 3 := by
    have equation := Power.normSq_pow (model.value.eval point) 3
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at equation
    exact equation
  have cubeLe : normSq (model.value.eval point ^ 3) ≤ bounds.inverseCube := by
    rewrite [cubeNorm, bounds.inverseCube_eq]
    exact Arithmetic.pow_le_pow_direct (normSq_nonneg _) valueLe 3
  have firstLe : normSq (coefficient.eval point * model.value.eval point ^ 3) ≤
      bounds.coefficientUpper * bounds.inverseCube := by
    rewrite [normSq_mul]
    exact Arithmetic.mul_le_mul_direct coefficientLe cubeLe (normSq_nonneg _)
      bounds.coefficientUpper_nonnegative
  have secondLe : normSq (model.value.eval point * (2 - model.residual.eval point)) ≤
      (2 * (4 + 1 / 16) : Coordinate) * root.inverseUpper := by
    rewrite [normSq_mul]
    have bound := Arithmetic.mul_le_mul_direct valueLe factorLe (normSq_nonneg _)
      root.inverseUpper_positive.le
    exact bound.trans_eq (Fraction.mul_comm _ _)
  have innerLe : normSq (coefficient.eval point * model.value.eval point ^ 3 -
      model.value.eval point * (2 - model.residual.eval point)) ≤
      2 * (bounds.coefficientUpper * bounds.inverseCube + (2 * (4 + 1 / 16)) * root.inverseUpper) := by
    have bound := Norm.Bounds.normSq_sub_le_two (coefficient.eval point * model.value.eval point ^ 3)
      (model.value.eval point * (2 - model.residual.eval point))
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstLe secondLe) (by decide))
  rewrite [normSq_mul]
  have total := Arithmetic.mul_le_mul_direct residualLe innerLe (normSq_nonneg _)
    (quarterRadius_nonneg initial.bound_nonnegative stage)
  apply total.trans_eq
  rewrite [bounds.cubicScale_eq, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  ring1

variable {numerator : Polynomial} {residual : DifferentialResidualBounds initial}
  {primitive : PrimitiveDerivativeBounds root numerator}

/-- The source-derived scale combining a linear square-residual remainder and the original inverse-root primitive. -/
@[expose] def connectionScale (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 0) : Coordinate :=
  2 * (bounds.linearScale + delta.scale)

/-- The source-derived scale combining a cubic square-residual discrepancy and the original third-power primitive. -/
@[expose] def scalarScale (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 2) : Coordinate :=
  2 * (bounds.cubicScale + delta.scale)

/-- The retained original linear and primitive error scales give a nonnegative combined scale. -/
theorem connectionScale_nonnegative (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 0) : 0 ≤ bounds.connectionScale delta :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg bounds.linearScale_nonnegative delta.scale_nonnegative)

/-- The retained original cubic and primitive error scales give a nonnegative combined scale. -/
theorem scalarScale_nonnegative (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 2) : 0 ≤ bounds.scalarScale delta :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg bounds.cubicScale_nonnegative delta.scale_nonnegative)

/-- The original linear remainder minus the original primitive mismatch has a fully derived geometric ceiling. -/
theorem connection_bound (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 0) (stage : Nat) {point : Gaussian}
    (inside : box.Contains point) :
    normSq (-(coefficient.eval point * (initial.refine stage).value.eval point *
        (initial.refine stage).residual.eval point) -
      primitiveMismatch (initial.refine stage) numerator delta.coefficient 0 point) ≤
      quarterRadius (bounds.connectionScale delta) stage := by
  have bound := Norm.Bounds.normSq_sub_le_two
    (-(coefficient.eval point * (initial.refine stage).value.eval point * (initial.refine stage).residual.eval point))
    (primitiveMismatch (initial.refine stage) numerator delta.coefficient 0 point)
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_eq_canonical, normSq_neg] at bound
  apply (bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (bounds.linear_bound stage inside)
      (delta.refine_bound stage inside)) (by decide))).trans_eq
  rewrite [connectionScale, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  ring1

/-- The original cubic discrepancy minus the original third-power primitive mismatch has a derived geometric ceiling. -/
theorem scalar_bound (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 2) (stage : Nat) {point : Gaussian}
    (inside : box.Contains point) :
    normSq ((initial.refine stage).residual.eval point *
        (coefficient.eval point * (initial.refine stage).value.eval point ^ 3 -
          (initial.refine stage).value.eval point * (2 - (initial.refine stage).residual.eval point)) -
      primitiveMismatch (initial.refine stage) numerator delta.coefficient 2 point) ≤
      quarterRadius (bounds.scalarScale delta) stage := by
  have bound := Norm.Bounds.normSq_sub_le_two
    ((initial.refine stage).residual.eval point *
      (coefficient.eval point * (initial.refine stage).value.eval point ^ 3 -
        (initial.refine stage).value.eval point * (2 - (initial.refine stage).residual.eval point)))
    (primitiveMismatch (initial.refine stage) numerator delta.coefficient 2 point)
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at bound
  apply (bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (bounds.cubic_bound stage inside)
      (delta.refine_bound stage inside)) (by decide))).trans_eq
  rewrite [scalarScale, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
  ring1

/-- Choose and retain a finite stage paying a request from the actual combined linear and primitive scale. -/
@[expose] def chooseConnection (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 0) (current : Nat)
    (target : Coordinate) (targetPositive : 0 < target) :
    Search.Selection (bounds.connectionScale delta) current target :=
  Search.Selection.build (bounds.connectionScale delta) (bounds.connectionScale_nonnegative delta)
    current target targetPositive

/-- Choose and retain a finite stage paying a request from the actual combined cubic and primitive scale. -/
@[expose] def chooseScalar (bounds : RemainderBounds root coefficient)
    (delta : PrimitiveResidualBounds root residual primitive 2) (current : Nat)
    (target : Coordinate) (targetPositive : 0 < target) : Search.Selection (bounds.scalarScale delta) current target :=
  Search.Selection.build (bounds.scalarScale delta) (bounds.scalarScale_nonnegative delta) current target targetPositive

end RemainderBounds

end Purelib.Riemann.Normalization.InverseModelRemainderBounds
