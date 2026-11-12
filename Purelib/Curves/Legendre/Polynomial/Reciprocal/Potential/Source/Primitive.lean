module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial.Factor
public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells.Numerator
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Tactic.Ring

/-! # Physical primitive cells from the same regular and reciprocal model caches

The retained parity primitive supplies C=U*P*B. Its new primitive numerator
budgets reuse the original reciprocal root and differential-residual data.
The physical cell then consumes the same actual reciprocal inverse and cube;
no preparation, observation, quotient or inverse refinement is replayed.
The finite primitive mismatch remains an explicit nonzero error budget.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box half)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual (PrimitiveResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal sourceDifferential}
    {preparation : PotentialComparison.Preparation comparison}
    {numerator : Polynomial} {index : Nat} {regularBox : Box}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- The actual physical numerator, its original two derivative budgets and the same-cache reciprocal cell.

The new coefficient is derived from the supplied regular-model parity sample.
Both derivative budgets retain the original reciprocal initial model and its
root/residual owners. The final original Cell contains the supplied inverse
and power bank, with only its numerator-dependent tables newly constructed.
-/
@[expose] def PhysicalPrimitive (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : Type _ :=
  (coefficient : { value : Polynomial // value = sample.physicalCoefficient }) ×
  (primitive : PrimitiveDerivativeBounds comparison.rootBounds coefficient.val) ×
  (bounds : PrimitiveResidualBounds comparison.rootBounds terminal.preparation.reciprocal primitive 0) ×
  { cell : Cell bounds coordinate stage allowance nonnegative // cell = Cell.withNumerator bounds retained }

/-- Build the physical numerator and its budgets once, then reuse the original reciprocal inverse and cube.

The actual stage is retained unchanged. Its resulting finite error bound is
not assumed to pay any new target; a stricter requested target needs the
corresponding original finite selection before a sufficient cell is built.
-/
def physicalPrimitive (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : PhysicalPrimitive sample retained :=
  let coefficient := sample.physicalCoefficient
  let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
  let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
  let cell := Cell.withNumerator bounds retained
  ⟨⟨coefficient, rfl⟩, primitive, bounds, ⟨cell, rfl⟩⟩

/-- The whole physical-cell factory retains all four actual operations and the original supplied cell caches. -/
private theorem packaged_physicalPrimitive_factory (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    physicalPrimitive sample retained =
      (let coefficient := sample.physicalCoefficient
       let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
       let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       let cell := Cell.withNumerator bounds retained
       ⟨⟨coefficient, rfl⟩, primitive, bounds, ⟨cell, rfl⟩⟩ : PhysicalPrimitive sample retained) := by rfl

/-- The whole physical-cell factory retains all four actual operations and the original supplied cell caches. -/
theorem physicalPrimitive_factory (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    physicalPrimitive sample retained =
      (let coefficient := sample.physicalCoefficient
       let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
       let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       let cell := Cell.withNumerator bounds retained
       ⟨⟨coefficient, rfl⟩, primitive, bounds, ⟨cell, rfl⟩⟩ : PhysicalPrimitive sample retained) :=
  packaged_physicalPrimitive_factory sample retained

namespace PhysicalPrimitive

variable {sample : PolynomialSample cap numerator index regularBox}
    {retained : Cell preparation.2.1 coordinate stage allowance nonnegative}

/-- Read the original physical cell compiled on the same supplied finite reciprocal inverse and power bank. -/
def cell (data : PhysicalPrimitive sample retained) : Cell data.2.2.1 coordinate stage allowance nonnegative :=
  data.2.2.2.val

/-- The complete returned cell is the original numerator-change factory on the supplied retained cell. -/
private theorem packaged_cell_eq (data : PhysicalPrimitive sample retained) :
    data.cell = Cell.withNumerator data.2.2.1 retained := data.2.2.2.property

/-- The complete returned cell is the original numerator-change factory on the supplied retained cell. -/
theorem cell_eq (data : PhysicalPrimitive sample retained) :
    data.cell = Cell.withNumerator data.2.2.1 retained := packaged_cell_eq data

/-- The whole physical primitive cell retains the same complete original finite reciprocal inverse model. -/
theorem cell_inverse (data : PhysicalPrimitive sample retained) : data.cell.inverse = retained.inverse :=
  (congrArg (fun value : Cell data.2.2.1 coordinate stage allowance nonnegative => value.inverse)
    data.cell_eq).trans (Cell.withNumerator_inverse data.2.2.1 retained)

/-- The whole physical primitive cell retains the same complete original finite reciprocal cube polynomial. -/
theorem cell_cube (data : PhysicalPrimitive sample retained) : data.cell.powers.cube = retained.powers.cube :=
  (congrArg (fun value : Cell data.2.2.1 coordinate stage allowance nonnegative => value.powers.cube)
    data.cell_eq).trans (Cell.withNumerator_cube data.2.2.1 retained)

/-- The whole physical primitive density retains its actual new coefficient and the same original cube. -/
theorem cell_density (data : PhysicalPrimitive sample retained) :
    data.cell.density = data.2.2.1.coefficient.scale half * retained.powers.cube :=
  (congrArg (fun value : Cell data.2.2.1 coordinate stage allowance nonnegative => value.density)
    data.cell_eq).trans (Cell.withNumerator_density data.2.2.1 retained)

/-- The actual cell's finite primitive increment has its original internally derived residual-model budget. -/
theorem integral_error_le (data : PhysicalPrimitive sample retained)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish) :
    Norm.Basic.normSq (data.cell.value.eval finish - data.cell.value.eval start -
      data.cell.pullback.model.integralSample) ≤
      quarterRadius (2 * Norm.Basic.normSq coordinate.displacement * data.2.2.1.scale) stage :=
  data.cell.integral_error_le startInside finishInside

/-- The actual regular-remainder numerator is twice the original signed w coefficient. -/
def regularNumerator : Polynomial := (wRemainder (parameter := parameter)).scale 2

/-- The actual regular primitive coefficient retains both finite P-model residuals on the original q owner.

The supplied parity sample has numerator -2*lambda*w. Its actual physical
cell therefore differs from the original regular w remainder by the stated
square and differential residuals of that same retained regular inverse.
-/
theorem regular_coefficient_residual
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained) (point : Gaussian) :
    half * data.2.2.1.coefficient.eval point -
        ((wRemainder (parameter := parameter)) *
          HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point =
      half * point * cap.polynomial.eval point *
        (regular.shiftedFactor.eval point * differentialResidual cap.polynomial regular.1.val.value point -
          (regularNumerator (parameter := parameter)).eval point * regular.1.val.residual.eval point) := by
  have coefficient := data.2.2.1.coefficient_eq point
  have factor := data.2.2.1.factor_eq
  have one : (0 : Gaussian) + 1 = 1 := by ring1
  have actualFactor : data.2.2.1.factor = 1 := factor.trans one
  have value := congrArg (fun polynomial : Polynomial => polynomial.eval point) data.1.property
  have derivative := congrArg (fun polynomial : Polynomial => (Derivative.derivative polynomial).eval point)
    data.1.property
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide +kernel
  have source : half * data.2.2.1.coefficient.eval point =
      (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
        (Derivative.derivative regular.physicalCoefficient).eval point -
      half * regular.physicalCoefficient.eval point *
        (Derivative.derivative (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))).eval point := by
    rewrite [coefficient, actualFactor, value, derivative]
    calc
      _ = (2 * half) *
          ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
            (Derivative.derivative regular.physicalCoefficient).eval point) -
          half * regular.physicalCoefficient.eval point *
            (Derivative.derivative (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))).eval point := by ring1
      _ = _ := by rewrite [twiceHalf, Basic.one_mul]; rfl
  have radicand : (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point =
      point * cap.polynomial.eval point := by
    rewrite [radicand_eq (frame := frame) (cap := cap), eval_shift, pow_one]
    ring1
  have radicandDerivative := congrArg (fun polynomial : Polynomial =>
    (Derivative.derivative polynomial).eval point) (radicand_eq (frame := frame) (cap := cap))
  have originalDerivative := radicandDerivative.trans (Derivative.eval_derivative_shift_one cap.polynomial point)
  have target : half * point * (regularNumerator (parameter := parameter)).eval point * cap.polynomial.eval point =
      ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point := by
    unfold regularNumerator
    rewrite [eval_scale, eval_mul, radicand]
    calc
      _ = (2 * half) * (wRemainder (parameter := parameter)).eval point *
          (point * cap.polynomial.eval point) := by ring1
      _ = _ := by rewrite [twiceHalf, Basic.one_mul]; rfl
  calc
    _ = point * cap.polynomial.eval point * (Derivative.derivative regular.physicalCoefficient).eval point -
        half * (cap.polynomial.eval point + point * (Derivative.derivative cap.polynomial).eval point) *
          regular.physicalCoefficient.eval point -
        half * point * (regularNumerator (parameter := parameter)).eval point * cap.polynomial.eval point := by
      rewrite [source, radicand, originalDerivative, target]
      ring1
    _ = _ := regular.physicalCoefficient_residual point

/-- The exact coefficient difference between the new physical primitive cell and the original signed remainder. -/
def regularDifference
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained) : Polynomial :=
  data.2.2.1.coefficient.scale half -
    (wRemainder (parameter := parameter)) * HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)

/-- The retained coefficient difference has the same finite regular-model residual readback. -/
private theorem packaged_regularDifference_eval
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained) (point : Gaussian) :
    (regularDifference regular data).eval point =
      half * point * cap.polynomial.eval point *
        (regular.shiftedFactor.eval point * differentialResidual cap.polynomial regular.1.val.value point -
          (regularNumerator (parameter := parameter)).eval point * regular.1.val.residual.eval point) := by
  unfold regularDifference
  rewrite [eval_sub, eval_scale]
  exact regular_coefficient_residual regular data point

/-- The retained coefficient difference has the same finite regular-model residual readback. -/
theorem regularDifference_eval
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained) (point : Gaussian) :
    (regularDifference regular data).eval point =
      half * point * cap.polynomial.eval point *
        (regular.shiftedFactor.eval point * differentialResidual cap.polynomial regular.1.val.value point -
          (regularNumerator (parameter := parameter)).eval point * regular.1.val.residual.eval point) :=
  packaged_regularDifference_eval regular data point

/-- The two actual pullbacks differ by their retained coefficient difference times the SAME original cube.

This polynomial identity holds at every supplied scalar parameter. It
retains both original pullback tables and their common spatial coordinate;
no box containment, endpoint observation or integral comparison is assumed.
-/
private theorem packaged_regular_point_difference
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) (input : Coordinate) :
    Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩ =
      (regularDifference regular data).eval (coordinate.point input) *
        retained.powers.cube.eval (coordinate.point input) := by
  let point := coordinate.point input
  have first := data.cell.pullback.eval_point input
  have last := cells.2.val.eval_point input
  have density := congrArg (fun polynomial : Polynomial => polynomial.eval point) data.cell_density
  rewrite [eval_mul, eval_scale] at density
  have target := congrArg (fun polynomial : Polynomial => polynomial.eval point) tables.2.property
  rewrite [eval_mul] at target
  have difference : (regularDifference regular data).eval point =
      half * data.2.2.1.coefficient.eval point -
        ((wRemainder (parameter := parameter)) *
          HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point := by
    unfold regularDifference
    rewrite [eval_sub, eval_scale]
    rfl
  have scalar :
      Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩ =
      (regularDifference regular data).eval point * retained.powers.cube.eval point :=
    (congrArg₂ (· - ·) first last).trans
      ((congrArg₂ (· - ·) density target).trans (by rewrite [difference]; ring1))
  exact scalar

/-- The two actual pullbacks differ by their retained coefficient difference times the SAME original cube. -/
theorem regular_point_difference
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) (input : Coordinate) :
    Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩ =
      (regularDifference regular data).eval (coordinate.point input) *
        retained.powers.cube.eval (coordinate.point input) :=
  packaged_regular_point_difference regular data tables cells input

/-- Compute an actual finite ceiling from the same residual coefficient, original cube and reciprocal source box. -/
def regularDifferenceBound
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained) : Coordinate :=
  Bounds.Box.denseEvalNormBound (regularDifference regular data)
      terminal.neighborhood.patch.base.box *
    Bounds.Box.denseEvalNormBound retained.powers.cube
      terminal.neighborhood.patch.base.box

/-- The actual two physical models differ by their same-cube coefficient difference at each original parameter. -/
private theorem packaged_regular_point_difference_le
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩) ≤
      regularDifferenceBound regular data := by
  let point := coordinate.point input
  have inside := coordinate.point_inside startInside finishInside lower upper
  have scalar := regular_point_difference regular data tables cells input
  have coefficientBound := Bounds.Box.normSq_eval_le_denseEvalNormBound
    (regularDifference regular data) inside
  have cubeBound := Bounds.Box.normSq_eval_le_denseEvalNormBound
    retained.powers.cube inside
  have nonnegative := (Bounds.Box.denseHornerNormBounds_nonneg
    (regularDifference regular data) terminal.neighborhood.patch.base.box).1
  have product := Arithmetic.mul_le_mul_direct coefficientBound cubeBound
    (Norm.Basic.normSq_nonneg _) nonnegative
  unfold regularDifferenceBound
  exact (congrArg Norm.Basic.normSq scalar).trans_le ((Norm.Basic.normSq_mul _ _).trans_le product)

/-- The actual two physical models retain their internally computed same-cube bound at every original parameter. -/
theorem regular_point_difference_le
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩) ≤
      regularDifferenceBound regular data :=
  packaged_regular_point_difference_le regular data tables cells startInside finishInside input lower upper

/-- The same physical primitive cell and original regular-remainder cell have their derived oriented integral bound.

Both models use the supplied coordinate and actual original reciprocal
cube. The finite coefficient ceiling is computed from those retained data;
no desired estimate, sample equality or closed-integral premise is supplied.
-/
theorem regular_integral_difference_le
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (data : PhysicalPrimitive regular retained)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish) :
    Norm.Basic.normSq (data.cell.pullback.model.integralSample - cells.2.val.model.integralSample) ≤
      2 * regularDifferenceBound regular data * Norm.Basic.normSq coordinate.displacement := by
  have estimate := Primitive.integral_difference_le data.cell.pullback.model cells.2.val.model
    (data.cell.pullback.start_eq.trans cells.2.val.start_eq.symm)
    (data.cell.pullback.finish_eq.trans cells.2.val.finish_eq.symm)
    (regularDifferenceBound regular data) (by
      intro input inside
      exact regular_point_difference_le regular data tables cells startInside finishInside input inside.1 inside.2)
  have displacement := congrArg (fun value : Gaussian =>
    2 * regularDifferenceBound regular data * Norm.Basic.normSq value) data.cell.pullback.displacement_eq
  exact estimate.trans_eq displacement

end PhysicalPrimitive

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

end
