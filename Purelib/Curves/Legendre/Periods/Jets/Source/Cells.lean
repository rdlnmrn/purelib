module

public import Purelib.Curves.Legendre.Periods.Jets.Source
public import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Shared Legendre source coefficients on original integration cells

The six original differential channels consume one retained spatial
coordinate and one selected inverse-model cache. The three relation cells
are formed from those exact local coefficient tables before integration.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Curves.Legendre.PicardFuchs

/-- The original first connection row in the retained ascending local coefficient tables. -/
@[expose] def zeroLocal (parameter : Canonical) (valueZero valueOne firstZero : CoefficientPolynomial) :
    CoefficientPolynomial :=
  Arithmetic.add (Arithmetic.scale (Clearance.connectionDenominator parameter) firstZero)
    (Arithmetic.add (Arithmetic.scale (-parameter) valueZero) valueOne)

/-- The original second connection row in the retained ascending local coefficient tables. -/
@[expose] def oneLocal (parameter : Canonical) (valueZero valueOne firstOne : CoefficientPolynomial) :
    CoefficientPolynomial :=
  Arithmetic.add (Arithmetic.scale (Clearance.connectionDenominator parameter) firstOne)
    (Arithmetic.add (Arithmetic.scale (-parameter) valueZero) (Arithmetic.scale parameter valueOne))

/-- The original scalar equation in the retained ascending local coefficient tables. -/
@[expose] def scalarLocal (parameter : Canonical) (valueZero firstZero secondZero : CoefficientPolynomial) :
    CoefficientPolynomial :=
  Arithmetic.add (Arithmetic.add (Arithmetic.scale (4 * parameter * (1 - parameter)) secondZero)
    (Arithmetic.scale (4 * (1 - 2 * parameter)) firstZero)) (Arithmetic.scale (-1) valueZero)

set_option genInjectivity false in
/-- The six actual polynomial cells and three relation cells sharing one original selected source cache.

The shared coordinate is retained once. Each differential pullback consumes
its exact coefficient from the original selected model. Relation cells use
the same six retained local tables, so their integrals are the displayed
linear combinations of those original cell integral samples. -/
structure CellModels {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
    {floor : Nat} {target : Rational} (request : Request cache floor target)
    (start finish : Canonical) (allowance : Rational) where
  /-- The shared original segment coordinate cache. -/
  coordinate : Spatial.Coordinate start finish
  /-- The first original value-channel pullback. -/
  valueZero : Spatial.Pullback coordinate request.models.valueZero allowance
  /-- The second original value-channel pullback. -/
  valueOne : Spatial.Pullback coordinate request.models.valueOne allowance
  /-- The first original first-derivative-channel pullback. -/
  firstZero : Spatial.Pullback coordinate request.models.firstZero allowance
  /-- The second original first-derivative-channel pullback. -/
  firstOne : Spatial.Pullback coordinate request.models.firstOne allowance
  /-- The first original second-derivative-channel pullback. -/
  secondZero : Spatial.Pullback coordinate request.models.secondZero allowance
  /-- The second original second-derivative-channel pullback. -/
  secondOne : Spatial.Pullback coordinate request.models.secondOne allowance
  /-- The retained first original relation cell. -/
  zero : Basic.CellModel
  /-- This relation cell consumes exactly the original retained value and first local tables. -/
  zero_eq : zero = Basic.CellModel.exact start finish
    (zeroLocal parameter valueZero.ascending valueOne.ascending firstZero.ascending)
  /-- The retained second original relation cell. -/
  one : Basic.CellModel
  /-- This relation cell consumes exactly the original retained value and weighted first local tables. -/
  one_eq : one = Basic.CellModel.exact start finish
    (oneLocal parameter valueZero.ascending valueOne.ascending firstOne.ascending)
  /-- The retained original scalar relation cell. -/
  scalar : Basic.CellModel
  /-- This relation cell consumes the original retained zero-coordinate second, first and value local tables. -/
  scalar_eq : scalar = Basic.CellModel.exact start finish
    (scalarLocal parameter valueZero.ascending firstZero.ascending secondZero.ascending)

constructive_injectivity CellModels

namespace CellModels

open Purelib.Approximation.Rational.Geometric
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

variable {parameter : Canonical} {count : Nat}
  {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
  {floor : Nat} {target : Rational} {request : Request cache floor target}
  {start finish : Canonical} {allowance : Rational}

/-- Select one of the six identical retained physical cells in value, first and second differential order.

This finite view reads the original pullback model fields. It performs no
source selection, coordinate construction or polynomial evaluation.
-/
@[expose] def cell (models : CellModels request start finish allowance) : Fin 6 → Basic.CellModel :=
  Fin.cases models.valueZero.model (Fin.cases models.valueOne.model
    (Fin.cases models.firstZero.model (Fin.cases models.firstOne.model
      (Fin.cases models.secondZero.model (Fin.cases models.secondOne.model Fin.elim0)))))

/-- Every selected original physical cell starts at the same original source coordinate. -/
theorem cell_start (models : CellModels request start finish allowance) (index : Fin 6) :
    (models.cell index).start = start := by
  refine Fin.cases models.valueZero.start_eq ?_ index
  intro index
  refine Fin.cases models.valueOne.start_eq ?_ index
  intro index
  refine Fin.cases models.firstZero.start_eq ?_ index
  intro index
  refine Fin.cases models.firstOne.start_eq ?_ index
  intro index
  refine Fin.cases models.secondZero.start_eq ?_ index
  intro index
  exact Fin.cases models.secondOne.start_eq (fun index => Fin.elim0 index) index

/-- Every selected original physical cell finishes at the same original target coordinate. -/
theorem cell_finish (models : CellModels request start finish allowance) (index : Fin 6) :
    (models.cell index).finish = finish := by
  refine Fin.cases models.valueZero.finish_eq ?_ index
  intro index
  refine Fin.cases models.valueOne.finish_eq ?_ index
  intro index
  refine Fin.cases models.firstZero.finish_eq ?_ index
  intro index
  refine Fin.cases models.firstOne.finish_eq ?_ index
  intro index
  refine Fin.cases models.secondZero.finish_eq ?_ index
  intro index
  exact Fin.cases models.secondOne.finish_eq (fun index => Fin.elim0 index) index

/-- Every original selected physical cell evaluates its point in the SAME retained shared spatial coordinate. -/
theorem cell_point (models : CellModels request start finish allowance) (index : Fin 6) (input : Rational) :
    (models.cell index).point input = models.coordinate.point input := by
  unfold Basic.CellModel.point Basic.CellModel.displacement
  rewrite [models.cell_start index, models.cell_finish index, models.coordinate.point_eq]
  rfl

/-- Every selected original cell retains its same original local allowance. -/
theorem cell_allowance (models : CellModels request start finish allowance) (index : Fin 6) :
    (models.cell index).localAllowance = allowance := by
  refine Fin.cases models.valueZero.allowance_eq ?_ index
  intro index
  refine Fin.cases models.valueOne.allowance_eq ?_ index
  intro index
  refine Fin.cases models.firstZero.allowance_eq ?_ index
  intro index
  refine Fin.cases models.firstOne.allowance_eq ?_ index
  intro index
  refine Fin.cases models.secondZero.allowance_eq ?_ index
  intro index
  exact Fin.cases models.secondOne.allowance_eq (fun index => Fin.elim0 index) index

/-- Each actual selected spatial integral is the endpoint increment of its same retained Source primitive.

The original pullback table, shared coordinate, allowance and Request are
unchanged. The original dense-primitive derivative certificate and actual
coefficient readback supply the existing exact pullback integral theorem;
no endpoint value, root, model or comparison is reconstructed.
-/
theorem cell_integralSample_primitive (models : CellModels request start finish allowance) (channel : Fin 6) :
    (models.cell channel).integralSample =
      (request.primitive channel).primitive.value.eval finish -
        (request.primitive channel).primitive.value.eval start := by
  have derivative (index : Fin 6) (point : Canonical) :
      (Polynomial.Dense.Gaussian.GCD.derivative (request.primitive index).primitive.value).eval point =
        (request.models.coefficient index).eval point :=
    ((request.primitive index).primitive.derivative_eq point).trans
      (congrArg (fun polynomial => polynomial.eval point) (request.primitive_coefficient index))
  refine Fin.cases (models.valueZero.integralSample_primitive _ (derivative 0)) ?_ channel
  intro channel
  refine Fin.cases (models.valueOne.integralSample_primitive _ (derivative 1)) ?_ channel
  intro channel
  refine Fin.cases (models.firstZero.integralSample_primitive _ (derivative 2)) ?_ channel
  intro channel
  refine Fin.cases (models.firstOne.integralSample_primitive _ (derivative 3)) ?_ channel
  intro channel
  refine Fin.cases (models.secondZero.integralSample_primitive _ (derivative 4)) ?_ channel
  intro channel
  exact Fin.cases (models.secondOne.integralSample_primitive _ (derivative 5)) (fun index => Fin.elim0 index) channel

/-- An actual retained pair selection bounds each original spatial cell difference across its two model patches.

The same channel fixes its scaled numerator and odd-power index. The
supplied original edge retains the signed root relation, and both actual
Source selections cover the same cached pair payment. No coefficient,
primitive or polynomial cell is rebuilt by this comparison proof.
-/
theorem pair_integral_difference_lt
    {otherCount otherFloor : Nat} {otherTarget : Rational}
    {otherPatch : ContinuedNeighborhood (Paths.polynomial parameter) otherCount}
    {otherCache : Cache otherPatch} {otherRequest : Request otherCache otherFloor otherTarget}
    {otherAllowance : Rational} (first : CellModels request start finish allowance)
    (last : CellModels otherRequest start finish otherAllowance) (channel : Fin 6)
    (budget : PrimitivePairBudget patch otherPatch
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale) start finish
      (Specification.Table.forms parameter channel).denominatorPairs)
    {current : Nat} {tolerance : Rational} (selection : Search.Selection budget.scale current tolerance)
    (edge : EdgeTransition (patch.base.refine request.selection.stage)
      (otherPatch.base.refine otherRequest.selection.stage) start finish)
    (unflipped : edge.sample.alignment.flip = false)
    (firstLater : selection.stage ≤ request.selection.stage)
    (lastLater : selection.stage ≤ otherRequest.selection.stage) :
    Data.Gaussian.Norm.Basic.normSq
      ((first.cell channel).integralSample - (last.cell channel).integralSample) < tolerance := by
  rewrite [first.cell_integralSample_primitive, last.cell_integralSample_primitive,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  have same :
      ((request.primitive channel).primitive.value.eval finish -
        (request.primitive channel).primitive.value.eval start) -
        ((otherRequest.primitive channel).primitive.value.eval finish -
          (otherRequest.primitive channel).primitive.value.eval start) =
      (request.primitive channel).primitive.value.eval finish -
        (request.primitive channel).primitive.value.eval start +
        ((otherRequest.primitive channel).primitive.value.eval start -
          (otherRequest.primitive channel).primitive.value.eval finish) := by ring1
  rewrite [same]
  exact budget.selected_increment_lt selection (request.primitive channel)
    (otherRequest.primitive channel) edge unflipped firstLater lastLater

/-- Compile all six original coefficient caches once along one retained segment coordinate.

The three relation cells are then computed from the actual six ascending
tables. Their zero allowance concerns these exact polynomial combinations;
the original differential cells retain the supplied admission allowance. -/
@[expose] def build (request : Request cache floor target) (start finish : Canonical)
    (allowance : Rational) (nonnegative : 0 ≤ allowance) : CellModels request start finish allowance :=
  let coordinate := Spatial.Coordinate.build start finish
  let valueZero := Spatial.Pullback.build coordinate request.models.valueZero allowance nonnegative
  let valueOne := Spatial.Pullback.build coordinate request.models.valueOne allowance nonnegative
  let firstZero := Spatial.Pullback.build coordinate request.models.firstZero allowance nonnegative
  let firstOne := Spatial.Pullback.build coordinate request.models.firstOne allowance nonnegative
  let secondZero := Spatial.Pullback.build coordinate request.models.secondZero allowance nonnegative
  let secondOne := Spatial.Pullback.build coordinate request.models.secondOne allowance nonnegative
  let zero := Basic.CellModel.exact start finish
    (zeroLocal parameter valueZero.ascending valueOne.ascending firstZero.ascending)
  let one := Basic.CellModel.exact start finish
    (oneLocal parameter valueZero.ascending valueOne.ascending firstOne.ascending)
  let scalar := Basic.CellModel.exact start finish
    (scalarLocal parameter valueZero.ascending firstZero.ascending secondZero.ascending)
  ⟨coordinate, valueZero, valueOne, firstZero, firstOne, secondZero, secondOne, zero, rfl, one, rfl, scalar, rfl⟩

/-- The first original relation cell reads the same cached spatial connection row. -/
theorem zero_eval (models : CellModels request start finish allowance) (input : Canonical) :
    Evaluation.eval models.zero.polynomial input =
      request.rows.zero.eval (start + input * (finish - start)) := by
  rw [models.zero_eq]
  change Evaluation.eval (zeroLocal parameter models.valueZero.ascending models.valueOne.ascending
    models.firstZero.ascending) input = _
  rw [zeroLocal, Evaluation.eval_add, Evaluation.eval_add, Evaluation.eval_scale, Evaluation.eval_scale,
    ← models.firstZero.polynomial_eq, ← models.valueZero.polynomial_eq, ← models.valueOne.polynomial_eq,
    models.firstZero.eval_local, models.valueZero.eval_local, models.valueOne.eval_local, request.rows.zero_eval]
  ring1

/-- The second original relation cell reads the same cached spatial connection row. -/
theorem one_eval (models : CellModels request start finish allowance) (input : Canonical) :
    Evaluation.eval models.one.polynomial input =
      request.rows.one.eval (start + input * (finish - start)) := by
  rw [models.one_eq]
  change Evaluation.eval (oneLocal parameter models.valueZero.ascending models.valueOne.ascending
    models.firstOne.ascending) input = _
  rw [oneLocal, Evaluation.eval_add, Evaluation.eval_add, Evaluation.eval_scale, Evaluation.eval_scale,
    Evaluation.eval_scale, ← models.firstOne.polynomial_eq, ← models.valueZero.polynomial_eq,
    ← models.valueOne.polynomial_eq, models.firstOne.eval_local, models.valueZero.eval_local,
    models.valueOne.eval_local, request.rows.one_eval]
  ring1

/-- The original scalar relation cell reads the same cached spatial equation coefficient. -/
theorem scalar_eval (models : CellModels request start finish allowance) (input : Canonical) :
    Evaluation.eval models.scalar.polynomial input =
      request.rows.scalar.eval (start + input * (finish - start)) := by
  rw [models.scalar_eq]
  change Evaluation.eval (scalarLocal parameter models.valueZero.ascending models.firstZero.ascending
    models.secondZero.ascending) input = _
  rw [scalarLocal, Evaluation.eval_add, Evaluation.eval_add, Evaluation.eval_scale, Evaluation.eval_scale,
    Evaluation.eval_scale, ← models.secondZero.polynomial_eq, ← models.firstZero.polynomial_eq,
    ← models.valueZero.polynomial_eq, models.secondZero.eval_local, models.firstZero.eval_local,
    models.valueZero.eval_local, request.rows.scalar_eval]
  ring1

/-- The first original relation cell integrates the displayed linear combination of the same original channel cells. -/
theorem zero_integralSample (models : CellModels request start finish allowance) :
    models.zero.integralSample = Clearance.connectionDenominator parameter * models.firstZero.model.integralSample -
      (parameter * models.valueZero.model.integralSample - models.valueOne.model.integralSample) := by
  rw [models.zero_eq, Basic.CellModel.exact_integralSample, zeroLocal, Integral.definiteIntegral_add,
    Integral.definiteIntegral_add, Integral.definiteIntegral_scale, Integral.definiteIntegral_scale,
    models.firstZero.integralSample_eq, models.valueZero.integralSample_eq, models.valueOne.integralSample_eq]
  ring1

/-- The second original relation cell integrates the displayed linear combination of the same original channel cells. -/
theorem one_integralSample (models : CellModels request start finish allowance) :
    models.one.integralSample = Clearance.connectionDenominator parameter * models.firstOne.model.integralSample -
      (parameter * models.valueZero.model.integralSample - parameter * models.valueOne.model.integralSample) := by
  rw [models.one_eq, Basic.CellModel.exact_integralSample, oneLocal, Integral.definiteIntegral_add,
    Integral.definiteIntegral_add, Integral.definiteIntegral_scale, Integral.definiteIntegral_scale,
    Integral.definiteIntegral_scale, models.firstOne.integralSample_eq, models.valueZero.integralSample_eq,
    models.valueOne.integralSample_eq]
  ring1

/-- The original scalar relation cell integrates the displayed second, first and value channel combination. -/
theorem scalar_integralSample (models : CellModels request start finish allowance) :
    models.scalar.integralSample = 4 * parameter * (1 - parameter) * models.secondZero.model.integralSample +
      4 * (1 - 2 * parameter) * models.firstZero.model.integralSample - models.valueZero.model.integralSample := by
  rw [models.scalar_eq, Basic.CellModel.exact_integralSample, scalarLocal, Integral.definiteIntegral_add,
    Integral.definiteIntegral_add, Integral.definiteIntegral_scale, Integral.definiteIntegral_scale,
    Integral.definiteIntegral_scale, models.secondZero.integralSample_eq, models.firstZero.integralSample_eq,
    models.valueZero.integralSample_eq]
  ring1

end CellModels

end Purelib.Curves.Legendre.Periods.Jets.Source

end
