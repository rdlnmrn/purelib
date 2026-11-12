module

public import Purelib.Curves.Legendre.Periods.Jets.Models
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Normalization.InverseModelRemainderBounds
public import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original regular-chart sources for synchronized Legendre differential models

A regular chart retains one original continued inverse-root owner. Its
shared derivative and residual caches construct the numerical defect
budgets for both connection rows and the scalar equation. A finite request
selects one original Newton stage before constructing the same six
polynomial coefficient channels and all three residual tables.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open InverseModelDerivativeBounds (DerivativeBounds)
open InverseModelDifferentialResidual (DifferentialResidualBounds)
open InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open InverseModelPrimitiveResidual (PrimitiveResidualBounds)
open InverseModelRemainderBounds (RemainderBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Readings
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric

set_option genInjectivity false in
/-- The shared regular-chart clearance, derivative and residual caches for all original Legendre differential relations.

The original continued neighborhood and its initial Newton model remain
indexed. Each row retains the original exact reduction and cached source
budgets. The scalar weighted cubic discrepancy uses its original displayed
coefficient, and the common scale pays all three actual relation bounds. -/
structure Cache {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) where
  /-- The retained original seeded-neighborhood polynomial clearance. -/
  clearance : RegionClearance (Paths.polynomial parameter) patch.base.box
  /-- The clearance is the original source-neighborhood construction. -/
  clearance_eq : clearance = SeededPrimitiveBounds.clearance patch.base
  /-- The shared uniform derivative and inverse-value ceilings on that exact initial source model. -/
  root : DerivativeBounds clearance patch.base.model
  /-- The shared initial differential residual and its finite norm ceiling. -/
  residual : DifferentialResidualBounds patch.base.model
  /-- The original first connection reduction retained once. -/
  zeroReduction : Connection.ConnectionReduction parameter
  /-- The retained first reduction belongs to the original canonical first row. -/
  zeroReduction_eq : zeroReduction = Connection.firstConnectionReduction parameter
  /-- The first original primitive's numerator and derivative ceilings. -/
  zeroPrimitive : PrimitiveDerivativeBounds root zeroReduction.primitiveNumerator
  /-- The first original primitive's exact cleared coefficient and source-derived mismatch budget. -/
  zeroDelta : PrimitiveResidualBounds root residual zeroPrimitive 0
  /-- The first original basis coefficient's source-derived square-residual budget. -/
  zeroRemainder : RemainderBounds root zeroReduction.basisNumerator
  /-- The original second connection reduction retained once. -/
  oneReduction : Connection.ConnectionReduction parameter
  /-- The retained second reduction belongs to the original canonical second row. -/
  oneReduction_eq : oneReduction = Connection.secondConnectionReduction parameter
  /-- The second original primitive's numerator and derivative ceilings. -/
  onePrimitive : PrimitiveDerivativeBounds root oneReduction.primitiveNumerator
  /-- The second original primitive's cleared coefficient and source-derived mismatch budget. -/
  oneDelta : PrimitiveResidualBounds root residual onePrimitive 0
  /-- The second original basis coefficient's source-derived square-residual budget. -/
  oneRemainder : RemainderBounds root oneReduction.basisNumerator
  /-- The original scalar Picard–Fuchs reduction retained once. -/
  scalarReduction : Residual.PicardFuchsReduction parameter
  /-- The retained scalar reduction is the original canonical scalar row. -/
  scalarReduction_eq : scalarReduction = Residual.picardFuchsReduction parameter
  /-- The original scalar primitive's numerator and derivative ceilings. -/
  scalarPrimitive : PrimitiveDerivativeBounds root scalarReduction.primitiveNumerator
  /-- The original scalar primitive's cleared coefficient and source-derived cube mismatch budget. -/
  scalarDelta : PrimitiveResidualBounds root residual scalarPrimitive 2
  /-- The retained weighted coefficient of the scalar cubic square-residual discrepancy. -/
  scalarCoefficient : InverseRootPolynomial.Polynomial
  /-- The scalar discrepancy coefficient is the original weighted first differential numerator. -/
  scalarCoefficient_eq : scalarCoefficient = Polynomials.basePolynomial.scale (2 * (1 - 2 * parameter))
  /-- The scalar discrepancy's original source-derived cubic remainder budget. -/
  scalarRemainder : RemainderBounds root scalarCoefficient
  /-- The cached common geometric scale for the three original relation defects. -/
  scale : Rational
  /-- The scale is the sum of the actual two connection and one scalar defect budgets. -/
  scale_eq : scale = zeroRemainder.connectionScale zeroDelta + oneRemainder.connectionScale oneDelta +
    scalarRemainder.scalarScale scalarDelta

constructive_injectivity Cache

namespace Cache

variable {parameter : Canonical} {count : Nat}
  {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}

/-- Construct all three original relation budgets from one retained continued inverse-root neighborhood.

The shared derivative and differential-residual caches are built once. Each
fixed numerator and discrepancy coefficient is evaluated into one retained
budget, and their computed scales are summed before any Newton request. -/
@[expose] def ofPatch (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) : Cache patch :=
  let clearance := SeededPrimitiveBounds.clearance patch.base
  let root := DerivativeBounds.build clearance patch.base.model
  let residual := DifferentialResidualBounds.build patch.base.model
  let zeroReduction := Connection.firstConnectionReduction parameter
  let zeroPrimitive := PrimitiveDerivativeBounds.build root zeroReduction.primitiveNumerator
  let zeroDelta := PrimitiveResidualBounds.build root residual zeroPrimitive 0
  let zeroRemainder := RemainderBounds.build root zeroReduction.basisNumerator
  let oneReduction := Connection.secondConnectionReduction parameter
  let onePrimitive := PrimitiveDerivativeBounds.build root oneReduction.primitiveNumerator
  let oneDelta := PrimitiveResidualBounds.build root residual onePrimitive 0
  let oneRemainder := RemainderBounds.build root oneReduction.basisNumerator
  let scalarReduction := Residual.picardFuchsReduction parameter
  let scalarPrimitive := PrimitiveDerivativeBounds.build root scalarReduction.primitiveNumerator
  let scalarDelta := PrimitiveResidualBounds.build root residual scalarPrimitive 2
  let scalarCoefficient := Polynomials.basePolynomial.scale (2 * (1 - 2 * parameter))
  let scalarRemainder := RemainderBounds.build root scalarCoefficient
  let scale := zeroRemainder.connectionScale zeroDelta + oneRemainder.connectionScale oneDelta +
    scalarRemainder.scalarScale scalarDelta
  ⟨clearance, rfl, root, residual, zeroReduction, rfl, zeroPrimitive, zeroDelta, zeroRemainder,
    oneReduction, rfl, onePrimitive, oneDelta, oneRemainder, scalarReduction, rfl, scalarPrimitive,
    scalarDelta, scalarCoefficient, rfl, scalarRemainder, scale, rfl⟩

/-- The original common relation-defect scale is nonnegative. -/
theorem scale_nonnegative (cache : Cache patch) : 0 ≤ cache.scale := by
  rewrite [cache.scale_eq]
  exact add_nonneg (add_nonneg (cache.zeroRemainder.connectionScale_nonnegative cache.zeroDelta)
    (cache.oneRemainder.connectionScale_nonnegative cache.oneDelta))
    (cache.scalarRemainder.scalarScale_nonnegative cache.scalarDelta)

/-- The first original connection defect scale is paid by the retained common scale. -/
theorem zeroScale_le (cache : Cache patch) : cache.zeroRemainder.connectionScale cache.zeroDelta ≤ cache.scale := by
  rewrite [cache.scale_eq]
  exact (le_add_of_nonneg_right (cache.oneRemainder.connectionScale_nonnegative cache.oneDelta)).trans
    (le_add_of_nonneg_right (cache.scalarRemainder.scalarScale_nonnegative cache.scalarDelta))

/-- The second original connection defect scale is paid by the retained common scale. -/
theorem oneScale_le (cache : Cache patch) : cache.oneRemainder.connectionScale cache.oneDelta ≤ cache.scale := by
  rewrite [cache.scale_eq]
  exact (le_add_of_nonneg_left (cache.zeroRemainder.connectionScale_nonnegative cache.zeroDelta)).trans
    (le_add_of_nonneg_right (cache.scalarRemainder.scalarScale_nonnegative cache.scalarDelta))

/-- The original scalar defect scale is paid by the same retained common scale. -/
theorem scalarScale_le (cache : Cache patch) : cache.scalarRemainder.scalarScale cache.scalarDelta ≤ cache.scale := by
  rewrite [cache.scale_eq]
  exact le_add_of_nonneg_left (add_nonneg
    (cache.zeroRemainder.connectionScale_nonnegative cache.zeroDelta)
    (cache.oneRemainder.connectionScale_nonnegative cache.oneDelta))

end Cache

set_option genInjectivity false in
/-- A retained finite common Newton request and the original model tables constructed at that actual selected stage.

The request uses the computed shared relation-defect budget. Only after
selecting its successful finite stage does the constructor refine the
original neighborhood model and cache the six channels and three rows. -/
structure Request {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (cache : Cache patch) (current : Nat) (target : Rational) where
  /-- The original successful finite selection from the cached common source scale. -/
  selection : Search.Selection cache.scale current target
  /-- The one original Newton model computed at the selected common stage. -/
  model : InverseRootPolynomial.Model (Paths.polynomial parameter) patch.base.box
  /-- The retained model is the selected refinement of the same original neighborhood model. -/
  model_eq : model = patch.base.refine selection.stage
  /-- All six original polynomial channels and primitives share that one retained model. -/
  models : Models.Shared model
  /-- The three residual coefficient caches consume those same original channel caches. -/
  rows : Models.Rows models

constructive_injectivity Request

namespace Cache

/-- Choose one sufficient finite original Newton stage, then compute and retain all six channels and three rows once. -/
@[expose] def request {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (cache : Cache patch) (current : Nat) (target : Rational) (positive : 0 < target) : Request cache current target :=
  let selection := Search.Selection.build cache.scale cache.scale_nonnegative current target positive
  let model := patch.base.refine selection.stage
  let models := Models.Shared.build model
  let rows := Models.Rows.build models
  ⟨selection, model, rfl, models, rows⟩

end Cache
namespace Request

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Basic.DensePolynomial
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open InverseModelPrimitiveResidual (primitiveMismatch)

variable {parameter : Canonical} {count current : Nat} {target : Rational}
  {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}

/-- The selected original six-form coefficient reads its own scaled numerator and actual model's odd power.

The readback consumes the six retained Shared fields and their existing
pointwise laws. It preserves the original form order, numerator, scale and
pair count; it asserts no coefficient equality from semantic coincidence.
-/
theorem coefficient_eval (request : Request cache current target) (channel : Fin 6) (point : Canonical) :
    (request.models.coefficient channel).eval point =
      match (Specification.Table.forms parameter channel).denominatorPairs with
      | 0 => ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale).eval point * request.model.value.eval point
      | remaining + 1 => ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale).eval point *
            request.model.value.eval point ^ (2 * (remaining + 1) + 1) := by
  refine Fin.cases ?_ ?_ channel
  · change request.models.valueZero.eval point = _
    rewrite [request.models.valueZero_eval]
    change _ = (Gaussian.Basic.constantOnePolynomial.scale 1).eval point * request.model.value.eval point
    rewrite [eval_scale, Gaussian.Evaluation.constantOnePolynomial_eval]
    ring1
  · intro channel
    refine Fin.cases ?_ ?_ channel
    · change request.models.valueOne.eval point = _
      rewrite [request.models.valueOne_eval]
      change _ = (Gaussian.Basic.coordinatePolynomial.scale 1).eval point * request.model.value.eval point
      rewrite [eval_scale, Gaussian.Evaluation.coordinatePolynomial_eval]
      ring1
    · intro channel
      refine Fin.cases ?_ ?_ channel
      · change request.models.firstZero.eval point = _
        rewrite [request.models.firstZero_eval]
        change _ = (Polynomials.basePolynomial.scale InverseRootPolynomial.half).eval point *
          request.model.value.eval point ^ 3
        rewrite [eval_scale]
        ring1
      · intro channel
        refine Fin.cases ?_ ?_ channel
        · change request.models.firstOne.eval point = _
          rewrite [request.models.firstOne_eval]
          change _ = (Polynomials.weightedBasePolynomial.scale InverseRootPolynomial.half).eval point *
            request.model.value.eval point ^ 3
          rewrite [eval_scale]
          ring1
        · intro channel
          refine Fin.cases ?_ ?_ channel
          · change request.models.secondZero.eval point = _
            rewrite [request.models.secondZero_eval]
            change _ = (Polynomials.squaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)).eval point *
              request.model.value.eval point ^ 5
            rewrite [eval_scale]
            ring1
          · intro channel
            refine Fin.cases ?_ (fun index => Fin.elim0 index) channel
            change request.models.secondOne.eval point = _
            rewrite [request.models.secondOne_eval]
            change _ = (Polynomials.weightedSquaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)).eval point *
              request.model.value.eval point ^ 5
            rewrite [eval_scale]
            ring1

/-- Construct the original polynomial primitive from one actual retained six-form source coefficient.

The same original Request supplies its actual model, stage equation, shared
power cache and coefficient table. The primitive constructor consumes that
stored table literally, while the form's scaled numerator and pair count
remain the original typed indices.
-/
def primitive (request : Request cache current target) (channel : Fin 6) :
    InverseRootPrimitive.PrimitiveModel patch request.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs :=
  InverseRootPrimitive.PrimitiveModel.ofCoefficient patch request.selection.stage
    ((Specification.Table.forms parameter channel).numerator.scale (Specification.Table.forms parameter channel).scale)
    (Specification.Table.forms parameter channel).denominatorPairs (request.models.coefficient channel)
    (fun point => by
      have compiled := request.coefficient_eval channel point
      have same := congrArg (fun model : InverseRootPolynomial.Model
        (Paths.polynomial parameter) patch.base.box => model.value.eval point) request.model_eq
      exact compiled.trans (congrArg (fun value : Canonical =>
        match (Specification.Table.forms parameter channel).denominatorPairs with
        | 0 => ((Specification.Table.forms parameter channel).numerator.scale
            (Specification.Table.forms parameter channel).scale).eval point * value
        | remaining + 1 => ((Specification.Table.forms parameter channel).numerator.scale
            (Specification.Table.forms parameter channel).scale).eval point * value ^ (2 * (remaining + 1) + 1)) same))

/-- The primitive retains exactly the actual original coefficient cache selected from this same six-form Request. -/
theorem primitive_coefficient (request : Request cache current target) (channel : Fin 6) :
    (request.primitive channel).coefficient = request.models.coefficient channel := (rfl)

/-- A retained primitive coefficient readback transports its actual derivative to the canonical positive power. -/
private theorem primitive_derivative_readback {box : InverseRootPolynomial.Box}
    (model : InverseRootPolynomial.Model (Paths.polynomial parameter) box)
    (numerator primitive : InverseRootPolynomial.Polynomial) (index : Nat)
    (readback : ∀ point, primitive.eval point = numerator.eval point * model.value.eval point ^ (index + 1))
    (point : Canonical) :
    (Derivative.derivative primitive).eval point =
      (Derivative.derivative (numerator * Power.power model.value (index + 1))).eval point := by
  have same : (primitive - numerator * Power.power model.value (index + 1)).isZero = true := by
    apply Extensionality.isZero_of_eval_eq_zero
    intro sample
    rw [eval_sub, readback sample, eval_mul, Power.eval_power]
    exact sub_self _
  exact Derivative.eval_derivative_eq_of_sub_isZero same point

/-- The original finite connection identity uses the exact same cached cleared primitive coefficient. -/
private theorem connection_defect {box : InverseRootPolynomial.Box}
    (reduction : Connection.ConnectionReduction parameter)
    (model : InverseRootPolynomial.Model (Paths.polynomial parameter) box)
    (primitive : InverseRootPolynomial.Polynomial)
    (readback : ∀ point, primitive.eval point = reduction.primitiveNumerator.eval point * model.value.eval point)
    (coefficient : InverseRootPolynomial.Polynomial)
    (coefficientReadback : ∀ point, coefficient.eval point =
      2 * (Paths.polynomial parameter).eval point * (Derivative.derivative reduction.primitiveNumerator).eval point -
        reduction.primitiveNumerator.eval point * (Derivative.derivative (Paths.polynomial parameter)).eval point)
    (point : Canonical) :
    Clearance.connectionDenominator parameter *
        (InverseRootPolynomial.half *
          (reduction.parameterDerivativeNumerator.eval point * model.value.eval point ^ 3)) -
      reduction.basisNumerator.eval point * model.value.eval point - (Derivative.derivative primitive).eval point =
    -(reduction.basisNumerator.eval point * model.value.eval point * model.residual.eval point) -
      primitiveMismatch model reduction.primitiveNumerator coefficient 0 point := by
  rw [primitive_derivative_readback model reduction.primitiveNumerator primitive 0
    (fun sample => by rw [pow_one]; exact readback sample) point]
  have identity := Models.connection_model_identity reduction model point
  have canonicalDerivative := primitive_derivative_readback model reduction.primitiveNumerator
    (reduction.primitiveNumerator * model.value) 0
    (fun sample => by rw [eval_mul, pow_one]) point
  rw [canonicalDerivative] at identity
  have coefficientEqual :
      (Algebra.Quadratic.Pair.Polynomial.Expression.oddPrimitiveNumerator
        (Paths.polynomial parameter) reduction.primitiveNumerator 0).eval point = coefficient.eval point := by
    rw [coefficientReadback point]
    simp only [Algebra.Quadratic.Pair.Polynomial.Expression.oddPrimitiveNumerator,
      eval_sub, eval_scale, eval_mul, Nat.cast_zero, mul_zero, zero_add, one_mul]
    ring1
  rw [coefficientEqual] at identity
  change _ = -(reduction.basisNumerator.eval point * model.value.eval point * model.residual.eval point) -
    ((Derivative.derivative (reduction.primitiveNumerator * Power.power model.value 1)).eval point -
      InverseRootPolynomial.half * coefficient.eval point * model.value.eval point ^ 3)
  exact identity

/-- The cached original first connection coefficient and primitive have the internally derived common source bound. -/
theorem zero_error_le (request : Request cache current target) {point : Canonical}
    (inside : patch.box.Contains point) :
    Norm.Basic.normSq
      (request.rows.zero.eval point - (Derivative.derivative request.models.primitiveZero).eval point) ≤
        Geometric.Basic.quarterRadius cache.scale request.selection.stage := by
  have pointInside := patch.box_refines.contains inside
  have bound := cache.zeroRemainder.connection_bound cache.zeroDelta request.selection.stage pointInside
  have primitiveReadback (sample : Canonical) : request.models.primitiveZero.eval sample =
      cache.zeroReduction.primitiveNumerator.eval sample * request.model.value.eval sample := by
    rw [request.models.primitiveZero_eval, cache.zeroReduction_eq]
    rfl
  have coefficientReadback (sample : Canonical) : cache.zeroDelta.coefficient.eval sample =
      2 * (Paths.polynomial parameter).eval sample *
          (Derivative.derivative cache.zeroReduction.primitiveNumerator).eval sample -
        cache.zeroReduction.primitiveNumerator.eval sample *
          (Derivative.derivative (Paths.polynomial parameter)).eval sample := by
    rw [cache.zeroDelta.coefficient_eq, cache.zeroDelta.factor_eq, Nat.cast_zero, zero_add, one_mul]
  have identity := connection_defect cache.zeroReduction request.model request.models.primitiveZero
    primitiveReadback cache.zeroDelta.coefficient coefficientReadback point
  have actual := request.rows.zero_form point
  rw [← cache.zeroReduction_eq] at actual
  rw [actual, identity]
  rw [request.model_eq, Norm.Basic.normSq_eq_canonical]
  exact bound.trans (Geometric.Basic.quarterRadius_scale_mono cache.zeroScale_le request.selection.stage)

/-- The cached original second connection coefficient and primitive share the computed common source bound. -/
theorem one_error_le (request : Request cache current target) {point : Canonical}
    (inside : patch.box.Contains point) :
    Norm.Basic.normSq
      (request.rows.one.eval point - (Derivative.derivative request.models.primitiveOne).eval point) ≤
        Geometric.Basic.quarterRadius cache.scale request.selection.stage := by
  have pointInside := patch.box_refines.contains inside
  have bound := cache.oneRemainder.connection_bound cache.oneDelta request.selection.stage pointInside
  have primitiveReadback (sample : Canonical) : request.models.primitiveOne.eval sample =
      cache.oneReduction.primitiveNumerator.eval sample * request.model.value.eval sample := by
    rw [request.models.primitiveOne_eval, cache.oneReduction_eq]
    rfl
  have coefficientReadback (sample : Canonical) : cache.oneDelta.coefficient.eval sample =
      2 * (Paths.polynomial parameter).eval sample *
          (Derivative.derivative cache.oneReduction.primitiveNumerator).eval sample -
        cache.oneReduction.primitiveNumerator.eval sample *
          (Derivative.derivative (Paths.polynomial parameter)).eval sample := by
    rw [cache.oneDelta.coefficient_eq, cache.oneDelta.factor_eq, Nat.cast_zero, zero_add, one_mul]
  have identity := connection_defect cache.oneReduction request.model request.models.primitiveOne
    primitiveReadback cache.oneDelta.coefficient coefficientReadback point
  have actual := request.rows.one_form point
  rw [← cache.oneReduction_eq] at actual
  rw [actual, identity, request.model_eq, Norm.Basic.normSq_eq_canonical]
  exact bound.trans (Geometric.Basic.quarterRadius_scale_mono cache.oneScale_le request.selection.stage)

/-- A denominator-cleared scalar primitive identity identifies the same retained half coefficient. -/
private theorem half_coefficient {E N : Canonical} (cleared : 2 * E = N) :
    InverseRootPolynomial.half * N = E := by
  have halfTwice : InverseRootPolynomial.half * (2 : Canonical) = 1 := by decide
  calc
    _ = InverseRootPolynomial.half * (2 * E) := congrArg (InverseRootPolynomial.half * ·) cleared.symm
    _ = (InverseRootPolynomial.half * 2) * E := by ring1
    _ = E := by rw [halfTwice, one_mul]

/-- Retain the scalar discrepancy while replacing the canonical primitive by its actual cached coefficient table. -/
private theorem scalar_defect {box : InverseRootPolynomial.Box}
    (model : InverseRootPolynomial.Model (Paths.polynomial parameter) box)
    (primitive : InverseRootPolynomial.Polynomial)
    (readback : ∀ point, primitive.eval point =
      Polynomials.picardFuchsPrimitivePolynomial.eval point * model.value.eval point ^ 3)
    (coefficient : InverseRootPolynomial.Polynomial)
    (coefficientReadback : ∀ point, InverseRootPolynomial.half * coefficient.eval point =
      (Residual.picardFuchsResidualPolynomial parameter).eval point)
    (point : Canonical) :
    3 * parameter * (1 - parameter) * Polynomials.baseValue point ^ 2 * model.value.eval point ^ 5 +
        2 * (1 - 2 * parameter) * Polynomials.baseValue point * model.value.eval point ^ 3 - model.value.eval point -
        (Derivative.derivative primitive).eval point =
      model.residual.eval point *
          (2 * (1 - 2 * parameter) * Polynomials.baseValue point * model.value.eval point ^ 3 -
            model.value.eval point * (2 - model.residual.eval point)) -
        primitiveMismatch model Polynomials.picardFuchsPrimitivePolynomial coefficient 2 point := by
  rw [primitive_derivative_readback model Polynomials.picardFuchsPrimitivePolynomial primitive 2 readback point]
  rw [primitiveMismatch, coefficientReadback point]
  have identity := Models.scalar_model_identity model point
  have subtractDerivative (a b c d : Canonical) (same : a - b = d) :
      a - c = d - (c - b) := by
    rw [← same]
    ring1
  exact subtractDerivative _ _ _ _ identity

/-- The cached original scalar row and primitive share the internally derived common source bound. -/
theorem scalar_error_le (request : Request cache current target) {point : Canonical}
    (inside : patch.box.Contains point) :
    Norm.Basic.normSq
      (request.rows.scalar.eval point - (Derivative.derivative request.models.scalarPrimitive).eval point) ≤
        Geometric.Basic.quarterRadius cache.scale request.selection.stage := by
  have pointInside := patch.box_refines.contains inside
  have bound := cache.scalarRemainder.scalar_bound cache.scalarDelta request.selection.stage pointInside
  have primitiveReadback := request.models.scalarPrimitive_eval
  have coefficientReadback (sample : Canonical) :
      InverseRootPolynomial.half * cache.scalarDelta.coefficient.eval sample =
        (Residual.picardFuchsResidualPolynomial parameter).eval sample := by
    have cleared := cache.scalarReduction.clearedIdentity sample
    rw [Gaussian.GCD.derivative, Gaussian.GCD.derivative] at cleared
    have sameCoefficient := cache.scalarDelta.coefficient_eq sample
    rw [cache.scalarDelta.factor_eq] at sameCoefficient
    have three : ((2 : Nat) : Canonical) + 1 = 3 := by decide
    rw [three] at sameCoefficient
    have same : 2 * cache.scalarReduction.residualNumerator.eval sample =
        cache.scalarDelta.coefficient.eval sample := by
      rw [sameCoefficient]
      calc
        _ = 2 * (Derivative.derivative cache.scalarReduction.primitiveNumerator).eval sample *
            (Paths.polynomial parameter).eval sample - 3 * cache.scalarReduction.primitiveNumerator.eval sample *
              (Derivative.derivative (Paths.polynomial parameter)).eval sample := cleared
        _ = _ := by ring1
    have result := half_coefficient same
    have residualEqual : cache.scalarReduction.residualNumerator =
        Residual.picardFuchsResidualPolynomial parameter :=
      congrArg Residual.PicardFuchsReduction.residualNumerator cache.scalarReduction_eq
    exact result.trans (congrArg (fun polynomial => polynomial.eval sample) residualEqual)
  have identity := scalar_defect request.model request.models.scalarPrimitive
    primitiveReadback cache.scalarDelta.coefficient coefficientReadback point
  have samePrimitive : cache.scalarReduction.primitiveNumerator = Polynomials.picardFuchsPrimitivePolynomial := by
    rw [cache.scalarReduction_eq]
    rfl
  have sameMismatch : primitiveMismatch (patch.base.model.refine request.selection.stage)
      cache.scalarReduction.primitiveNumerator cache.scalarDelta.coefficient 2 point =
    primitiveMismatch (patch.base.model.refine request.selection.stage)
      Polynomials.picardFuchsPrimitivePolynomial cache.scalarDelta.coefficient 2 point :=
    congrArg (fun numerator => primitiveMismatch (patch.base.model.refine request.selection.stage)
      numerator cache.scalarDelta.coefficient 2 point) samePrimitive
  rw [sameMismatch] at bound
  have sameCoefficient : cache.scalarCoefficient.eval point =
      2 * (1 - 2 * parameter) * Polynomials.baseValue point := by
    rw [cache.scalarCoefficient_eq, eval_scale, Polynomials.basePolynomial_eval]
    rfl
  rw [sameCoefficient] at bound
  rw [request.rows.scalar_form, identity, request.model_eq, Norm.Basic.normSq_eq_canonical]
  exact bound.trans (Geometric.Basic.quarterRadius_scale_mono cache.scalarScale_le request.selection.stage)

end Request

end Purelib.Curves.Legendre.Periods.Jets.Source
