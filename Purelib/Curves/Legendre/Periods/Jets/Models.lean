module

public import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Polynomial.Dense.Power
public import Purelib.Curves.Legendre.PicardFuchs.Connection
public import Purelib.Curves.Legendre.PicardFuchs.Residual
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Shared finite polynomial models for the six Legendre differential channels

One inverse-root model owns all six integrands and the three algebraic
primitive approximations. The retained square, cube and fifth power are
shared before any channel is formed. Each readback concerns the original
polynomial model, including its actual residual, rather than an exact root.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Models

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial Box half)
open Purelib.Polynomial.Dense
open Basic.DensePolynomial
open Purelib.Curves.Legendre.PicardFuchs

set_option genInjectivity false in
/-- The original inverse-root model's six differential channels and three primitive coefficient caches.

All odd powers share the same retained multiplication cache. The first and
second channels are finite polynomial models of parameter-differential
integrands; they do not assert differentiation of a moving-cycle period. -/
structure Shared {parameter : Canonical} {box : Box} (model : Model (Paths.polynomial parameter) box) where
  /-- The same model's shared square, cube and fifth power. -/
  powers : Power.OddPowers model.value
  /-- The cached unweighted value differential. -/
  valueZero : Polynomial
  /-- The original unweighted coefficient is the model itself. -/
  valueZero_eq : valueZero = model.value
  /-- The cached coordinate-weighted value differential. -/
  valueOne : Polynomial
  /-- The weighted value consumes the same original model. -/
  valueOne_eq : valueOne = Gaussian.Basic.coordinatePolynomial * model.value
  /-- The cached unweighted first parameter-differential channel. -/
  firstZero : Polynomial
  /-- The unweighted first channel consumes the retained original cube. -/
  firstZero_eq : firstZero = (Polynomials.basePolynomial * powers.cube).scale half
  /-- The cached coordinate-weighted first parameter-differential channel. -/
  firstOne : Polynomial
  /-- The weighted first channel consumes the retained original cube. -/
  firstOne_eq : firstOne = (Polynomials.weightedBasePolynomial * powers.cube).scale half
  /-- The cached unweighted second parameter-differential channel. -/
  secondZero : Polynomial
  /-- The unweighted second channel consumes the retained original fifth power. -/
  secondZero_eq : secondZero = (Polynomials.squaredBasePolynomial * powers.fifth).scale ⟨3 / 4, 0⟩
  /-- The cached coordinate-weighted second parameter-differential channel. -/
  secondOne : Polynomial
  /-- The weighted second channel consumes the retained original fifth power. -/
  secondOne_eq : secondOne = (Polynomials.weightedSquaredBasePolynomial * powers.fifth).scale ⟨3 / 4, 0⟩
  /-- The cached first connection primitive. -/
  primitiveZero : Polynomial
  /-- The first primitive consumes the same original model. -/
  primitiveZero_eq : primitiveZero = Polynomials.firstPrimitivePolynomial * model.value
  /-- The cached second connection primitive. -/
  primitiveOne : Polynomial
  /-- The second primitive consumes the same original model. -/
  primitiveOne_eq : primitiveOne = Polynomials.secondPrimitivePolynomial parameter * model.value
  /-- The cached scalar Picard–Fuchs primitive. -/
  scalarPrimitive : Polynomial
  /-- The scalar primitive consumes the same original cube. -/
  scalarPrimitive_eq : scalarPrimitive = Polynomials.picardFuchsPrimitivePolynomial * powers.cube

constructive_injectivity Shared

namespace Shared

variable {parameter : Canonical} {box : Box} {model : Model (Paths.polynomial parameter) box}

/-- Compute the shared power factors once, then retain all six original differential models and three primitives. -/
@[expose] def build (model : Model (Paths.polynomial parameter) box) : Shared model :=
  let powers := Power.OddPowers.build model.value
  let valueOne := Gaussian.Basic.coordinatePolynomial * model.value
  let firstZero := (Polynomials.basePolynomial * powers.cube).scale half
  let firstOne := (Polynomials.weightedBasePolynomial * powers.cube).scale half
  let secondZero := (Polynomials.squaredBasePolynomial * powers.fifth).scale ⟨3 / 4, 0⟩
  let secondOne := (Polynomials.weightedSquaredBasePolynomial * powers.fifth).scale ⟨3 / 4, 0⟩
  let primitiveZero := Polynomials.firstPrimitivePolynomial * model.value
  let primitiveOne := Polynomials.secondPrimitivePolynomial parameter * model.value
  let scalarPrimitive := Polynomials.picardFuchsPrimitivePolynomial * powers.cube
  ⟨powers, model.value, rfl, valueOne, rfl, firstZero, rfl, firstOne, rfl,
    secondZero, rfl, secondOne, rfl, primitiveZero, rfl, primitiveOne, rfl, scalarPrimitive, rfl⟩

/-- Select one actual retained coefficient in the original six-form order without computing another table. -/
@[expose] def coefficient (models : Shared model) : Fin 6 → Polynomial :=
  Fin.cases models.valueZero (Fin.cases models.valueOne
    (Fin.cases models.firstZero (Fin.cases models.firstOne
      (Fin.cases models.secondZero (Fin.cases models.secondOne Fin.elim0)))))

/-- Read the cached value coefficient of the original basis coordinate. -/
@[expose] def value (models : Shared model) (coordinate : Fin 2) : Polynomial :=
  if coordinate = 0 then models.valueZero else models.valueOne

/-- Read the cached first parameter-differential coefficient of the original basis coordinate. -/
@[expose] def first (models : Shared model) (coordinate : Fin 2) : Polynomial :=
  if coordinate = 0 then models.firstZero else models.firstOne

/-- Read the cached second parameter-differential coefficient of the original basis coordinate. -/
@[expose] def second (models : Shared model) (coordinate : Fin 2) : Polynomial :=
  if coordinate = 0 then models.secondZero else models.secondOne

/-- Read the cached connection primitive of the original basis coordinate. -/
@[expose] def primitive (models : Shared model) (coordinate : Fin 2) : Polynomial :=
  if coordinate = 0 then models.primitiveZero else models.primitiveOne

/-- The unweighted value coefficient reads the same original inverse-root polynomial. -/
theorem valueZero_eval (models : Shared model) (point : Canonical) :
    models.valueZero.eval point = model.value.eval point := by rw [models.valueZero_eq]

/-- The weighted value coefficient reads the exact original coordinate times that same inverse model. -/
theorem valueOne_eval (models : Shared model) (point : Canonical) :
    models.valueOne.eval point = point * model.value.eval point := by
  rw [models.valueOne_eq, eval_mul]
  have coordinate : Gaussian.Basic.coordinatePolynomial.eval point = point := by
    change (0 * point + 1) * point + 0 = point
    ring1
  rw [coordinate]

/-- The original first channel reads the retained cube of the same inverse model. -/
theorem firstZero_eval (models : Shared model) (point : Canonical) :
    models.firstZero.eval point = half * (Polynomials.basePolynomial.eval point * model.value.eval point ^ 3) := by
  rw [models.firstZero_eq, eval_scale, eval_mul, models.powers.cube_eval]

/-- The weighted first channel uses the same retained cube. -/
theorem firstOne_eval (models : Shared model) (point : Canonical) :
    models.firstOne.eval point = half *
      (Polynomials.weightedBasePolynomial.eval point * model.value.eval point ^ 3) := by
  rw [models.firstOne_eq, eval_scale, eval_mul, models.powers.cube_eval]

/-- The original second channel reads the retained fifth power of the same inverse model. -/
theorem secondZero_eval (models : Shared model) (point : Canonical) :
    models.secondZero.eval point = (⟨3 / 4, 0⟩ : Canonical) *
      (Polynomials.squaredBasePolynomial.eval point * model.value.eval point ^ 5) := by
  rw [models.secondZero_eq, eval_scale, eval_mul, models.powers.fifth_eval]

/-- The weighted second channel uses that same retained fifth power. -/
theorem secondOne_eval (models : Shared model) (point : Canonical) :
    models.secondOne.eval point = (⟨3 / 4, 0⟩ : Canonical) *
      (Polynomials.weightedSquaredBasePolynomial.eval point * model.value.eval point ^ 5) := by
  rw [models.secondOne_eq, eval_scale, eval_mul, models.powers.fifth_eval]

/-- The first connection primitive reads its original numerator times the same inverse model. -/
theorem primitiveZero_eval (models : Shared model) (point : Canonical) :
    models.primitiveZero.eval point = Polynomials.firstPrimitivePolynomial.eval point * model.value.eval point := by
  rw [models.primitiveZero_eq, eval_mul]

/-- The second connection primitive reads its original parameter-dependent numerator times the same inverse model. -/
theorem primitiveOne_eval (models : Shared model) (point : Canonical) :
    models.primitiveOne.eval point =
      (Polynomials.secondPrimitivePolynomial parameter).eval point * model.value.eval point := by
  rw [models.primitiveOne_eq, eval_mul]

/-- The scalar primitive reads its original numerator times the same retained cube. -/
theorem scalarPrimitive_eval (models : Shared model) (point : Canonical) :
    models.scalarPrimitive.eval point =
      Polynomials.picardFuchsPrimitivePolynomial.eval point * model.value.eval point ^ 3 := by
  rw [models.scalarPrimitive_eq, eval_mul, models.powers.cube_eval]

end Shared

set_option genInjectivity false in
/-- Cached finite connection and scalar residual coefficient tables consuming the same original six channel models.

Each table is the displayed linear combination of retained channel caches.
The primitive coefficients remain those of the same shared inverse model.
No inverse-root power or channel coefficient is recomputed by readback. -/
structure Rows {parameter : Canonical} {box : Box} {model : Model (Paths.polynomial parameter) box}
    (models : Shared model) where
  /-- The cached first original connection row coefficient. -/
  zero : Polynomial
  /-- The first row consumes the original first and value channel caches. -/
  zero_eq : zero = models.firstZero.scale (Clearance.connectionDenominator parameter) -
    (models.valueZero.scale parameter - models.valueOne)
  /-- The cached second original connection row coefficient. -/
  one : Polynomial
  /-- The second row consumes the same original value caches and original weighted first cache. -/
  one_eq : one = models.firstOne.scale (Clearance.connectionDenominator parameter) -
    (models.valueZero.scale parameter - models.valueOne.scale parameter)
  /-- The cached original scalar equation coefficient. -/
  scalar : Polynomial
  /-- The scalar equation consumes the original second, first and value coefficient caches. -/
  scalar_eq : scalar = models.secondZero.scale (4 * parameter * (1 - parameter)) +
    models.firstZero.scale (4 * (1 - 2 * parameter)) - models.valueZero

constructive_injectivity Rows

namespace Rows

variable {parameter : Canonical} {box : Box} {model : Model (Paths.polynomial parameter) box}
  {models : Shared model}

/-- Compute all three residual coefficient tables once from the same six cached original channels. -/
@[expose] def build (models : Shared model) : Rows models :=
  let zero := models.firstZero.scale (Clearance.connectionDenominator parameter) -
    (models.valueZero.scale parameter - models.valueOne)
  let one := models.firstOne.scale (Clearance.connectionDenominator parameter) -
    (models.valueZero.scale parameter - models.valueOne.scale parameter)
  let scalar := models.secondZero.scale (4 * parameter * (1 - parameter)) +
    models.firstZero.scale (4 * (1 - 2 * parameter)) - models.valueZero
  ⟨zero, rfl, one, rfl, scalar, rfl⟩

/-- Read the cached original connection coefficient for one basis coordinate. -/
@[expose] def connection (rows : Rows models) (coordinate : Fin 2) : Polynomial :=
  if coordinate = 0 then rows.zero else rows.one

/-- The original first row reads its same cached first and value channels. -/
theorem zero_eval (rows : Rows models) (point : Canonical) :
    rows.zero.eval point = Clearance.connectionDenominator parameter * models.firstZero.eval point -
      (parameter * models.valueZero.eval point - models.valueOne.eval point) := by
  rw [rows.zero_eq, eval_sub, eval_scale, eval_sub, eval_scale]

/-- The original second row reads its same cached first and value channels. -/
theorem one_eval (rows : Rows models) (point : Canonical) :
    rows.one.eval point = Clearance.connectionDenominator parameter * models.firstOne.eval point -
      (parameter * models.valueZero.eval point - parameter * models.valueOne.eval point) := by
  rw [rows.one_eq, eval_sub, eval_scale, eval_sub, eval_scale, eval_scale]

/-- The original scalar row reads all three same cached differential channels. -/
theorem scalar_eval (rows : Rows models) (point : Canonical) :
    rows.scalar.eval point = 4 * parameter * (1 - parameter) * models.secondZero.eval point +
      4 * (1 - 2 * parameter) * models.firstZero.eval point - models.valueZero.eval point := by
  rw [rows.scalar_eq, eval_sub, eval_add, eval_scale, eval_scale]

/-- The cached first connection row reads the original first reduction at the same approximate inverse root. -/
theorem zero_form (rows : Rows models) (point : Canonical) :
    rows.zero.eval point = Clearance.connectionDenominator parameter *
      (half * ((Connection.firstConnectionReduction parameter).parameterDerivativeNumerator.eval point *
        model.value.eval point ^ 3)) -
      (Connection.firstConnectionReduction parameter).basisNumerator.eval point * model.value.eval point := by
  rw [rows.zero_eval, models.firstZero_eval, models.valueZero_eval, models.valueOne_eval,
    Connection.ConnectionReduction.basisNumerator_eval]
  change _ = Clearance.connectionDenominator parameter *
    (half * (Polynomials.basePolynomial.eval point * model.value.eval point ^ 3)) -
    (parameter + (-1 : Canonical) * point) * model.value.eval point
  ring1

/-- The cached second connection row reads the original second reduction at the same approximate inverse root. -/
theorem one_form (rows : Rows models) (point : Canonical) :
    rows.one.eval point = Clearance.connectionDenominator parameter *
      (half * ((Connection.secondConnectionReduction parameter).parameterDerivativeNumerator.eval point *
        model.value.eval point ^ 3)) -
      (Connection.secondConnectionReduction parameter).basisNumerator.eval point * model.value.eval point := by
  rw [rows.one_eval, models.firstOne_eval, models.valueZero_eval, models.valueOne_eval,
    Connection.ConnectionReduction.basisNumerator_eval]
  change _ = Clearance.connectionDenominator parameter *
    (half * (Polynomials.weightedBasePolynomial.eval point * model.value.eval point ^ 3)) -
    (parameter + (-parameter) * point) * model.value.eval point
  ring1

/-- Half scaling gives the scalar equation's displayed channel coefficients. -/
private theorem scalar_factors (parameter base squared inverse : Canonical) :
    4 * parameter * (1 - parameter) * ((⟨3 / 4, 0⟩ : Canonical) * (squared * inverse ^ 5)) +
      4 * (1 - 2 * parameter) * (half * (base * inverse ^ 3)) - inverse =
    3 * parameter * (1 - parameter) * squared * inverse ^ 5 +
      2 * (1 - 2 * parameter) * base * inverse ^ 3 - inverse := by
  have three : (4 : Canonical) * (⟨3 / 4, 0⟩ : Canonical) = 3 := by decide
  have two : (4 : Canonical) * half = 2 := by decide
  calc
    _ = (4 * (⟨3 / 4, 0⟩ : Canonical)) * parameter * (1 - parameter) * squared * inverse ^ 5 +
      (4 * half) * (1 - 2 * parameter) * base * inverse ^ 3 - inverse := by ring1
    _ = _ := by rw [three, two]

/-- The original cached scalar row reads the three displayed coefficients at the same approximate inverse root. -/
theorem scalar_form (rows : Rows models) (point : Canonical) :
    rows.scalar.eval point =
      3 * parameter * (1 - parameter) * Polynomials.baseValue point ^ 2 * model.value.eval point ^ 5 +
        2 * (1 - 2 * parameter) * Polynomials.baseValue point * model.value.eval point ^ 3 -
          model.value.eval point := by
  rw [rows.scalar_eval, models.secondZero_eval, models.firstZero_eval, models.valueZero_eval,
    Polynomials.squaredBasePolynomial_eval, Polynomials.basePolynomial_eval]
  exact scalar_factors parameter _ _ _

end Rows

/-- The scalar connection defect splits into the actual root residual and primitive error. -/
private theorem connection_model_scalar {D S B P R dR dP q derivativeValue : Canonical}
    (cleared : D * S = 2 * B * P + 2 * dR * P - R * dP) :
    D * (half * (S * q ^ 3)) - B * q - derivativeValue =
      -(B * q * (1 - P * q ^ 2)) -
        (derivativeValue - half * (2 * (P * dR) - R * dP) * q ^ 3) := by
  have twice : (2 : Canonical) * half = 1 := by decide
  calc
    _ = half * (D * S) * q ^ 3 - B * q - derivativeValue := by ring1
    _ = half * (2 * B * P + 2 * dR * P - R * dP) * q ^ 3 - B * q - derivativeValue :=
      congrArg (fun value => half * value * q ^ 3 - B * q - derivativeValue) cleared
    _ = -(B * q * (1 - P * q ^ 2)) -
        (derivativeValue - half * (2 * (P * dR) - R * dP) * q ^ 3) +
          B * P * q ^ 3 * (2 * half - 1) := by ring1
    _ = _ := by rw [twice]; ring1

/-- The actual connection differential models differ from their retained polynomial primitive by two original residuals.

The cleared identity is the original reduction's certificate. The root
residual is the same model's cached residual, and the derivative term is
the actual derivative of the finite primitive model. Neither term is
identified with zero at a finite approximation stage. -/
theorem connection_model_identity {parameter : Canonical} {box : Box}
    (reduction : Connection.ConnectionReduction parameter) (model : Model (Paths.polynomial parameter) box)
    (point : Canonical) :
    Clearance.connectionDenominator parameter *
          (half * (reduction.parameterDerivativeNumerator.eval point * model.value.eval point ^ 3)) -
        reduction.basisNumerator.eval point * model.value.eval point -
        (Derivative.derivative (reduction.primitiveNumerator * model.value)).eval point =
      -(reduction.basisNumerator.eval point * model.value.eval point * model.residual.eval point) -
        ((Derivative.derivative (reduction.primitiveNumerator * model.value)).eval point -
          half * (Algebra.Quadratic.Pair.Polynomial.Expression.oddPrimitiveNumerator
            (Paths.polynomial parameter) reduction.primitiveNumerator 0).eval point * model.value.eval point ^ 3) := by
  have cleared := reduction.clearedIdentity point
  rw [Gaussian.GCD.derivative, Gaussian.GCD.derivative,
    ← reduction.basisNumerator_eval point] at cleared
  rw [model.residual_eq]
  simp only [Algebra.Quadratic.Pair.Polynomial.Expression.oddPrimitiveNumerator,
    eval_sub, eval_scale, eval_mul, Nat.cast_zero, mul_zero, zero_add, one_mul]
  exact connection_model_scalar cleared

/-- The scalar model and its fifth-power expression differ by the same cached root residual. -/
private theorem scalar_model_scalar (A B P q : Canonical) :
    A * q ^ 5 + B * q ^ 3 - q - (A + B * P - P ^ 2) * q ^ 5 =
      (1 - P * q ^ 2) * (B * q ^ 3 - q * (2 - (1 - P * q ^ 2))) := by ring1

/-- The three actual scalar-equation channels retain the extra finite root-residual term from their unequal odd powers.

Multiplying by an approximate inverse root does not permit replacing its
square by the exact reciprocal. This identity exposes that discrepancy
using the same model residual as the connection rows. -/
theorem scalar_model_identity {parameter : Canonical} {box : Box}
    (model : Model (Paths.polynomial parameter) box) (point : Canonical) :
    3 * parameter * (1 - parameter) * Polynomials.baseValue point ^ 2 * model.value.eval point ^ 5 +
        2 * (1 - 2 * parameter) * Polynomials.baseValue point * model.value.eval point ^ 3 -
        model.value.eval point -
        (Residual.picardFuchsResidualPolynomial parameter).eval point * model.value.eval point ^ 5 =
      model.residual.eval point *
        (2 * (1 - 2 * parameter) * Polynomials.baseValue point * model.value.eval point ^ 3 -
          model.value.eval point * (2 - model.residual.eval point)) := by
  rw [Residual.picardFuchsResidualPolynomial_eval, Residual.picardFuchsResidualNumerator,
    Polynomials.curveValue, ← Paths.polynomial_eval, model.residual_eq]
  exact scalar_model_scalar _ _ _ _

end Purelib.Curves.Legendre.Periods.Jets.Models
