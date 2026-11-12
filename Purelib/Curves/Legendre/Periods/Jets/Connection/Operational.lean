module

public import Purelib.Curves.Legendre.Periods.Jets.Connection
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Linear
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Data.Fin.Two
import Purelib.Tactic.Ring

/-! # Original pointwise connection reductions on the retained prepared sheet

The original two value specifications and first derivative specification
remain the numerical coefficient owners. Canonical polynomial reductions
construct the primitive function and its independent spatial derivative.
The original square comparison and finite reciprocal arithmetic prove their
pointwise operational connection identity.

The primitive's actual integral edge and closed-boundary comparison remain
separate geometric integration obligations.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Connection.Operational

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The original connection row's primitive function specification, retaining its displayed numerator over one sheet. -/
@[expose] def primitiveForm (parameter : Canonical) (coordinate : Fin 2) :
    OddPowerDifferential (Paths.polynomial parameter) :=
  OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
    (connectionReduction parameter coordinate).primitiveNumerator 0 1

/-- The independent spatial derivative of that same original primitive, with both polynomial derivatives cached. -/
@[expose] def primitiveDerivative (parameter : Canonical) (coordinate : Fin 2) :
    OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter coordinate) :=
  OddPower.Derivative.Specification.build (Paths.polynomial parameter) (primitiveForm parameter coordinate)

/-- The original source first-derivative evaluator scaled by the exact original connection denominator. -/
@[expose] def scaledFirstValue (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) : CoherentNamed :=
  Power.scale (Clearance.connectionDenominator parameter)
    ((Specification.firstDerivativeSpecification parameter coordinate).value point sheet apart)

/-- The canonical row coefficients acting on the two unchanged original value evaluators at the same point and sheet. -/
@[expose] def actionValue (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) : CoherentNamed :=
  let reduction := connectionReduction parameter coordinate
  CoherentNamed.add
    (Power.scale reduction.basisConstant ((Specification.valueSpecification parameter 0).value point sheet apart))
    (Power.scale reduction.basisLinear ((Specification.valueSpecification parameter 1).value point sheet apart))

/-- The source first specification retains the exact numerator of its canonical polynomial reduction. -/
private theorem first_numerator (parameter : Canonical) (coordinate : Fin 2) :
    (Specification.firstDerivativeSpecification parameter coordinate).numerator =
      (connectionReduction parameter coordinate).parameterDerivativeNumerator := by
  rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
  · subst coordinate
    rfl
  · subst coordinate
    rewrite [Specification.firstDerivativeSpecification_one, connectionReduction_one]
    rfl

/-- Every original first derivative specification has the exact Gaussian half as its scale. -/
private theorem first_scale (parameter : Canonical) (coordinate : Fin 2) :
    (Specification.firstDerivativeSpecification parameter coordinate).scale = (1 / 2 : Canonical) := by
  rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
  · subst coordinate
    change (⟨1 / 2, 0⟩ : Canonical) = (1 / 2 : Canonical)
    decide +kernel
  · subst coordinate
    rewrite [Specification.firstDerivativeSpecification_one]
    change (⟨1 / 2, 0⟩ : Canonical) = (1 / 2 : Canonical)
    decide +kernel

/-- Every original first derivative specification uses exactly the reciprocal cube. -/
private theorem first_exponent (parameter : Canonical) (coordinate : Fin 2) :
    (Specification.firstDerivativeSpecification parameter coordinate).denominatorExponent = 3 := rfl

/-- The retained original source evaluator has its canonical exact half-numerator and reciprocal cube. -/
private theorem first_value (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.firstDerivativeSpecification parameter coordinate).value point sheet apart =
      Power.scale ((1 / 2 : Canonical) *
        (connectionReduction parameter coordinate).parameterDerivativeNumerator.eval point)
        (Power.namedPower ((Coherence.exact 1).div sheet apart) 3) := by
  unfold OddPowerDifferential.value
  rewrite [first_numerator parameter coordinate, first_scale parameter coordinate, first_exponent parameter coordinate]
  rfl

/-- The original value-zero evaluator is scaling by one on its identical retained reciprocal power. -/
private theorem value_zero (parameter : Canonical) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.valueSpecification parameter 0).value point sheet apart =
      Power.scale 1 (Power.namedPower ((Coherence.exact 1).div sheet apart) 1) := by
  rewrite [Specification.valueSpecification_zero]
  unfold OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    OddPowerDifferential.ofCoefficients
  rewrite [Evaluation.constantOnePolynomial_eval, Gaussian.Basic.one_mul]
  rfl

/-- The original value-one evaluator has its identical original spatial-coordinate coefficient. -/
private theorem value_one (parameter : Canonical) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.valueSpecification parameter 1).value point sheet apart =
      Power.scale point (Power.namedPower ((Coherence.exact 1).div sheet apart) 1) := by
  rewrite [Specification.valueSpecification_one]
  unfold OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    OddPowerDifferential.ofCoefficients
  rewrite [Evaluation.coordinatePolynomial_eval, Gaussian.Basic.one_mul]
  rfl

/-- The original action evaluator agrees with its exact retained polynomial row coefficient on the same reciprocal. -/
private def action_coefficient (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    NamedEquivalent (actionValue parameter coordinate point sheet apart).name
      (Power.scale ((connectionReduction parameter coordinate).basisConstant +
        (connectionReduction parameter coordinate).basisLinear * point)
        (Power.namedPower ((Coherence.exact 1).div sheet apart) 1)).name := by
  unfold actionValue
  rewrite [value_zero parameter point sheet apart, value_one parameter point sheet apart]
  let power := Power.namedPower ((Coherence.exact 1).div sheet apart) 1
  let reduction := connectionReduction parameter coordinate
  have constant := Power.scale_scale reduction.basisConstant 1 power
  have constantValue : reduction.basisConstant * 1 = reduction.basisConstant := Gaussian.Basic.mul_one _
  rewrite [constantValue] at constant
  exact
    (Sum.Congruence.coherentAdd_respects
      (Power.scale reduction.basisConstant (Power.scale 1 power)) (Power.scale reduction.basisConstant power)
      (Power.scale reduction.basisLinear (Power.scale point power))
      (Power.scale (reduction.basisLinear * point) power) constant
      (Power.scale_scale reduction.basisLinear point power)).trans
        (Power.scale_add reduction.basisConstant (reduction.basisLinear * point) power)

/-- The canonical cleared identity expresses the source coefficient as its combined first term minus the last. -/
private theorem cleared_coefficient (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (derivative : OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter coordinate)) :
    Clearance.connectionDenominator parameter *
        ((1 / 2 : Canonical) * (connectionReduction parameter coordinate).parameterDerivativeNumerator.eval point) =
      ((connectionReduction parameter coordinate).basisConstant +
        (connectionReduction parameter coordinate).basisLinear * point +
        derivative.first.scale * derivative.first.numerator.eval point) *
          (Paths.polynomial parameter).eval point - derivative.last.scale * derivative.last.numerator.eval point := by
  rewrite [derivative.first_eq, derivative.last_eq, derivative.numeratorDerivative_eq,
    derivative.polynomialDerivative_eq]
  have exponent : OddPower.Derivative.exponentCoefficient (primitiveForm parameter coordinate) = 1 := by
    change (⟨Data.Rat.Fraction.Cast.fromInt 1, 0⟩ : Canonical) = 1
    decide +kernel
  rewrite [exponent]
  change Clearance.connectionDenominator parameter *
      ((1 / 2 : Canonical) * (connectionReduction parameter coordinate).parameterDerivativeNumerator.eval point) =
    ((connectionReduction parameter coordinate).basisConstant +
      (connectionReduction parameter coordinate).basisLinear * point +
      1 * (GCD.derivative (connectionReduction parameter coordinate).primitiveNumerator).eval point) *
        (Paths.polynomial parameter).eval point - (1 * 1 / 2 : Canonical) *
          ((connectionReduction parameter coordinate).primitiveNumerator *
            GCD.derivative (Paths.polynomial parameter)).eval point
  have unitHalf : (1 * 1 / 2 : Canonical) = (1 / 2 : Canonical) :=
    congrArg (fun value : Canonical => value / 2) (Gaussian.Basic.one_mul 1)
  rewrite [unitHalf, Gaussian.Basic.one_mul]
  rewrite [eval_mul]
  have cleared := (connectionReduction parameter coordinate).clearedIdentity point
  have half : (2 : Canonical) * (1 / 2 : Canonical) = 1 := by decide +kernel
  calc
    _ = (1 / 2 : Canonical) * (Clearance.connectionDenominator parameter *
        (connectionReduction parameter coordinate).parameterDerivativeNumerator.eval point) := by ring1
    _ = (1 / 2 : Canonical) *
        (2 * ((connectionReduction parameter coordinate).basisConstant +
            (connectionReduction parameter coordinate).basisLinear * point) *
            (Paths.polynomial parameter).eval point +
          2 * (GCD.derivative (connectionReduction parameter coordinate).primitiveNumerator).eval point *
            (Paths.polynomial parameter).eval point -
          (connectionReduction parameter coordinate).primitiveNumerator.eval point *
            (GCD.derivative (Paths.polynomial parameter)).eval point) :=
      congrArg (fun value : Canonical => (1 / 2 : Canonical) * value) cleared
    _ = (((connectionReduction parameter coordinate).basisConstant +
          (connectionReduction parameter coordinate).basisLinear * point +
          (GCD.derivative (connectionReduction parameter coordinate).primitiveNumerator).eval point) *
            (Paths.polynomial parameter).eval point) * (2 * (1 / 2 : Canonical)) -
        (1 / 2 : Canonical) *
          ((connectionReduction parameter coordinate).primitiveNumerator.eval point *
            (GCD.derivative (Paths.polynomial parameter)).eval point) := by ring1
    _ = _ := by rewrite [half, Gaussian.Basic.mul_one]; rfl

/-- Both original pointwise connection rows agree with the original action plus the retained independent derivative.

The existing primitive-value cache and its original Leibniz comparison are
reused. The canonical cleared polynomial identity and original square
comparison derive the actual coefficient relation, before any geometric
integral or scheduled period-sample comparison is supplied.
-/
def reduced (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact ((Paths.polynomial parameter).eval point)).name)
    (derivative : OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter coordinate))
    (values : derivative.Values point sheet apart) :
    NamedEquivalent (scaledFirstValue parameter coordinate point sheet apart).name
      ((actionValue parameter coordinate point sheet apart).add values.derivative).name := by
  let reciprocal := (Coherence.exact 1).div sheet apart
  let lower := Power.namedPower reciprocal 1
  let upper := Power.namedPower reciprocal 3
  let reduction := connectionReduction parameter coordinate
  let basis := reduction.basisConstant + reduction.basisLinear * point
  let first := derivative.first.scale * derivative.first.numerator.eval point
  let last := derivative.last.scale * derivative.last.numerator.eval point
  have source := Power.scale_scale (Clearance.connectionDenominator parameter)
    ((1 / 2 : Canonical) * reduction.parameterDerivativeNumerator.eval point) upper
  have sourceCoefficient := cleared_coefficient parameter coordinate point derivative
  rewrite [sourceCoefficient] at source
  have division := Power.reciprocalPower_coefficient_difference sheet reciprocal apart rfl
    ((Paths.polynomial parameter).eval point) (basis + first) last square 1
  have separated := (Sum.Congruence.coherentAdd_respects (Power.scale (basis + first) lower)
    ((Power.scale basis lower).add (Power.scale first lower))
    (CoherentNamed.neg (Power.scale last upper)) (CoherentNamed.neg (Power.scale last upper))
    (Power.scale_add basis first lower).symm (NamedEquivalent.refl _)).trans
      (Add.coherentAdd_assoc (Power.scale basis lower) (Power.scale first lower)
        (CoherentNamed.neg (Power.scale last upper)))
  have firstExponent : derivative.first.denominatorExponent = 1 := derivative.first_exponent
  have lastExponent : derivative.last.denominatorExponent = 3 := derivative.last_exponent
  have firstValue : values.first = Power.scale first lower := by
    rewrite [values.first_eq]
    unfold OddPowerDifferential.value
    rewrite [firstExponent]
    rfl
  have lastValue : values.last = Power.scale last upper := by
    rewrite [values.last_eq]
    unfold OddPowerDifferential.value
    rewrite [lastExponent]
    rfl
  have leibniz := values.agreement
  rewrite [values.difference_eq, firstValue, lastValue] at leibniz
  have finish := Sum.Congruence.coherentAdd_respects (Power.scale basis lower)
    (actionValue parameter coordinate point sheet apart)
    ((Power.scale first lower).add (CoherentNamed.neg (Power.scale last upper))) values.derivative
    (action_coefficient parameter coordinate point sheet apart).symm leibniz.symm
  unfold scaledFirstValue
  rewrite [first_value parameter coordinate point sheet apart]
  exact source.trans (division.trans (separated.trans finish))

end Purelib.Curves.Legendre.Periods.Jets.Connection.Operational
