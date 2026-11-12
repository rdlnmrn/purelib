module

public import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
public import Purelib.Curves.Legendre.PicardFuchs.Residual
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Linear
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Data.Gaussian.Cast
import Purelib.Tactic.Ring

/-! # The original pointwise scalar residual and its independent primitive derivative

The retained value, first and second specifications construct the original
three numerical residual terms on the same point and prepared sheet. The
canonical polynomial identity compares their actual finite reciprocal-power
processes with the independent derivative of the original primitive over y³.

Actual primitive edge increments and closed-cycle integral cancellation
remain separate geometric obligations.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.Operational

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

/-- The canonical residual primitive function retains its original polynomial numerator over the sheet cube. -/
@[expose] def primitiveForm (parameter : Canonical) : OddPowerDifferential (Paths.polynomial parameter) :=
  OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
    (Residual.picardFuchsReduction parameter).primitiveNumerator 1 1

/-- The independent spatial derivative of that original primitive with both original polynomial derivatives cached. -/
@[expose] def primitiveDerivative (parameter : Canonical) :
    OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter) :=
  OddPower.Derivative.Specification.build (Paths.polynomial parameter) (primitiveForm parameter)

/-- The original three-term scalar residual evaluated on one identical retained point and prepared sheet. -/
@[expose] def residualValue (parameter point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) : CoherentNamed :=
  CoherentNamed.add
    (CoherentNamed.add
      (Power.scale (4 * parameter * (1 - parameter))
        ((Specification.secondDerivativeSpecification parameter 0).value point sheet apart))
      (Power.scale (4 * (1 - 2 * parameter))
        ((Specification.firstDerivativeSpecification parameter 0).value point sheet apart)))
    (CoherentNamed.neg ((Specification.valueSpecification parameter 0).value point sheet apart))

/-- The original displayed half scale equals the exact Gaussian half. -/
private theorem half_scale : Cast.LegendrePeriodJets.realGaussian (1 / 2) = (1 / 2 : Canonical) := by
  decide +kernel

/-- The original displayed second-derivative scale equals three Gaussian quarters. -/
private theorem second_scale : Cast.LegendrePeriodJets.realGaussian (3 / 4) = (3 / 4 : Canonical) := by
  decide +kernel

/-- The original value evaluator retains scaling by one on the actual reciprocal power. -/
private theorem value_zero (parameter : Canonical) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.valueSpecification parameter 0).value point sheet apart =
      Power.scale 1 (Power.namedPower ((Coherence.exact 1).div sheet apart) 1) := by
  rewrite [Specification.valueSpecification_zero]
  unfold OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    OddPowerDifferential.ofCoefficients
  rewrite [Evaluation.constantOnePolynomial_eval, Gaussian.Basic.one_mul]
  rfl

/-- The original first evaluator has its original exact quadratic numerator over the reciprocal cube. -/
private theorem first_value (parameter : Canonical) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.firstDerivativeSpecification parameter 0).value point sheet apart =
      Power.scale ((1 / 2 : Canonical) * Polynomials.baseValue point)
        (Power.namedPower ((Coherence.exact 1).div sheet apart) 3) := by
  rewrite [Specification.firstDerivativeSpecification_zero]
  unfold OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    OddPowerDifferential.ofCoefficients
  rewrite [half_scale, Polynomials.basePolynomial_eval]
  rfl

/-- The original second evaluator retains the squared quadratic numerator over the actual reciprocal fifth power. -/
private theorem second_value (parameter : Canonical) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    (Specification.secondDerivativeSpecification parameter 0).value point sheet apart =
      Power.scale ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2)
        (Power.namedPower ((Coherence.exact 1).div sheet apart) 5) := by
  rewrite [Specification.secondDerivativeSpecification_zero]
  unfold OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    OddPowerDifferential.ofCoefficients
  rewrite [second_scale, Polynomials.squaredBasePolynomial_eval]
  rfl

/-- Combining the original three scalar coefficients gives the exact retained residual-polynomial numerator. -/
private theorem residual_coefficient (parameter point : Canonical) :
    (4 * parameter * (1 - parameter)) * ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2) +
        (4 * (1 - 2 * parameter)) * ((1 / 2 : Canonical) * Polynomials.baseValue point) *
          (Paths.polynomial parameter).eval point -
        (Paths.polynomial parameter).eval point * (Paths.polynomial parameter).eval point =
      (Residual.picardFuchsReduction parameter).residualNumerator.eval point := by
  change _ = (Residual.picardFuchsResidualPolynomial parameter).eval point
  rewrite [Residual.picardFuchsResidualPolynomial_eval]
  unfold Residual.picardFuchsResidualNumerator
  simp only [Paths.polynomial_eval, -eq_self, -iff_self]
  have half : (4 : Canonical) * (1 / 2 : Canonical) = 2 := by decide +kernel
  have quarters : (4 : Canonical) * (3 / 4 : Canonical) = 3 := by decide +kernel
  calc
    _ = (4 * (3 / 4 : Canonical)) * parameter * (1 - parameter) * Polynomials.baseValue point ^ 2 +
        (4 * (1 / 2 : Canonical)) * (1 - 2 * parameter) * Polynomials.baseValue point *
          Polynomials.curveValue parameter point - Polynomials.curveValue parameter point ^ 2 := by
      unfold Polynomials.curveValue
      ring1
    _ = _ := by rewrite [half, quarters]; rfl

/-- The canonical cleared polynomial identity equals the exact independent derivative coefficient. -/
private theorem derivative_coefficient (parameter point : Canonical)
    (derivative : OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter)) :
    derivative.differential.scale * derivative.differential.numerator.eval point =
      (Residual.picardFuchsReduction parameter).residualNumerator.eval point := by
  rewrite [derivative.differential_eq, derivative.numerator_eq, derivative.numeratorDerivative_eq,
    derivative.polynomialDerivative_eq]
  have exponent : OddPower.Derivative.exponentCoefficient (primitiveForm parameter) = 3 := by
    change (⟨Data.Rat.Fraction.Cast.fromInt 3, 0⟩ : Canonical) = 3
    decide +kernel
  rewrite [exponent]
  change (1 / 2 : Canonical) *
      (((GCD.derivative (Residual.picardFuchsReduction parameter).primitiveNumerator) *
        Paths.polynomial parameter).scale 2 -
        ((Residual.picardFuchsReduction parameter).primitiveNumerator *
          GCD.derivative (Paths.polynomial parameter)).scale 3).eval point = _
  rewrite [eval_sub, eval_scale, eval_mul, eval_scale, eval_mul]
  have cleared := (Residual.picardFuchsReduction parameter).clearedIdentity point
  have half : (1 / 2 : Canonical) * 2 = 1 := by decide +kernel
  calc
    _ = (1 / 2 : Canonical) *
        (2 * (GCD.derivative (Residual.picardFuchsReduction parameter).primitiveNumerator).eval point *
            (Paths.polynomial parameter).eval point -
          3 * (Residual.picardFuchsReduction parameter).primitiveNumerator.eval point *
            (GCD.derivative (Paths.polynomial parameter)).eval point) := by ring1
    _ = (1 / 2 : Canonical) *
        (2 * (Residual.picardFuchsReduction parameter).residualNumerator.eval point) :=
      congrArg (fun value : Canonical => (1 / 2 : Canonical) * value) cleared.symm
    _ = ((1 / 2 : Canonical) * 2) * (Residual.picardFuchsReduction parameter).residualNumerator.eval point := by ring1
    _ = _ := by rewrite [half, Gaussian.Basic.one_mul]; rfl

/-- The actual original scalar residual agrees with the retained independent primitive derivative on the same sheet.

The original value, cube and fifth-power evaluators retain their separate
process trees. Square cancellation moves them to a common reciprocal fifth
power; the canonical exact scalar identity identifies its numerator with
the cached independent derivative specification.
-/
def reduced (parameter point : Canonical) (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact ((Paths.polynomial parameter).eval point)).name)
    (derivative : OddPower.Derivative.Specification (Paths.polynomial parameter) (primitiveForm parameter))
    (values : derivative.Values point sheet apart) :
    NamedEquivalent (residualValue parameter point sheet apart).name values.derivative.name := by
  let reciprocal := (Coherence.exact 1).div sheet apart
  let lower := Power.namedPower reciprocal 1
  let middle := Power.namedPower reciprocal 3
  let upper := Power.namedPower reciprocal 5
  let curve := (Paths.polynomial parameter).eval point
  let second := (4 * parameter * (1 - parameter)) * ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2)
  let first := (4 * (1 - 2 * parameter)) * ((1 / 2 : Canonical) * Polynomials.baseValue point)
  have upperToMiddle : NamedEquivalent (Power.scale curve upper).name middle.name :=
    (Product.Laws.coherentMul_comm (Coherence.exact curve) upper).trans
      (Power.reciprocalPower_square_mul_cancel sheet reciprocal apart rfl curve square 3)
  have middleToLower : NamedEquivalent (Power.scale curve middle).name lower.name :=
    (Product.Laws.coherentMul_comm (Coherence.exact curve) middle).trans
      (Power.reciprocalPower_square_mul_cancel sheet reciprocal apart rfl curve square 1)
  have upperToLower : NamedEquivalent (Power.scale (curve * curve) upper).name lower.name :=
    (Power.scale_scale curve curve upper).symm.trans
      ((Product.Congruence.coherentMul_respects (Coherence.exact curve) (Coherence.exact curve)
        (Power.scale curve upper) middle (NamedEquivalent.refl _) upperToMiddle).trans middleToLower)
  have secondReduced := Power.scale_scale (4 * parameter * (1 - parameter))
    ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2) upper
  have firstReduced := (Power.scale_scale (4 * (1 - 2 * parameter))
    ((1 / 2 : Canonical) * Polynomials.baseValue point) middle).trans
      ((Product.Congruence.coherentMul_respects (Coherence.exact first) (Coherence.exact first)
        middle (Power.scale curve upper) (NamedEquivalent.refl _) upperToMiddle.symm).trans
          (Power.scale_scale first curve upper))
  have baseReduced : NamedEquivalent (Power.scale 1 lower).name (Power.scale (curve * curve) upper).name :=
    (Mul.coherentMul_one_left lower).trans upperToLower.symm
  have baseNegated := Coherent.Additive.coherentNeg_respects (Power.scale 1 lower)
    (Power.scale (curve * curve) upper) baseReduced
  have rows := Sum.Congruence.coherentAdd_respects
    (Power.scale (4 * parameter * (1 - parameter))
      (Power.scale ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2) upper))
    (Power.scale second upper)
    (Power.scale (4 * (1 - 2 * parameter)) (Power.scale ((1 / 2 : Canonical) * Polynomials.baseValue point) middle))
    (Power.scale (first * curve) upper) secondReduced firstReduced
  have combined := (Sum.Congruence.coherentAdd_respects
    ((Power.scale second upper).add (Power.scale (first * curve) upper))
    (Power.scale (second + first * curve) upper)
    (CoherentNamed.neg (Power.scale (curve * curve) upper))
    (CoherentNamed.neg (Power.scale (curve * curve) upper))
    (Power.scale_add second (first * curve) upper) (NamedEquivalent.refl _)).trans
      (Power.scale_sub (second + first * curve) (curve * curve) upper)
  have result := (Sum.Congruence.coherentAdd_respects
    ((Power.scale (4 * parameter * (1 - parameter))
        (Power.scale ((3 / 4 : Canonical) * Polynomials.baseValue point ^ 2) upper)).add
      (Power.scale (4 * (1 - 2 * parameter))
        (Power.scale ((1 / 2 : Canonical) * Polynomials.baseValue point) middle)))
    ((Power.scale second upper).add (Power.scale (first * curve) upper))
    (CoherentNamed.neg (Power.scale 1 lower)) (CoherentNamed.neg (Power.scale (curve * curve) upper))
    rows baseNegated).trans combined
  have coefficient : second + first * curve - curve * curve =
      derivative.differential.scale * derivative.differential.numerator.eval point :=
    (residual_coefficient parameter point).trans (derivative_coefficient parameter point derivative).symm
  have derivativeExponent : derivative.differential.denominatorExponent = 5 := derivative.differential_exponent
  have derivativeValue : values.derivative =
      Power.scale (derivative.differential.scale * derivative.differential.numerator.eval point) upper := by
    rewrite [values.derivative_eq]
    unfold OddPowerDifferential.value
    rewrite [derivativeExponent]
    rfl
  have final := NamedEquivalent.transport rfl
    (congrArg (fun coefficient : Canonical => (Power.scale coefficient upper).name) coefficient) result
  have transported := NamedEquivalent.transport rfl
    (congrArg (fun channel : CoherentNamed => channel.name) derivativeValue.symm) final
  unfold residualValue
  rewrite [second_value parameter point sheet apart, first_value parameter point sheet apart,
    value_zero parameter point sheet apart]
  exact transported

end Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.Operational
