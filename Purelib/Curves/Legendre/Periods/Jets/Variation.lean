module

public import Purelib.Calculus.Jet.Quadratic.SquareRoot
public import Purelib.Calculus.Jet.Quadratic.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Calculus.Jet.Quadratic.Arithmetic
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Derivative.Monomial
import Purelib.Tactic.Ring

/-! # Finite parameter variation of the original Legendre differential rows

The original value numerator is held at one spatial point, and the two
displayed sheet readings retain their own square residuals. The affine
Legendre radicand relation constructs a value-row quadratic certificate.
Cubic composition constructs the first derivative row's variation. Their
slopes are the original first and second derivative differential rows. These
local calculations do not assert a derivative of a transported cycle or a
period integral. Such a consumer must retain its original oriented cycle and
provide geometric sign and uniform sum/denominator clearance for these same
sheet readings, along with their original process-state comparisons.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Calculus.Jet
open Purelib.Calculus.Jet.Quadratic
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial

/-- The exact coefficient reading of an original value row at its original spatial point. -/
@[expose] def valueReading (coordinate : Fin 2) (point root : Canonical) : Canonical :=
  1 * (Specification.valueNumerator coordinate).eval point * root⁻¹

/-- The exact coefficient reading of the original first derivative row on the same sheet. -/
@[expose] def firstReading (coordinate : Fin 2) (point root : Canonical) : Canonical :=
  Cast.LegendrePeriodJets.realGaussian (1 / 2) *
    (Specification.firstDerivativeNumerator coordinate).eval point * root⁻¹ ^ 3

/-- The parameter-independent value scalar reading is the readout of the actual indexed original specification. -/
theorem valueReading_specification (parameter : Canonical) (coordinate : Fin 2) (point root : Canonical) :
    valueReading coordinate point root =
      (Specification.valueSpecification parameter coordinate).scale *
        (Specification.valueSpecification parameter coordinate).numerator.eval point * root⁻¹ := (rfl)

/-- The parameter-independent first scalar reading is the readout of the actual indexed original specification. -/
theorem firstReading_specification (parameter : Canonical) (coordinate : Fin 2) (point root : Canonical) :
    firstReading coordinate point root =
      (Specification.firstDerivativeSpecification parameter coordinate).scale *
        (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point * root⁻¹ ^ 3 := (rfl)

/-- Parameter variation of the original Legendre cubic is affine at the retained spatial point. -/
theorem radicand_step (parameter increment point : Canonical) :
    Polynomials.curveValue (parameter + increment) point =
      Polynomials.curveValue parameter point - increment * Polynomials.baseValue point := by
  unfold Polynomials.curveValue Polynomials.baseValue
  ring1

/-- Scaling the inverse-root coefficient by the original value numerator gives the original first derivative row. -/
theorem original_first_coefficient (coordinate : Fin 2) (point root : Canonical) :
    (1 * (Specification.valueNumerator coordinate).eval point) *
        (SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) =
      firstReading coordinate point root := by
  rcases Purelib.Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    unfold Specification.valueNumerator
    rewrite [if_pos rfl, Dense.Gaussian.Evaluation.constantOnePolynomial_eval]
    unfold firstReading
    unfold Specification.firstDerivativeNumerator
    rewrite [if_pos rfl, Polynomials.basePolynomial_eval]
    change (1 * 1) * (SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) =
      SquareRoot.half * (point * (point - 1)) * root⁻¹ ^ 3
    unfold Polynomials.baseValue
    ring1
  · subst coordinate
    unfold Specification.valueNumerator
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0), Dense.Gaussian.Evaluation.coordinatePolynomial_eval]
    unfold firstReading
    unfold Specification.firstDerivativeNumerator
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0), Polynomials.weightedBasePolynomial_eval]
    change (1 * point) * (SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) =
      SquareRoot.half * (point * (point * (point - 1))) * root⁻¹ ^ 3
    unfold Polynomials.baseValue
    ring1

/-- Construct a finite value-row Taylor certificate from the original two Legendre sheet residuals.

The spatial point, original value differential and parameter increment are
held fixed. Both residual factors and all signed-sheet clearance inputs concern
the actual first and last readings. The constructor computes the inverse-root
factor and scales it by the original row's numerator without replacing either
reading by an equal or commonly chosen sample.
-/
@[expose] def valueCertificate (coordinate : Fin 2)
    (parameter increment point first last : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor)
    (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0)
    (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - Polynomials.curveValue parameter point) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - Polynomials.curveValue (parameter + increment) point) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) : Quadratic.Basic.Certificate increment :=
  (SquareRoot.inverseCertificate first last (Polynomials.curveValue parameter point) increment
    (Polynomials.baseValue point) firstFactor lastFactor firstFactorNonnegative lastFactorNonnegative
      firstNonzero lastNonzero sumNonzero unit firstResidual (by
        rewrite [← radicand_step]
        exact lastResidual)).scale
    ((Specification.valueSpecification parameter coordinate).scale *
      (Specification.valueSpecification parameter coordinate).numerator.eval point)

/-- The parameter certificate's base is the original value row on the first displayed sheet. -/
theorem valueCertificate_base (coordinate : Fin 2)
    (parameter increment point first last : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - Polynomials.curveValue parameter point) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - Polynomials.curveValue (parameter + increment) point) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (valueCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).base = valueReading coordinate point first := rfl

/-- The parameter certificate's output is the same original value row on the last displayed sheet. -/
theorem valueCertificate_output (coordinate : Fin 2)
    (parameter increment point first last : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - Polynomials.curveValue parameter point) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - Polynomials.curveValue (parameter + increment) point) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (valueCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).output = valueReading coordinate point last := rfl

/-- The computed parameter coefficient agrees with the original first derivative differential row. -/
theorem valueCertificate_slope (coordinate : Fin 2)
    (parameter increment point first last : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - Polynomials.curveValue parameter point) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - Polynomials.curveValue (parameter + increment) point) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (valueCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).slope = firstReading coordinate point first := by
  change ((Specification.valueSpecification parameter coordinate).scale *
    (Specification.valueSpecification parameter coordinate).numerator.eval point) *
      (SquareRoot.inverseCertificate first last (Polynomials.curveValue parameter point) increment
        (Polynomials.baseValue point) firstFactor lastFactor firstFactorNonnegative lastFactorNonnegative
          firstNonzero lastNonzero sumNonzero unit firstResidual _).slope = _
  rewrite [SquareRoot.inverseCertificate_slope]
  exact original_first_coefficient coordinate point first

/-- The exact coefficient reading of the original second derivative row on the same sheet. -/
@[expose] def secondReading (coordinate : Fin 2) (point root : Canonical) : Canonical :=
  Cast.LegendrePeriodJets.realGaussian (3 / 4) *
    (Specification.secondDerivativeNumerator coordinate).eval point * root⁻¹ ^ 5

/-- The parameter-independent second scalar reading is the readout of the actual indexed original specification. -/
theorem secondReading_specification (parameter : Canonical) (coordinate : Fin 2) (point root : Canonical) :
    secondReading coordinate point root =
      (Specification.secondDerivativeSpecification parameter coordinate).scale *
        (Specification.secondDerivativeSpecification parameter coordinate).numerator.eval point * root⁻¹ ^ 5 := (rfl)

/-- The two retained Gaussian halves and the cubic coefficient give three quarters. -/
private theorem three_quarters : SquareRoot.half * (SquareRoot.half * 3) =
    Cast.LegendrePeriodJets.realGaussian (3 / 4) := by decide +kernel

/-- The original cube polynomial's formal derivative reads three times the input square. -/
private theorem cube_slope (value : Canonical) :
    (Dense.Gaussian.GCD.derivative (Power.Coordinate.coordinatePositivePower 2)).eval value =
      3 * value ^ 2 := by
  change (Dense.Derivative.derivative (Power.Coordinate.coordinatePositivePower 2)).eval value = _
  exact Dense.Gaussian.Derivative.Monomial.derivative_coordinatePositivePower_eval 2 value

/-- Cubic composition scaled by the original first derivative row gives the original second derivative row. -/
theorem original_second_coefficient (coordinate : Fin 2) (point root : Canonical) :
    (Cast.LegendrePeriodJets.realGaussian (1 / 2) *
      (Specification.firstDerivativeNumerator coordinate).eval point) *
        ((SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) * (3 * root⁻¹ ^ 2)) =
      secondReading coordinate point root := by
  rcases Purelib.Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    unfold Specification.firstDerivativeNumerator
    rewrite [if_pos rfl, Polynomials.basePolynomial_eval]
    unfold secondReading
    unfold Specification.secondDerivativeNumerator
    rewrite [if_pos rfl, Polynomials.squaredBasePolynomial_eval]
    change (SquareRoot.half * (point * (point - 1))) *
        ((SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) * (3 * root⁻¹ ^ 2)) =
      Cast.LegendrePeriodJets.realGaussian (3 / 4) * (point * (point - 1)) ^ 2 * root⁻¹ ^ 5
    unfold Polynomials.baseValue
    calc
      _ = (SquareRoot.half * (SquareRoot.half * 3)) * (point * (point - 1)) ^ 2 * root⁻¹ ^ 5 := by ring1
      _ = _ := by rewrite [three_quarters]; rfl
  · subst coordinate
    unfold Specification.firstDerivativeNumerator
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0), Polynomials.weightedBasePolynomial_eval]
    unfold secondReading
    unfold Specification.secondDerivativeNumerator
    rewrite [if_neg (by decide : (1 : Fin 2) ≠ 0), Polynomials.weightedSquaredBasePolynomial_eval]
    change (SquareRoot.half * (point * (point * (point - 1)))) *
        ((SquareRoot.half * Polynomials.baseValue point * root⁻¹ ^ 3) * (3 * root⁻¹ ^ 2)) =
      Cast.LegendrePeriodJets.realGaussian (3 / 4) * (point * (point * (point - 1)) ^ 2) * root⁻¹ ^ 5
    unfold Polynomials.baseValue
    calc
      _ = (SquareRoot.half * (SquareRoot.half * 3)) * (point * (point * (point - 1)) ^ 2) * root⁻¹ ^ 5 := by ring1
      _ = _ := by rewrite [three_quarters]; rfl

section

variable (coordinate : Fin 2) (parameter increment point first last : Canonical)
  (firstFactor lastFactor : Fraction.Rational)
  (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
  (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
  (unit : Norm.Basic.normSq increment ≤ 1)
  (firstResidual : Norm.Basic.normSq (first * first - Polynomials.curveValue parameter point) ≤
    firstFactor * Norm.Basic.normSq increment ^ 2)
  (lastResidual : Norm.Basic.normSq (last * last - Polynomials.curveValue (parameter + increment) point) ≤
    lastFactor * Norm.Basic.normSq increment ^ 2)

/-- Construct the original first derivative row's finite parameter-variation certificate.

The inverse-root certificate and its two actual readings are retained once.
The existing polynomial Horner bounds certify their cubic on a computed
two-point hull. Generic quadratic composition then computes the full remainder
factor, and the original first derivative numerator and scale are retained.
-/
@[expose] def firstCertificate : Quadratic.Basic.Certificate increment :=
  let inverse := SquareRoot.inverseCertificate first last (Polynomials.curveValue parameter point) increment
    (Polynomials.baseValue point) firstFactor lastFactor firstFactorNonnegative lastFactorNonnegative
      firstNonzero lastNonzero sumNonzero unit firstResidual (by
        rewrite [← radicand_step]
        exact lastResidual)
  let cubic := Quadratic.Polynomial.certificate (Power.Coordinate.coordinatePositivePower 2)
    inverse.base inverse.output
  let composed := inverse.compose cubic (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  composed.scale ((Specification.firstDerivativeSpecification parameter coordinate).scale *
    (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point)

/-- The first derivative certificate retains the original first row reading as its base. -/
theorem firstCertificate_base :
    (firstCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).base = firstReading coordinate point first := by
  change ((Specification.firstDerivativeSpecification parameter coordinate).scale *
    (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point) *
      (Power.Coordinate.coordinatePositivePower 2).eval first⁻¹ = _
  rewrite [Power.Coordinate.coordinatePositivePower_eval]
  rfl

/-- The first derivative certificate retains the same original row on the last reading as its output. -/
theorem firstCertificate_output :
    (firstCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).output = firstReading coordinate point last := by
  change ((Specification.firstDerivativeSpecification parameter coordinate).scale *
    (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point) *
      (Power.Coordinate.coordinatePositivePower 2).eval last⁻¹ = _
  rewrite [Power.Coordinate.coordinatePositivePower_eval]
  rfl

/-- The constructed first derivative variation has the original second derivative row as its slope. -/
theorem firstCertificate_slope :
    (firstCertificate coordinate parameter increment point first last firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).slope = secondReading coordinate point first := by
  change ((Specification.firstDerivativeSpecification parameter coordinate).scale *
    (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval point) *
      ((SquareRoot.inverseCertificate first last (Polynomials.curveValue parameter point) increment
        (Polynomials.baseValue point) firstFactor lastFactor firstFactorNonnegative lastFactorNonnegative
          firstNonzero lastNonzero sumNonzero unit firstResidual _).slope *
          (Dense.Gaussian.GCD.derivative
            (Power.Coordinate.coordinatePositivePower 2)).eval first⁻¹) = _
  rewrite [SquareRoot.inverseCertificate_slope, cube_slope]
  exact original_second_coefficient coordinate point first

end

end Purelib.Curves.Legendre.Periods.Jets.Variation
