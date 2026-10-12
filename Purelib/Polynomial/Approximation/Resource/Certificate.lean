module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Encoding
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
import Purelib.Data.GaussianInt.Pair.Basic

import Purelib.Approximation.Gaussian.Grid.Basic
public import Purelib.Approximation.Gaussian.Grid.Resource
import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Approximation.Rational.QuadraticTarget.Basic
public import Purelib.Approximation.Rational.QuadraticTarget.Resource
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource
import Purelib.Data.Gaussian.Resource
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Resource
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.SquareThreshold.Resource
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Resource.Width
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Resource
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.ComplexContinuedFraction.Hurwitz (Encoding)

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-! ## One RFAP-II resource certificate -/

set_option genInjectivity false in
/-- Displayed data consumed by the bounded RFAP-II calculation family.  The
integral coefficient list is the already cleared list used by homogeneous
evaluation; constructing RFAP-I eliminants and the supplied Newton band is
outside this record. -/
structure StageTwoInput where
  /-- The retained normalized Gaussian polynomial for the Newton calculation. -/ polynomial :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The supplied Gaussian point at which the polynomial and derivative are evaluated. -/ anchor :
    Gaussian.Basic.Canonical
  /-- The retained rational radius used to construct the Gaussian grid. -/ radius : Fraction.Rational
  /-- The displayed Gaussian-integer numerator for homogeneous evaluation. -/ homogeneousNumerator : GaussianInt
  /-- The displayed Gaussian-integer denominator for homogeneous evaluation. -/ homogeneousDenominator : GaussianInt
  /-- The already cleared finite coefficient list used by homogeneous evaluation. -/ homogeneousCoefficients : List
    GaussianInt
  /-- The displayed Gaussian-integer fraction encoded by finite Hurwitz recursion. -/ hurwitzSource :
    GaussianInt.Fraction
  /-- The rational coefficient in the quadratic target request. -/ targetCoefficient : Fraction.Rational
  /-- The rational target for the bounded square-threshold request. -/ target : Fraction.Rational

constructive_injectivity StageTwoInput

end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate.StageTwoInput
open Purelib.Data.Gaussian

open Purelib.Data.GaussianInt
section

/-- Semantic Newton centre obtained by erasing the normalized working
record. -/
def center (input :
  StageTwoInput) : Gaussian.Basic.Canonical :=
  Gaussian.Basic.value
    (Dense.Gaussian.Newton.Basic.newtonCenter input.polynomial input.anchor)

end
end Purelib.Polynomial.Approximation.Resource.Certificate.StageTwoInput

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Accounted recursive and arithmetic clauses actually executed by the
normalized Newton update, grid construction, homogeneous evaluation, finite
Hurwitz encoding, and square-threshold scan. -/
def stageTwoAccountedSteps (input :
  StageTwoInput) : Nat :=
  Dense.Gaussian.Newton.Resource.newtonSteps input.polynomial input.anchor +
    Grid.Resource.gridArithmeticSteps input.center input.radius +
    Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousStepBudget
      input.homogeneousCoefficients +
    Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousMultiplicationBudget
      input.homogeneousCoefficients +
    (Encoding.encode input.hurwitzSource).length +
    Data.ComplexContinuedFraction.Hurwitz.Resource.continuantArithmeticSteps
      (Encoding.encode input.hurwitzSource) +
    (Approximation.Rational.QuadraticTarget.Resource.targetCeiling input.targetCoefficient input.target + 1)
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The explicit `T`/`B` claim for the fully instrumented RFAP-II
post-processing family.  Each field names an actual trace or returned record;
the budgets themselves are computed only from the displayed input. -/
structure StageTwoResourcesWithin (input :
  StageTwoInput)
    (steps bits : Nat) : Prop where
  /-- The exact combined accounted clause count is at most the retained step budget. -/ accountedSteps :
    stageTwoAccountedSteps input ≤ steps
  /-- Every original polynomial Horner trace entry fits the retained bit budget. -/ sourceTrace : ∀ {candidate :
    Gaussian.Basic.Number},
    candidate ∈ Dense.Gaussian.Evaluation.Trace.trace input.anchor
        input.polynomial.coeffs →
      Gaussian.Resource.workingGaussianWidth candidate ≤ bits
  /-- Every derivative Horner trace entry fits the retained bit budget. -/ derivativeTrace : ∀ {candidate :
    Gaussian.Basic.Number},
    candidate ∈ Dense.Gaussian.Evaluation.Trace.trace input.anchor
        (Dense.Derivative.derivative input.polynomial).coeffs →
      Gaussian.Resource.workingGaussianWidth candidate ≤ bits
  /-- The normalized Newton center record fits the retained bit budget. -/ newtonCenter :
    Gaussian.Resource.workingGaussianWidth
      (Dense.Gaussian.Newton.Basic.newtonCenter input.polynomial input.anchor) ≤
    bits
  /-- The normalized Newton quotient record fits the retained bit budget. -/ newtonQuotient :
    Gaussian.Resource.workingGaussianWidth
      (Dense.Gaussian.Newton.Resource.normalizedNewtonQuotient input.polynomial input.anchor) ≤ bits
  /-- The grid's normalized half-to-radius quotient fits the retained bit budget. -/ gridDivision :
    Fraction.Resource.Width.rationalRecordWidth
      (Fraction.Arithmetic.normalizedDiv (1 / 2 : Fraction.Rational)
        input.radius) ≤ bits
  /-- The normalized grid-denominator times real-center product fits the retained bit budget. -/ gridRealProduct :
    Fraction.Resource.Width.rationalRecordWidth
      (Fraction.Arithmetic.normalizedMul
        (Approximation.Rational.Grid.Basic.gridDenominator input.radius : Fraction.Rational)
        input.center.re) ≤ bits
  /-- The normalized grid-denominator times imaginary-center product fits the retained bit budget. -/
    gridImaginaryProduct : Fraction.Resource.Width.rationalRecordWidth
      (Fraction.Arithmetic.normalizedMul
        (Approximation.Rational.Grid.Basic.gridDenominator input.radius : Fraction.Rational)
        input.center.im) ≤ bits
  /-- The returned common-denominator Gaussian grid record fits the retained bit budget. -/ gridRecord :
    Gaussian.Fraction.NaturalDenominator.Resource.commonFractionWidth
      (Grid.Basic.gridFraction input.center input.radius) ≤ bits
  /-- Every retained homogeneous suffix evaluation fits the bit budget. -/ homogeneousTrace : ∀ {candidate :
    GaussianInt},
    candidate ∈ Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace
      input.homogeneousNumerator
        input.homogeneousDenominator input.homogeneousCoefficients →
      GaussianInt.Resource.gaussianIntWidth candidate ≤ bits
  /-- Every emitted Gaussian-integer Hurwitz digit fits the bit budget. -/ hurwitzDigit : ∀ {candidate : GaussianInt},
    candidate ∈ Encoding.encode input.hurwitzSource →
      GaussianInt.Resource.gaussianIntWidth candidate ≤ bits
  /-- Both components of every retained continuant trace pair fit the bit budget. -/ continuantTrace : ∀ {pair :
    GaussianInt.Pair.Basic.ConvergentPair},
    pair ∈ Data.ComplexContinuedFraction.Hurwitz.Resource.continuantTrace
      (Encoding.encode
        input.hurwitzSource) →
      GaussianInt.Resource.gaussianIntWidth pair.numerator ≤ bits ∧
        GaussianInt.Resource.gaussianIntWidth pair.denominator ≤ bits
  /-- The final Hurwitz continuant numerator fits the retained bit budget. -/ continuantNumerator :
    GaussianInt.Resource.gaussianIntWidth
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
        (Encoding.encode input.hurwitzSource)).numerator ≤ bits
  /-- The final Hurwitz continuant denominator fits the retained bit budget. -/ continuantDenominator :
    GaussianInt.Resource.gaussianIntWidth
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
        (Encoding.encode input.hurwitzSource)).denominator ≤ bits
  /-- The returned quadratic-target denominator fits the retained bit budget. -/ targetDenominator :
    Data.Nat.BitWidth.natWidth
      (Approximation.Rational.QuadraticTarget.Basic.targetDenominator input.targetCoefficient
        input.target) ≤ bits
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Bit-width budget for integral homogeneous and Hurwitz records. -/
def stageTwoIntegralBitBudget (input :
  StageTwoInput) : Nat :=
  max (Data.Nat.BitWidth.natWidth
    (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousWorkingEnvelope
    input.homogeneousNumerator
    input.homogeneousDenominator input.homogeneousCoefficients))
    (max (Data.Nat.BitWidth.natWidth (Data.ComplexContinuedFraction.Hurwitz.Step.digitNormBudget
      input.hurwitzSource))
      (Data.Nat.BitWidth.natWidth (Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzContinuantNormBudget
        input.hurwitzSource)))
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Bit-width budget for normalized Newton and grid working records. -/
def stageTwoRationalBitBudget (input :
  StageTwoInput) : Nat :=
  max (Dense.Gaussian.Newton.Resource.normalizedNewtonBitBudget input.polynomial input.anchor)
    (max (Grid.Resource.gridArithmeticBitBudget input.center input.radius)
      (Grid.Resource.gridRecordBitBudget input.center input.radius))
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- A single source-computed bit-width bound for every working record named
in `StageTwoResourcesWithin`. -/
def stageTwoBitBudget (input :
  StageTwoInput) : Nat :=
  max (stageTwoRationalBitBudget input)
    (max (stageTwoIntegralBitBudget input)
      (Data.Nat.BitWidth.natWidth (Approximation.Rational.QuadraticTarget.Resource.targetCeiling input.targetCoefficient
        input.target + 1)))
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- Source recurrence bounding the sum of the same accounted clauses. -/
def stageTwoStepBudget (input :
  StageTwoInput) : Nat :=
  Dense.Gaussian.Newton.Resource.normalizedNewtonStepBudget input.polynomial input.anchor +
    Grid.Resource.gridArithmeticStepBudget input.center input.radius +
    Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousStepBudget
      input.homogeneousCoefficients +
    Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousMultiplicationBudget
      input.homogeneousCoefficients +
    Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzStepBudget input.hurwitzSource +
    Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzContinuantStepBudget input.hurwitzSource +
    Approximation.Rational.QuadraticTarget.Resource.targetComparisonBudget input.targetCoefficient input.target
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The combined accounted Newton, grid, homogeneous, Hurwitz and threshold steps fit their source-computed budget. -/
theorem stageTwoAccountedSteps_le_budget (input :
  StageTwoInput) :
    stageTwoAccountedSteps input ≤
      stageTwoStepBudget input := by
  have newton := Dense.Gaussian.Newton.Resource.normalizedNewton_steps_le_budget
    input.polynomial input.anchor
  have grid := Grid.Resource.gridArithmeticSteps_le_budget input.center input.radius
  have hurwitz := Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitz_length_le_stepBudget input.hurwitzSource
  have continuant := Data.ComplexContinuedFraction.Hurwitz.Resource.encodedContinuant_steps_le_budget
    input.hurwitzSource
  have combined := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add newton grid)
            (le_refl (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousStepBudget
              input.homogeneousCoefficients)))
          (le_refl (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousMultiplicationBudget
            input.homogeneousCoefficients))) hurwitz)
        continuant)
    (le_refl (Approximation.Rational.QuadraticTarget.Resource.targetCeiling input.targetCoefficient input.target + 1))
  simpa only [stageTwoAccountedSteps,
    stageTwoStepBudget,
    Approximation.Rational.QuadraticTarget.Resource.targetComparisonBudget,
      Data.Nat.SquareThreshold.Resource.squareThresholdComparisonBudget] using combined
end Purelib.Polynomial.Approximation.Resource.Certificate

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Polynomial.Approximation.Resource.Certificate
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt

/-- The complete stage-two package computes explicit natural numbers `T`
and `B` satisfying all named operation-count and working-width bounds. -/
theorem stageTwo_resource_certificate (input :
  StageTwoInput) :
    StageTwoResourcesWithin input
      (stageTwoStepBudget input)
      (stageTwoBitBudget input) := by
  have rationalLe : stageTwoRationalBitBudget input ≤
      stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact Purelib.Data.Nat.Order.le_max_left _ _
  have integralLe : stageTwoIntegralBitBudget input ≤
      stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact (Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)
  have targetLe :
      Data.Nat.BitWidth.natWidth (Approximation.Rational.QuadraticTarget.Resource.targetCeiling input.targetCoefficient
        input.target + 1) ≤
        stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact (Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)
  refine
    { accountedSteps := stageTwoAccountedSteps_le_budget input
      sourceTrace := ?_
      derivativeTrace := ?_
      newtonCenter := ?_
      newtonQuotient := ?_
      gridDivision := ?_
      gridRealProduct := ?_
      gridImaginaryProduct := ?_
      gridRecord := ?_
      homogeneousTrace := ?_
      hurwitzDigit := ?_
      continuantTrace := ?_
      continuantNumerator := ?_
      continuantDenominator := ?_
      targetDenominator := ?_ }
  · intro candidate member
    exact (Dense.Gaussian.Newton.Resource.normalizedNewton_sourceTrace_width_le_budget
      input.polynomial input.anchor member).trans
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans rationalLe)
  · intro candidate member
    exact (Dense.Gaussian.Newton.Resource.normalizedNewton_derivativeTrace_width_le_budget
      input.polynomial input.anchor member).trans
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans rationalLe)
  · exact (Dense.Gaussian.Newton.Resource.normalizedNewtonCenter_width_le_budget
      input.polynomial input.anchor).trans
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans rationalLe)
  · exact (Dense.Gaussian.Newton.Resource.normalizedNewtonQuotient_width_le_budget
      input.polynomial input.anchor).trans
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans rationalLe)
  · exact (Grid.Resource.gridDivision_width_le_budget input.center input.radius).trans
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans rationalLe))
  · exact (Grid.Resource.gridRealProduct_width_le_budget input.center input.radius).trans
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans rationalLe))
  · exact (Grid.Resource.gridImaginaryProduct_width_le_budget input.center input.radius).trans
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans rationalLe))
  · exact (Grid.Resource.gridFraction_width_le_budget input.center input.radius).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans rationalLe))
  · intro candidate member
    exact (GaussianInt.Resource.gaussianIntWidth_le_budget
      (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousTrace_norm_le_workingEnvelope
        input.homogeneousNumerator input.homogeneousDenominator
        input.homogeneousCoefficients member)).trans
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans integralLe)
  · intro candidate member
    exact (GaussianInt.Resource.gaussianIntWidth_le_budget
      (Encoding.encode_digit_norm_le input.hurwitzSource
        member)).trans
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans integralLe))
  · intro pair member
    have bound := Data.ComplexContinuedFraction.Hurwitz.Resource.continuantTrace_norm_le_envelope
      (fun candidate candidateMember =>
        Encoding.encode_digit_norm_le input.hurwitzSource
          candidateMember) member
    have lengthLe := Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitz_length_le_stepBudget input.hurwitzSource
    have basePositive : 0 < 2 *
        (Data.ComplexContinuedFraction.Hurwitz.Step.digitNormBudget input.hurwitzSource + 1) := by
      exact Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
    have envelopeLe : Data.ComplexContinuedFraction.Hurwitz.Resource.continuantNormEnvelope
          (Data.ComplexContinuedFraction.Hurwitz.Step.digitNormBudget input.hurwitzSource)
          (Encoding.encode input.hurwitzSource).length ≤
        Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzContinuantNormBudget input.hurwitzSource :=
      Nat.pow_le_pow_right basePositive lengthLe
    exact ⟨(GaussianInt.Resource.gaussianIntWidth_le_budget
      (bound.1.trans envelopeLe)).trans
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans integralLe)),
      (GaussianInt.Resource.gaussianIntWidth_le_budget
        (bound.2.trans envelopeLe)).trans
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans
            ((Purelib.Data.Nat.Order.le_max_right _ _).trans integralLe))⟩
  · have bound := (Data.ComplexContinuedFraction.Hurwitz.Resource.encodedContinuant_norm_le_budget
      input.hurwitzSource).1
    exact (GaussianInt.Resource.gaussianIntWidth_le_budget bound).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans integralLe))
  · have bound := (Data.ComplexContinuedFraction.Hurwitz.Resource.encodedContinuant_norm_le_budget
      input.hurwitzSource).2
    exact (GaussianInt.Resource.gaussianIntWidth_le_budget bound).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans integralLe))
  · have threshold := Data.Nat.SquareThreshold.Resource.squareThreshold_le_add_one
      (Approximation.Rational.QuadraticTarget.Resource.targetCeiling input.targetCoefficient input.target)
    have width : Data.Nat.BitWidth.natWidth
        (Approximation.Rational.QuadraticTarget.Basic.targetDenominator input.targetCoefficient
          input.target) ≤
        Data.Nat.BitWidth.natWidth (Approximation.Rational.QuadraticTarget.Resource.targetCeiling
          input.targetCoefficient input.target + 1) := by
      unfold Approximation.Rational.QuadraticTarget.Basic.targetDenominator
        Approximation.Rational.QuadraticTarget.Resource.targetCeiling
      exact Data.Nat.BitWidth.natWidth_mono threshold
    exact width.trans targetLe

end Purelib.Polynomial.Approximation.Resource.Certificate

end
