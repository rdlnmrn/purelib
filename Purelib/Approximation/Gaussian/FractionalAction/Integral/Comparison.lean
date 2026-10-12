module
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Vector.Operational.Basic

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.LinearAlgebra.Matrix
open Purelib.Riemann.Integration

section
public section

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance
automatically constructs and transports an all-row provider. Otherwise one
signed numerical inspection prepares either half-plane, or returns retained
near-boundary evidence. Nonzeroness of the input alone is not used as a
certificate for every intermediate word denominator. Real inputs and
unsupported symbolic provenance may remain inconclusive by this sufficient
test; this is not a decision procedure for each particular real word.
-/

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- Equivalent coherent inputs have equivalent fractional denominators for the same integral matrix.

The comparison is the denominator row of the homogeneous matrix action and requires no apartness or division
certificate. -/
@[expose] def denominatorComparison (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    {first second : Coherent.CoherentNamed} (equivalent : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      first.name second.name) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator matrix first).name
      (LegendreModularMonodromy.fractionalDenominator matrix second).name := by
  have rows := Action.matrixAction_respects matrix
    (Homogeneous.fractionalVector_respects equivalent)
  simpa only [LegendreModularMonodromy.fractionalDenominator,
    LegendreModularMonodromy.fractionalRow] using rows 0

end

public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- Productive fractional output is independent of which successful apartification certificate prepared the same exact
denominator process. -/
@[expose] def fractionalLinear_preparation_independent (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed)
    (first second : Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Gaussian.Equivalence.NamedEquivalent (fractionalLinear matrix tau first).name
      (fractionalLinear matrix tau second).name := by
  let denominator := fractionalDenominator matrix tau
  let numerator := fractionalNumerator matrix tau
  let firstOutput := fractionalLinear matrix tau first
  let secondOutput := fractionalLinear matrix tau second
  have firstScaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        first.prepared firstOutput).name numerator.name := by
    simpa only [firstOutput, numerator,
      CoherentNamed.mul] using
      (prepared_denominator_mul_fractionalLinear matrix tau first)
  have secondScaledByFirst : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        first.prepared secondOutput).name numerator.name :=
    Gaussian.Equivalence.NamedEquivalent.trans
      (Congruence.coherentMul_respects
        first.prepared denominator secondOutput secondOutput
        (Gaussian.Equivalence.NamedEquivalent.symm first.equivalent)
        (Gaussian.Equivalence.NamedEquivalent.refl secondOutput.name))
      (by
          simpa only [denominator, numerator, secondOutput, CoherentNamed.mul]
            using (denominator_mul_fractionalLinear matrix tau second))
  change Gaussian.Equivalence.NamedEquivalent firstOutput.name secondOutput.name
  exact Cancellation.coherentMul_cancel_left
    first.prepared firstOutput secondOutput first.apart
    (Gaussian.Equivalence.NamedEquivalent.trans firstScaled
      (Gaussian.Equivalence.NamedEquivalent.symm secondScaledByFirst))

/-- Productive fractional action respects an operationally equivalent input, while retaining independently prepared
denominators at the two exact input processes.

This is the rebasing step needed to compare genuine stepwise word executions rather than only their single folded-matrix
representatives. -/
@[expose] def fractionalLinear_respects (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (first second : Coherent.CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name)
    (firstPreparation : Prepared.DenominatorPreparation
      (fractionalDenominator matrix first))
    (secondPreparation : Prepared.DenominatorPreparation
      (fractionalDenominator matrix second)) :
    Gaussian.Equivalence.NamedEquivalent
      (fractionalLinear matrix first firstPreparation).name
      (fractionalLinear matrix second secondPreparation).name := by
  let firstDenominator := fractionalDenominator matrix first
  let secondDenominator := fractionalDenominator matrix second
  let firstNumerator := fractionalNumerator matrix first
  let secondNumerator := fractionalNumerator matrix second
  let firstOutput := fractionalLinear matrix first firstPreparation
  let secondOutput := fractionalLinear matrix second secondPreparation
  have rows := Action.matrixAction_respects matrix
    (Homogeneous.fractionalVector_respects equivalent)
  have denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent firstDenominator.name
      secondDenominator.name := by
    simpa only [firstDenominator, secondDenominator, fractionalDenominator,
      fractionalRow] using rows 0
  have numeratorEquivalent : Gaussian.Equivalence.NamedEquivalent firstNumerator.name
      secondNumerator.name := by
    simpa only [firstNumerator, secondNumerator, fractionalNumerator,
      fractionalRow] using rows 1
  have firstScaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        firstPreparation.prepared firstOutput).name firstNumerator.name := by
    simpa only [firstOutput, firstNumerator] using
      (prepared_denominator_mul_fractionalLinear matrix first firstPreparation)
  have secondScaledByFirst : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        firstPreparation.prepared secondOutput).name firstNumerator.name :=
    Gaussian.Equivalence.NamedEquivalent.trans
      (Congruence.coherentMul_respects
        firstPreparation.prepared firstDenominator secondOutput secondOutput
        (Gaussian.Equivalence.NamedEquivalent.symm
          firstPreparation.equivalent)
        (Gaussian.Equivalence.NamedEquivalent.refl secondOutput.name))
      (Gaussian.Equivalence.NamedEquivalent.trans
        (Congruence.coherentMul_respects
          firstDenominator secondDenominator secondOutput secondOutput
          denominatorEquivalent
          (Gaussian.Equivalence.NamedEquivalent.refl secondOutput.name))
        (Gaussian.Equivalence.NamedEquivalent.trans
          (by
              simpa only [secondDenominator, secondNumerator, secondOutput, CoherentNamed.mul]
                using (denominator_mul_fractionalLinear matrix second secondPreparation))
          (Gaussian.Equivalence.NamedEquivalent.symm
            numeratorEquivalent)))
  change Gaussian.Equivalence.NamedEquivalent firstOutput.name secondOutput.name
  exact Cancellation.coherentMul_cancel_left
    firstPreparation.prepared firstOutput secondOutput firstPreparation.apart
    (Gaussian.Equivalence.NamedEquivalent.trans firstScaled
      (Gaussian.Equivalence.NamedEquivalent.symm secondScaledByFirst))

/-- Exact matrix equality transports productive fractional output even when the two equal matrix expressions were
prepared independently. -/
@[expose] def fractionalLinear_of_matrix_eq {left right : LinearAlgebra.Matrix.Basic.IntegralMatrix}
    (matrixEq : left = right) (tau : Coherent.CoherentNamed)
    (leftPreparation : Prepared.DenominatorPreparation
      (fractionalDenominator left tau))
    (rightPreparation : Prepared.DenominatorPreparation
      (fractionalDenominator right tau)) :
    Gaussian.Equivalence.NamedEquivalent (fractionalLinear left tau leftPreparation).name
      (fractionalLinear right tau rightPreparation).name := by
  subst right
  exact Approximation.Gaussian.FractionalAction.Integral.Comparison.fractionalLinear_preparation_independent left tau
    leftPreparation rightPreparation

end

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
