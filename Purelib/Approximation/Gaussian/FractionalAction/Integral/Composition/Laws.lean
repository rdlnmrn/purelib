module
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Laws

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.LinearAlgebra.Matrix

public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- A prepared product matrix agrees operationally with the corresponding nested fractional action.

The composition certificate supplies the inner, outer and combined denominator preparations at their exact dependent
inputs. The product order is left times right, with the right action executed first. -/
@[expose] def fractionalLinear_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation left right tau) :
    Gaussian.Equivalence.NamedEquivalent preparation.combinedOutput.name
      preparation.nestedOutput.name := by
  let innerOutput := preparation.innerOutput
  let nestedOutput := preparation.nestedOutput
  let combinedOutput := preparation.combinedOutput
  let rightDenominator := fractionalDenominator right tau
  let outerDenominator := fractionalDenominator left innerOutput
  let outerNumerator := fractionalNumerator left innerOutput
  let combinedDenominator := fractionalDenominator
    (Multiplication.mul left right) tau
  let combinedNumerator := fractionalNumerator
    (Multiplication.mul left right) tau
  have rows := Scaling.fractionalRows_mul_scaled left right tau preparation.inner
  have denominatorScaled := rows 0
  change Gaussian.Equivalence.NamedEquivalent combinedDenominator.name
    (CoherentNamed.mul
      rightDenominator outerDenominator).name at denominatorScaled
  have numeratorScaled := rows 1
  change Gaussian.Equivalence.NamedEquivalent combinedNumerator.name
    (CoherentNamed.mul
      rightDenominator outerNumerator).name at numeratorScaled
  have outerEquation : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        outerDenominator nestedOutput).name outerNumerator.name := by
    simpa only [innerOutput, nestedOutput, outerDenominator, outerNumerator,
      CompositionPreparation.innerOutput,
      CompositionPreparation.nestedOutput] using
      (denominator_mul_fractionalLinear left
        preparation.innerOutput preparation.outer)
  have combinedNested : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        combinedDenominator nestedOutput).name combinedNumerator.name := by
    apply NamedEquivalent.trans
    · exact Congruence.coherentMul_respects
        combinedDenominator
        (CoherentNamed.mul
          rightDenominator outerDenominator)
        nestedOutput nestedOutput denominatorScaled
        (NamedEquivalent.refl nestedOutput.name)
    · apply NamedEquivalent.trans
      · simpa only [CoherentNamed.mul] using
          Laws.coherentMul_assoc
            rightDenominator outerDenominator nestedOutput
      · apply NamedEquivalent.trans
        · exact Congruence.coherentMul_respects
            rightDenominator rightDenominator
            (CoherentNamed.mul
              outerDenominator nestedOutput)
            outerNumerator
            (NamedEquivalent.refl
              rightDenominator.name) outerEquation
        · exact NamedEquivalent.symm numeratorScaled
  have preparedNested : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        preparation.combined.prepared nestedOutput).name
      combinedNumerator.name :=
    NamedEquivalent.trans
      (Congruence.coherentMul_respects
        preparation.combined.prepared combinedDenominator
        nestedOutput nestedOutput
        (NamedEquivalent.symm
          preparation.combined.equivalent)
        (NamedEquivalent.refl nestedOutput.name))
      combinedNested
  have preparedCombined : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        preparation.combined.prepared combinedOutput).name
      combinedNumerator.name := by
    simpa only [combinedOutput, combinedNumerator,
      CompositionPreparation.combinedOutput] using
      (prepared_denominator_mul_fractionalLinear
        (Multiplication.mul left right) tau
        preparation.combined)
  change Gaussian.Equivalence.NamedEquivalent combinedOutput.name nestedOutput.name
  exact Cancellation.coherentMul_cancel_left
    preparation.combined.prepared combinedOutput nestedOutput
    preparation.combined.apart
    (NamedEquivalent.trans preparedCombined
      (NamedEquivalent.symm preparedNested))

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Laws
