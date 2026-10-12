module
public import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Arithmetic.Exact
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

namespace Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

open Purelib
open Purelib.Data
open Purelib.Polynomial

section
public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

open Purelib.Approximation

/-- Stateful high-to-low Horner evaluation starting from one coherent
accumulator. -/
@[expose] def horner (input :
  Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    Approximation.Gaussian.Name.Coherent.CoherentNamed → List
      Gaussian.Basic.Canonical →
      Approximation.Gaussian.Name.Coherent.CoherentNamed
  | accumulator, [] => accumulator
  | accumulator, coefficient :: coefficients =>
      Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.horner input
        (Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          (Approximation.Gaussian.Name.Coherent.CoherentNamed.mul
            accumulator input)
          (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
            coefficient))
        coefficients

/-- Horner evaluation respects finite operational equality in both the input
and initial accumulator. -/
@[expose] def horner_respects
    (leftInput rightInput leftAccumulator rightAccumulator :
      Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent leftInput.name rightInput.name)
    (accumulatorEquivalent :
      Gaussian.Equivalence.NamedEquivalent leftAccumulator.name rightAccumulator.name) :
    (coefficients : List Gaussian.Basic.Canonical) →
      Gaussian.Equivalence.NamedEquivalent
        (Approximation.Gaussian.Evaluation.Horner.horner leftInput leftAccumulator coefficients).name
        (Approximation.Gaussian.Evaluation.Horner.horner rightInput rightAccumulator coefficients).name
  | [] => accumulatorEquivalent
  | coefficient :: coefficients => by
      let exactCoefficient :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact coefficient
      let leftProduct :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.mul
          leftAccumulator leftInput
      let rightProduct :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.mul
          rightAccumulator rightInput
      let leftStep :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          leftProduct exactCoefficient
      let rightStep :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          rightProduct exactCoefficient
      have products : Gaussian.Equivalence.NamedEquivalent leftProduct.name rightProduct.name :=
        Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects leftAccumulator
          rightAccumulator
          leftInput rightInput accumulatorEquivalent inputEquivalent
      have steps : Gaussian.Equivalence.NamedEquivalent leftStep.name rightStep.name :=
        Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects leftProduct rightProduct
          exactCoefficient exactCoefficient products
          (Approximation.Gaussian.Equivalence.NamedEquivalent.refl
            exactCoefficient.name)
      simpa only [Approximation.Gaussian.Evaluation.Horner.horner, leftStep, rightStep, leftProduct, rightProduct,
        exactCoefficient] using
        Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.horner_respects leftInput rightInput leftStep
          rightStep
          inputEquivalent steps coefficients

/-- Exact rational specialization of the finite Horner process. -/
@[expose] def horner_exact (input accumulator : Gaussian.Basic.Canonical) :
    (coefficients : List Gaussian.Basic.Canonical) →
      Gaussian.Equivalence.NamedEquivalent
        (Approximation.Gaussian.Evaluation.Horner.horner
          (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact input)
          (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact accumulator)
          coefficients).name
        (Approximation.Gaussian.Name.Basic.Named.exact
          (coefficients.foldl
            (fun value coefficient => value * input + coefficient)
            accumulator))
  | [] =>
      Approximation.Gaussian.Equivalence.NamedEquivalent.refl _
  | coefficient :: coefficients => by
      let exactInput :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact input
      let actualProduct :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.mul
          (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact accumulator)
          exactInput
      let exactProduct :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
          (accumulator * input)
      let exactCoefficient :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact coefficient
      let actualStep :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          actualProduct exactCoefficient
      let exactStep :=
        Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
          (accumulator * input + coefficient)
      have productEquivalent : Gaussian.Equivalence.NamedEquivalent
          actualProduct.name exactProduct.name := by
        simpa only [actualProduct, exactProduct, exactInput,
          Approximation.Gaussian.Name.Coherent.CoherentNamed.mul,
          Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact] using
          Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact.exactMul_named_equivalent
            accumulator input
      have stepToExactOperands : Gaussian.Equivalence.NamedEquivalent actualStep.name
          (Approximation.Gaussian.Name.Basic.Named.add
            exactProduct.name exactCoefficient.name) :=
        Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects actualProduct exactProduct
          exactCoefficient exactCoefficient productEquivalent
          (Approximation.Gaussian.Equivalence.NamedEquivalent.refl
            exactCoefficient.name)
      have stepEquivalent : Gaussian.Equivalence.NamedEquivalent actualStep.name exactStep.name :=
        Approximation.Gaussian.Equivalence.NamedEquivalent.trans
          stepToExactOperands
          (by
            simpa only [exactProduct, exactCoefficient, exactStep,
              Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact] using
              Approximation.Gaussian.Arithmetic.Exact.exactAdd_named_equivalent (accumulator * input) coefficient)
      have remainingRespect := Approximation.Gaussian.Evaluation.Horner.horner_respects exactInput exactInput
        actualStep exactStep
        (Approximation.Gaussian.Equivalence.NamedEquivalent.refl
          exactInput.name)
        stepEquivalent coefficients
      exact Approximation.Gaussian.Equivalence.NamedEquivalent.trans
        (middle := (Approximation.Gaussian.Evaluation.Horner.horner exactInput exactStep coefficients).name)
        (by simpa only [Approximation.Gaussian.Evaluation.Horner.horner, actualStep, actualProduct, exactCoefficient,
            exactInput] using remainingRespect)
        (by simpa only [List.foldl_cons] using
          Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.horner_exact input (accumulator * input +
            coefficient) coefficients)

/-- Coherent polynomial evaluation by actual CCL Horner arithmetic. -/
@[expose] def polynomialEval (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Approximation.Gaussian.Name.Coherent.CoherentNamed) :
      Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  Approximation.Gaussian.Evaluation.Horner.horner input
    (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0)
    polynomial.coeffs

/-- At a displayed rational input, CCL Horner evaluation retains the exact polynomial value.

The original ordered coefficient list is folded from the exact zero
accumulator. The exact-input certificate compares that same finite fold
with its terminating rational readback. -/
@[expose] def polynomialEval_exact (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Evaluation.Horner.polynomialEval polynomial
        (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact input)).name
      (Approximation.Gaussian.Name.Basic.Named.exact
        (polynomial.eval input)) := by
  exact Approximation.Gaussian.Evaluation.Horner.horner_exact input 0 polynomial.coeffs

end

public section

/-!+# Evaluating finite factored primitives at retained square-root names

The coefficient identity for F(t)=t G(t²) transports through the existing
operational Horner evaluator. Only the supplied coordinate's square law is
used; its finite rational readings need not square exactly to the parameter.
-/

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)

section
/-- Horner evaluation of concatenated coefficient tables equals consecutive evaluation with the retained intermediate
accumulator. -/
public theorem horner_append (input initial :
  Approximation.Gaussian.Name.Coherent.CoherentNamed) (first last : List Gaussian.Basic.Canonical) :
    Approximation.Gaussian.Evaluation.Horner.horner input initial (first ++ last) =
      Approximation.Gaussian.Evaluation.Horner.horner input (Approximation.Gaussian.Evaluation.Horner.horner input
      initial first) last := by
  induction first generalizing initial with
  | nil => rfl
  | cons coefficient remaining previous =>
      exact previous (Approximation.Gaussian.Name.Coherent.CoherentNamed.add
        (Approximation.Gaussian.Name.Coherent.CoherentNamed.mul initial input) (exact coefficient))
end

end

end

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
