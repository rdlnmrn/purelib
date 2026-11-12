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

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence

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

/-- One original Horner step's retained coefficient, numerical product and updated accumulator.

The view stores existing coherent-name owners and exact construction equations.
Its output consumes those actual cached operands, rather than evaluating a
prefix of the coefficient list again.
-/
abbrev Step (input initial : CoherentNamed) (coefficient : Gaussian.Basic.Canonical) :=
  (scalar : {channel : CoherentNamed // channel = CoherentNamed.Coherence.exact coefficient}) ×
    (product : {channel : CoherentNamed // channel = CoherentNamed.mul initial input}) ×
      {channel : CoherentNamed // channel = CoherentNamed.add product.val scalar.val}

namespace Step

/-- Read the original retained exact coefficient channel. -/
abbrev scalar {input initial : CoherentNamed} {coefficient : Gaussian.Basic.Canonical}
    (step : Step input initial coefficient) := step.1

/-- Read the actual original product of this accumulator and retained input. -/
abbrev product {input initial : CoherentNamed} {coefficient : Gaussian.Basic.Canonical}
    (step : Step input initial coefficient) := step.2.1

/-- Read the actual updated original accumulator. -/
abbrev output {input initial : CoherentNamed} {coefficient : Gaussian.Basic.Canonical}
    (step : Step input initial coefficient) := step.2.2.val

/-- The retained output is the original Horner multiply-and-add operation on these exact inputs. -/
theorem output_eq {input initial : CoherentNamed} {coefficient : Gaussian.Basic.Canonical}
    (step : Step input initial coefficient) : step.output =
      CoherentNamed.add (CoherentNamed.mul initial input) (CoherentNamed.Coherence.exact coefficient) :=
  step.2.2.property.trans (congrArg₂ CoherentNamed.add step.product.property step.scalar.property)

end Step

/-- Build one original Horner coefficient step once, retaining all actual operands and its output. -/
@[expose] def step (input initial : CoherentNamed) (coefficient : Gaussian.Basic.Canonical) :
    Step input initial coefficient :=
  let scalar := CoherentNamed.Coherence.exact coefficient
  let product := CoherentNamed.mul initial input
  let output := CoherentNamed.add product scalar
  ⟨⟨scalar, rfl⟩, ⟨product, rfl⟩, ⟨output, rfl⟩⟩

/-- Every valid retained coefficient step has the complete original constructor result. -/
theorem Step.eq_step {input initial : CoherentNamed} {coefficient : Gaussian.Basic.Canonical}
    (retained : Step input initial coefficient) : retained = step input initial coefficient := by
  rcases retained with ⟨⟨scalar, scalarEq⟩, ⟨product, productEq⟩, ⟨output, outputEq⟩⟩
  cases scalarEq
  cases productEq
  cases outputEq
  rfl

/-- The stored original Horner coefficient steps, with every tail indexed by its actual retained accumulator. -/
@[expose] def Accumulations (input : CoherentNamed) :
    CoherentNamed → List Gaussian.Basic.Canonical → Type 1
  | _, [] => PUnit
  | initial, coefficient :: remaining =>
      (current : Step input initial coefficient) × Accumulations input current.output remaining

/-- Retain the finite Horner execution, sharing the same original coefficient-step builder at every occurrence. -/
@[expose] def retain (input : CoherentNamed) :
    (initial : CoherentNamed) → (coefficients : List Gaussian.Basic.Canonical) →
      Accumulations input initial coefficients
  | _, [] => PUnit.unit
  | initial, coefficient :: remaining =>
      let current := step input initial coefficient
      ⟨current, retain input current.output remaining⟩

/-- Read the last actual stored original accumulator, without invoking the coefficient-step builder. -/
@[expose] def Accumulations.output (input : CoherentNamed) :
    (initial : CoherentNamed) → (coefficients : List Gaussian.Basic.Canonical) →
      Accumulations input initial coefficients → CoherentNamed
  | initial, [], _ => initial
  | _, _ :: remaining, retained => output input retained.1.output remaining retained.2

/-- Every retained coefficient execution has the same complete original step inventory. -/
theorem Accumulations.eq_retain (input : CoherentNamed) :
    (initial : CoherentNamed) → (coefficients : List Gaussian.Basic.Canonical) →
    (retained : Accumulations input initial coefficients) → retained = retain input initial coefficients
  | _, [], retained => by cases retained; rfl
  | initial, coefficient :: remaining, ⟨current, tail⟩ => by
      cases current.eq_step
      have same := eq_retain input (step input initial coefficient).output remaining tail
      cases same
      rfl

/-- Stateful high-to-low Horner evaluation using the same original coefficient-step builder. -/
@[expose] def horner (input : CoherentNamed) :
    CoherentNamed → List Gaussian.Basic.Canonical → CoherentNamed
  | initial, [] => initial
  | initial, coefficient :: remaining => horner input (step input initial coefficient).output remaining

/-- The original empty coefficient equation retains its complete supplied accumulator. -/
theorem horner_nil (input initial : CoherentNamed) : horner input initial [] = initial := rfl

/-- The original nonempty coefficient equation uses the same original multiply-and-add step and unchanged tail. -/
theorem horner_cons (input initial : CoherentNamed) (coefficient : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) : horner input initial (coefficient :: remaining) =
      horner input (CoherentNamed.add (CoherentNamed.mul initial input) (CoherentNamed.Coherence.exact coefficient))
        remaining := rfl

/-- Every valid retained Horner execution has the same complete original numerical output.

The equality concerns coherent names, including their original processes and
states. It does not identify functions extensionally or choose new input owners.
-/
theorem Accumulations.output_eq (input : CoherentNamed) :
    (initial : CoherentNamed) → (coefficients : List Gaussian.Basic.Canonical) →
    (retained : Accumulations input initial coefficients) → retained.output input initial coefficients =
      horner input initial coefficients
  | _, [], _ => rfl
  | initial, coefficient :: remaining, retained =>
      (output_eq input retained.1.output remaining retained.2).trans
        ((congrArg (fun accumulator => horner input accumulator remaining) retained.1.output_eq).trans
          (horner_cons input initial coefficient remaining).symm)

/-- Horner evaluation respects finite operational equality in both the input
and initial accumulator. -/
@[expose] def horner_respects
    (leftInput rightInput leftAccumulator rightAccumulator :
      CoherentNamed)
    (inputEquivalent : NamedEquivalent leftInput.name rightInput.name)
    (accumulatorEquivalent :
      NamedEquivalent leftAccumulator.name rightAccumulator.name) :
    (coefficients : List Gaussian.Basic.Canonical) →
      NamedEquivalent
        (horner leftInput leftAccumulator coefficients).name
        (horner rightInput rightAccumulator coefficients).name
  | [] => accumulatorEquivalent
  | coefficient :: coefficients => by
      let exactCoefficient :=
        CoherentNamed.Coherence.exact coefficient
      let leftProduct :=
        CoherentNamed.mul
          leftAccumulator leftInput
      let rightProduct :=
        CoherentNamed.mul
          rightAccumulator rightInput
      let leftStep :=
        CoherentNamed.add
          leftProduct exactCoefficient
      let rightStep :=
        CoherentNamed.add
          rightProduct exactCoefficient
      have products : NamedEquivalent leftProduct.name rightProduct.name :=
        Arithmetic.Product.Congruence.coherentMul_respects leftAccumulator
          rightAccumulator
          leftInput rightInput accumulatorEquivalent inputEquivalent
      have steps : NamedEquivalent leftStep.name rightStep.name :=
        Arithmetic.Sum.Congruence.coherentAdd_respects leftProduct rightProduct
          exactCoefficient exactCoefficient products
          (NamedEquivalent.refl
            exactCoefficient.name)
      simpa only [horner_cons, leftStep, rightStep, leftProduct, rightProduct,
        exactCoefficient] using
        Horner.horner_respects leftInput rightInput leftStep
          rightStep
          inputEquivalent steps coefficients

/-- Exact rational specialization of the finite Horner process. -/
@[expose] def horner_exact (input accumulator : Gaussian.Basic.Canonical) :
    (coefficients : List Gaussian.Basic.Canonical) →
      NamedEquivalent
        (horner
          (CoherentNamed.Coherence.exact input)
          (CoherentNamed.Coherence.exact accumulator)
          coefficients).name
        (Gaussian.Name.Basic.Named.exact
          (coefficients.foldl
            (fun value coefficient => value * input + coefficient)
            accumulator))
  | [] =>
      NamedEquivalent.refl _
  | coefficient :: coefficients => by
      let exactInput :=
        CoherentNamed.Coherence.exact input
      let actualProduct :=
        CoherentNamed.mul
          (CoherentNamed.Coherence.exact accumulator)
          exactInput
      let exactProduct :=
        CoherentNamed.Coherence.exact
          (accumulator * input)
      let exactCoefficient :=
        CoherentNamed.Coherence.exact coefficient
      let actualStep :=
        CoherentNamed.add
          actualProduct exactCoefficient
      let exactStep :=
        CoherentNamed.Coherence.exact
          (accumulator * input + coefficient)
      have productEquivalent : NamedEquivalent
          actualProduct.name exactProduct.name := by
        simpa only [actualProduct, exactProduct, exactInput,
          CoherentNamed.mul,
          CoherentNamed.Coherence.exact] using
          Arithmetic.Product.Exact.exactMul_named_equivalent
            accumulator input
      have stepToExactOperands : NamedEquivalent actualStep.name
          (Gaussian.Name.Basic.Named.add
            exactProduct.name exactCoefficient.name) :=
        Arithmetic.Sum.Congruence.coherentAdd_respects actualProduct exactProduct
          exactCoefficient exactCoefficient productEquivalent
          (NamedEquivalent.refl
            exactCoefficient.name)
      have stepEquivalent : NamedEquivalent actualStep.name exactStep.name :=
        NamedEquivalent.trans
          stepToExactOperands
          (by
            simpa only [exactProduct, exactCoefficient, exactStep,
              CoherentNamed.Coherence.exact] using
              Gaussian.Arithmetic.Exact.exactAdd_named_equivalent (accumulator * input) coefficient)
      have remainingRespect := horner_respects exactInput exactInput
        actualStep exactStep
        (NamedEquivalent.refl
          exactInput.name)
        stepEquivalent coefficients
      exact NamedEquivalent.trans
        (middle := (horner exactInput exactStep coefficients).name)
        (by simpa only [horner_cons, actualStep, actualProduct, exactCoefficient,
            exactInput] using remainingRespect)
        (by simpa only [List.foldl_cons] using
          Horner.horner_exact input (accumulator * input +
            coefficient) coefficients)

/-- Coherent polynomial evaluation by actual CCL Horner arithmetic. -/
@[expose] def polynomialEval (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : CoherentNamed) :
      CoherentNamed :=
  horner input
    (CoherentNamed.Coherence.exact 0)
    polynomial.coeffs

/-- At a displayed rational input, CCL Horner evaluation retains the exact polynomial value.

The original ordered coefficient list is folded from the exact zero
accumulator. The exact-input certificate compares that same finite fold
with its terminating rational readback. -/
@[expose] def polynomialEval_exact (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    NamedEquivalent
      (polynomialEval polynomial
        (CoherentNamed.Coherence.exact input)).name
      (Gaussian.Name.Basic.Named.exact
        (polynomial.eval input)) := by
  exact horner_exact input 0 polynomial.coeffs

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
  CoherentNamed) (first last : List Gaussian.Basic.Canonical) :
    horner input initial (first ++ last) =
      horner input (horner input
      initial first) last := by
  induction first generalizing initial with
  | nil => rfl
  | cons coefficient remaining previous =>
      exact previous (CoherentNamed.add
        (CoherentNamed.mul initial input) (exact coefficient))
end

end

end

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
