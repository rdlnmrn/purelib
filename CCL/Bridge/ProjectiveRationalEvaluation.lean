import CCL.Arithmetic.CertifiedExpression
import CCL.Bridge.Rational

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

namespace CCL.ProjectiveRationalEvaluation

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Expression := CCL.CertifiedExpression.Expression

open CCL.OperationalFieldLaws
open CCL.TranscendentalCoherence

/-- Actual addition of two terminating displayed Gaussian-rational names. -/
def exactAdd_named_equivalent (left right : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.exact left)
        (CCL.ProgressiveTransducer.Named.exact right))
      (CCL.ProgressiveTransducer.Named.exact (left + right)) :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples
    _ _ (left + right) (by intro index; rfl) (by intro index; rfl)

/-- Stateful high-to-low Horner evaluation starting from one coherent
accumulator. -/
def horner (input : CoherentNamed) :
    CoherentNamed → List Gaussian → CoherentNamed
  | accumulator, [] => accumulator
  | accumulator, coefficient :: coefficients =>
      horner input
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (CCL.ProgressiveCoherence.CoherentNamed.mul
            accumulator input)
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            coefficient))
        coefficients

/-- Horner evaluation respects finite operational equality in both the input
and initial accumulator. -/
def horner_respects
    (leftInput rightInput leftAccumulator rightAccumulator : CoherentNamed)
    (inputEquivalent : NamedEquivalent leftInput.name rightInput.name)
    (accumulatorEquivalent :
      NamedEquivalent leftAccumulator.name rightAccumulator.name) :
    (coefficients : List Gaussian) →
      NamedEquivalent
        (horner leftInput leftAccumulator coefficients).name
        (horner rightInput rightAccumulator coefficients).name
  | [] => accumulatorEquivalent
  | coefficient :: coefficients => by
      let exactCoefficient :=
        CCL.ProgressiveCoherence.CoherentNamed.exact coefficient
      let leftProduct :=
        CCL.ProgressiveCoherence.CoherentNamed.mul
          leftAccumulator leftInput
      let rightProduct :=
        CCL.ProgressiveCoherence.CoherentNamed.mul
          rightAccumulator rightInput
      let leftStep :=
        CCL.ProgressiveCoherence.CoherentNamed.add
          leftProduct exactCoefficient
      let rightStep :=
        CCL.ProgressiveCoherence.CoherentNamed.add
          rightProduct exactCoefficient
      have products : NamedEquivalent leftProduct.name rightProduct.name :=
        coherentMul_respects leftAccumulator rightAccumulator
          leftInput rightInput accumulatorEquivalent inputEquivalent
      have steps : NamedEquivalent leftStep.name rightStep.name :=
        coherentAdd_respects leftProduct rightProduct
          exactCoefficient exactCoefficient products
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            exactCoefficient.name)
      simpa only [horner, leftStep, rightStep, leftProduct, rightProduct,
        exactCoefficient] using
        horner_respects leftInput rightInput leftStep rightStep
          inputEquivalent steps coefficients

/-- Exact rational specialization of the finite Horner process. -/
def horner_exact (input accumulator : Gaussian) :
    (coefficients : List Gaussian) →
      NamedEquivalent
        (horner
          (CCL.ProgressiveCoherence.CoherentNamed.exact input)
          (CCL.ProgressiveCoherence.CoherentNamed.exact accumulator)
          coefficients).name
        (CCL.ProgressiveTransducer.Named.exact
          (coefficients.foldl
            (fun value coefficient => value * input + coefficient)
            accumulator))
  | [] =>
      CCL.OperationalEquivalence.NamedEquivalent.refl _
  | coefficient :: coefficients => by
      let exactInput :=
        CCL.ProgressiveCoherence.CoherentNamed.exact input
      let actualProduct :=
        CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact accumulator)
          exactInput
      let exactProduct :=
        CCL.ProgressiveCoherence.CoherentNamed.exact
          (accumulator * input)
      let exactCoefficient :=
        CCL.ProgressiveCoherence.CoherentNamed.exact coefficient
      let actualStep :=
        CCL.ProgressiveCoherence.CoherentNamed.add
          actualProduct exactCoefficient
      let exactStep :=
        CCL.ProgressiveCoherence.CoherentNamed.exact
          (accumulator * input + coefficient)
      have productEquivalent : NamedEquivalent
          actualProduct.name exactProduct.name := by
        simpa only [actualProduct, exactProduct, exactInput,
          CCL.ProgressiveCoherence.CoherentNamed.mul,
          CCL.ProgressiveCoherence.CoherentNamed.exact] using
          exactMul_named_equivalent accumulator input
      have stepToExactOperands : NamedEquivalent actualStep.name
          (CCL.ProgressiveTransducer.Named.add
            exactProduct.name exactCoefficient.name) :=
        coherentAdd_respects actualProduct exactProduct
          exactCoefficient exactCoefficient productEquivalent
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            exactCoefficient.name)
      have stepEquivalent : NamedEquivalent actualStep.name exactStep.name :=
        CCL.OperationalEquivalence.NamedEquivalent.trans
          stepToExactOperands
          (by
            simpa only [exactProduct, exactCoefficient, exactStep,
              CCL.ProgressiveCoherence.CoherentNamed.exact] using
              exactAdd_named_equivalent (accumulator * input) coefficient)
      have remainingRespect := horner_respects exactInput exactInput
        actualStep exactStep
        (CCL.OperationalEquivalence.NamedEquivalent.refl
          exactInput.name)
        stepEquivalent coefficients
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [horner, actualStep, actualProduct, exactCoefficient,
            exactInput] using remainingRespect)
        (by simpa only [List.foldl_cons] using
          horner_exact input (accumulator * input + coefficient) coefficients)

/-- Coherent polynomial evaluation by actual CCL Horner arithmetic. -/
def polynomialEval (polynomial : GaussianPolynomial)
    (input : CoherentNamed) : CoherentNamed :=
  horner input
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
    polynomial.coeffs

/-- At a displayed rational input, CCL Horner evaluation is operationally
the terminating exact rational polynomial value. -/
def polynomialEval_exact (polynomial : GaussianPolynomial)
    (input : Gaussian) :
    NamedEquivalent
      (polynomialEval polynomial
        (CCL.ProgressiveCoherence.CoherentNamed.exact input)).name
      (CCL.ProgressiveTransducer.Named.exact
        (polynomial.eval input)) := by
  simpa only [polynomialEval, RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs] using
    horner_exact input 0 polynomial.coeffs

/-- Expression-tree form of polynomial Horner evaluation. -/
def polynomialExpression (polynomial : GaussianPolynomial)
    (input : Expression) : Expression :=
  polynomial.coeffs.foldl
    (fun accumulator coefficient =>
      CCL.CertifiedExpression.Expression.add
        (CCL.CertifiedExpression.Expression.mul accumulator input)
        (CCL.CertifiedExpression.Expression.exact coefficient))
    (CCL.CertifiedExpression.Expression.exact 0)

private theorem expressionHorner_output (input accumulator : Expression) :
    (coefficients : List Gaussian) →
      (coefficients.foldl
        (fun current coefficient =>
          CCL.CertifiedExpression.Expression.add
            (CCL.CertifiedExpression.Expression.mul current input)
            (CCL.CertifiedExpression.Expression.exact coefficient))
        accumulator).output =
      horner input.output accumulator.output coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      simpa only [List.foldl_cons, horner,
        CCL.CertifiedExpression.Expression.add,
        CCL.CertifiedExpression.Expression.mul,
        CCL.CertifiedExpression.Expression.exact,
        CCL.CertifiedExpression.Expression.leaf] using
        expressionHorner_output input
          (CCL.CertifiedExpression.Expression.add
            (CCL.CertifiedExpression.Expression.mul
              accumulator input)
            (CCL.CertifiedExpression.Expression.exact coefficient))
          coefficients

theorem polynomialExpression_output (polynomial : GaussianPolynomial)
    (input : Expression) :
    (polynomialExpression polynomial input).output =
      polynomialEval polynomial input.output := by
  exact expressionHorner_output input
    (CCL.CertifiedExpression.Expression.exact 0)
    polynomial.coeffs

/-- Exact rational specialization of the public expression-tree evaluator. -/
def polynomialExpression_exact (polynomial : GaussianPolynomial)
    (input : Gaussian) :
    NamedEquivalent
      (polynomialExpression polynomial
        (CCL.CertifiedExpression.Expression.exact input)).output.name
      (CCL.ProgressiveTransducer.Named.exact
        (polynomial.eval input)) := by
  rw [polynomialExpression_output]
  simpa only [CCL.CertifiedExpression.Expression.exact,
    CCL.CertifiedExpression.Expression.leaf] using
    polynomialEval_exact polynomial input

/-- A rational-function value represented projectively by its two actual CCL
Horner processes.  The denominator may approach or equal zero. -/
structure ProjectiveEvaluation where
  numerator : Expression
  denominator : Expression

/-- Construct projective evaluation without any denominator decision. -/
def evaluate (numerator denominator : GaussianPolynomial)
    (input : Expression) : ProjectiveEvaluation :=
  { numerator := polynomialExpression numerator input
    denominator := polynomialExpression denominator input }

/-- Exact rational specialization of both projective coordinates. -/
structure ExactEvaluation
    (evaluation : ProjectiveEvaluation)
    (numeratorValue denominatorValue : Gaussian) where
  numeratorExact : NamedEquivalent evaluation.numerator.output.name
    (CCL.ProgressiveTransducer.Named.exact numeratorValue)
  denominatorExact : NamedEquivalent evaluation.denominator.output.name
    (CCL.ProgressiveTransducer.Named.exact denominatorValue)

/-- At a displayed rational input, the projective CCL pair is operationally
the exact displayed pair of polynomial evaluations. -/
def evaluate_exact (numerator denominator : GaussianPolynomial)
    (input : Gaussian) :
    ExactEvaluation
      (evaluate numerator denominator
        (CCL.CertifiedExpression.Expression.exact input))
      (numerator.eval input) (denominator.eval input) :=
  { numeratorExact := polynomialExpression_exact numerator input
    denominatorExact := polynomialExpression_exact denominator input }

namespace ProjectiveEvaluation

/-- Enter the ordinary affine chart only from finite denominator apartness. -/
def affine (evaluation : ProjectiveEvaluation)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      evaluation.denominator.output.name) : Expression :=
  CCL.CertifiedExpression.Expression.div
    evaluation.numerator evaluation.denominator apart

/-- Enter the reciprocal affine chart around a pole only from finite
numerator apartness.  A pole is represented there by an output near zero,
rather than by constructing an affine infinity. -/
def reciprocalAffine (evaluation : ProjectiveEvaluation)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      evaluation.numerator.output.name) : Expression :=
  CCL.CertifiedExpression.Expression.div
    evaluation.denominator evaluation.numerator apart

/-- Finite operational pole data: the denominator process is operationally
zero while the numerator process is uniformly apart.  This records the
projective infinity chart without adjoining a completed infinity value. -/
structure PoleCertificate (evaluation : ProjectiveEvaluation) where
  numeratorApart : CCL.ProgressiveTransducer.Named.Apart
    evaluation.numerator.output.name
  denominatorZero : NamedEquivalent evaluation.denominator.output.name
    (CCL.ProgressiveTransducer.Named.exact 0)

end ProjectiveEvaluation

end CCL.ProjectiveRationalEvaluation
