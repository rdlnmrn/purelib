import mathlib.RFAP.ComputableDerivative
import mathlib.RFAP.ConstructivePolynomial
import mathlib.RFAP.NormalizedGaussian

/-!
# Traced normalized Gaussian-polynomial evaluation

This module runs dense Horner evaluation entirely through reduced Gaussian
rational working records.  Its trace lists every accumulator, its arithmetic
count is computed alongside the same recursion, and source-only recurrences
bound both the count and every intermediate component.  Erasing the final
working record gives the existing dense-polynomial evaluation exactly.
-/

namespace RFAP.NormalizedEvaluation

abbrev SemanticGaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev WorkingGaussian := RFAP.NormalizedGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

/-- One normalized Horner clause. -/
def step (point accumulator : WorkingGaussian)
    (coefficient : SemanticGaussian) : WorkingGaussian :=
  RFAP.NormalizedGaussian.add
    (RFAP.NormalizedGaussian.mul accumulator point)
    (RFAP.NormalizedGaussian.ofGaussian coefficient)

theorem value_step (point accumulator : WorkingGaussian)
    (coefficient : SemanticGaussian) :
    RFAP.NormalizedGaussian.value (step point accumulator coefficient) =
      RFAP.NormalizedGaussian.value accumulator *
          RFAP.NormalizedGaussian.value point + coefficient := by
  rw [step, RFAP.NormalizedGaussian.value_add,
    RFAP.NormalizedGaussian.value_mul,
    RFAP.NormalizedGaussian.value_ofGaussian]

/-- Tail-recursive normalized Horner evaluation from a supplied accumulator. -/
def evalCoeffsFrom (point : WorkingGaussian) :
    WorkingGaussian → List SemanticGaussian → WorkingGaussian
  | accumulator, [] => accumulator
  | accumulator, coefficient :: remaining =>
      evalCoeffsFrom point (step point accumulator coefficient) remaining

/-- Evaluate a displayed coefficient list from the normalized zero record. -/
def evalCoeffs (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : WorkingGaussian :=
  evalCoeffsFrom (RFAP.NormalizedGaussian.ofGaussian point)
    (RFAP.NormalizedGaussian.ofGaussian 0) coefficients

def eval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : WorkingGaussian :=
  evalCoeffs point polynomial.coeffs

def derivativeEval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : WorkingGaussian :=
  eval (RFAP.ComputableDerivative.derivative polynomial) point

/-- Newton update using the two normalized Horner evaluations directly. -/
def newtonCenter (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : WorkingGaussian :=
  RFAP.NormalizedGaussian.sub
    (RFAP.NormalizedGaussian.ofGaussian point)
    (RFAP.NormalizedGaussian.div (eval polynomial point)
      (derivativeEval polynomial point))

theorem value_evalCoeffsFrom (point accumulator : WorkingGaussian)
    (coefficients : List SemanticGaussian) :
    RFAP.NormalizedGaussian.value
        (evalCoeffsFrom point accumulator coefficients) =
      coefficients.foldl
        (fun current coefficient =>
          current * RFAP.NormalizedGaussian.value point + coefficient)
        (RFAP.NormalizedGaussian.value accumulator) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [evalCoeffsFrom, inductionHypothesis, value_step, List.foldl_cons]

theorem value_evalCoeffs (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) :
    RFAP.NormalizedGaussian.value (evalCoeffs point coefficients) =
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point coefficients := by
  rw [evalCoeffs, value_evalCoeffsFrom,
    RFAP.NormalizedGaussian.value_ofGaussian,
    RFAP.NormalizedGaussian.value_ofGaussian]
  rfl

theorem value_eval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    RFAP.NormalizedGaussian.value (eval polynomial point) =
      polynomial.eval point := by
  exact value_evalCoeffs point polynomial.coeffs

theorem value_derivativeEval (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    RFAP.NormalizedGaussian.value (derivativeEval polynomial point) =
      (RFAP.ComputableDerivative.derivative polynomial).eval point :=
  value_eval _ _

theorem value_newtonCenter (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    RFAP.NormalizedGaussian.value (newtonCenter polynomial point) =
      point - polynomial.eval point /
        (RFAP.ComputableDerivative.derivative polynomial).eval point := by
  rw [newtonCenter, RFAP.NormalizedGaussian.value_sub,
    RFAP.NormalizedGaussian.value_ofGaussian,
    RFAP.NormalizedGaussian.value_div, value_eval, value_derivativeEval]

/-! ## Executed trace and arithmetic count -/

/-- Every accumulator visited by the normalized Horner recursion, including
the initial and final accumulators. -/
def traceFrom (point : WorkingGaussian) :
    WorkingGaussian → List SemanticGaussian → List WorkingGaussian
  | accumulator, [] => [accumulator]
  | accumulator, coefficient :: remaining =>
      accumulator ::
        traceFrom point (step point accumulator coefficient) remaining

def trace (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : List WorkingGaussian :=
  traceFrom (RFAP.NormalizedGaussian.ofGaussian point)
    (RFAP.NormalizedGaussian.ofGaussian 0) coefficients

/-- Audited arithmetic clauses executed by exactly the same accumulator
recursion. -/
def stepsFrom (point : WorkingGaussian) :
    WorkingGaussian → List SemanticGaussian → Nat
  | _, [] => 0
  | accumulator, coefficient :: remaining =>
      let product := RFAP.NormalizedGaussian.mul accumulator point
      RFAP.NormalizedGaussian.mulSteps accumulator point +
        RFAP.NormalizedGaussian.addSteps product
          (RFAP.NormalizedGaussian.ofGaussian coefficient) +
        stepsFrom point (step point accumulator coefficient) remaining

def steps (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : Nat :=
  stepsFrom (RFAP.NormalizedGaussian.ofGaussian point)
    (RFAP.NormalizedGaussian.ofGaussian 0) coefficients

@[simp] theorem traceFrom_length (point accumulator : WorkingGaussian)
    (coefficients : List SemanticGaussian) :
    (traceFrom point accumulator coefficients).length =
      coefficients.length + 1 := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [traceFrom, List.length_cons, inductionHypothesis,
        List.length_cons]

/-! ## Source-only magnitude and step recurrences -/

def semanticMagnitude (source : SemanticGaussian) : Nat :=
  RFAP.NormalizedGaussian.componentMagnitude
    (RFAP.NormalizedGaussian.ofGaussian source)

/-- A Horner-clause envelope which also retains the preceding accumulator
bound, making the final recurrence a bound for every earlier state. -/
def stepMagnitudeEnvelope (current point coefficient : Nat) : Nat :=
  max current
    (RFAP.NormalizedGaussian.addMagnitudeEnvelope
      (RFAP.NormalizedGaussian.mulMagnitudeEnvelope current point)
      coefficient)

def magnitudeEnvelopeFrom (point current : Nat) :
    List SemanticGaussian → Nat
  | [] => current
  | coefficient :: remaining =>
      magnitudeEnvelopeFrom point
        (stepMagnitudeEnvelope current point (semanticMagnitude coefficient))
        remaining

def magnitudeEnvelope (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : Nat :=
  magnitudeEnvelopeFrom (semanticMagnitude point) (semanticMagnitude 0)
    coefficients

def stepEnvelope (current point coefficient : Nat) : Nat :=
  let product := RFAP.NormalizedGaussian.mulMagnitudeEnvelope current point
  RFAP.NormalizedGaussian.mulStepEnvelope current point +
    RFAP.NormalizedGaussian.addStepEnvelope product coefficient

def arithmeticEnvelopeFrom (point current : Nat) :
    List SemanticGaussian → Nat
  | [] => 0
  | coefficient :: remaining =>
      stepEnvelope current point (semanticMagnitude coefficient) +
        arithmeticEnvelopeFrom point
          (stepMagnitudeEnvelope current point
            (semanticMagnitude coefficient)) remaining

def arithmeticEnvelope (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) : Nat :=
  arithmeticEnvelopeFrom (semanticMagnitude point) (semanticMagnitude 0)
    coefficients

theorem current_le_magnitudeEnvelopeFrom (point current : Nat)
    (coefficients : List SemanticGaussian) :
    current ≤ magnitudeEnvelopeFrom point current coefficients := by
  induction coefficients generalizing current with
  | nil => exact le_refl _
  | cons coefficient remaining inductionHypothesis =>
      exact (le_max_left _ _).trans
        (inductionHypothesis
          (stepMagnitudeEnvelope current point
            (semanticMagnitude coefficient)))

theorem step_magnitude_le
    {point accumulator : WorkingGaussian} {coefficient : SemanticGaussian}
    {pointBound accumulatorBound coefficientBound : Nat}
    (pointLe : RFAP.NormalizedGaussian.componentMagnitude point ≤ pointBound)
    (accumulatorLe :
      RFAP.NormalizedGaussian.componentMagnitude accumulator ≤ accumulatorBound)
    (coefficientLe : semanticMagnitude coefficient ≤ coefficientBound) :
    RFAP.NormalizedGaussian.componentMagnitude
        (step point accumulator coefficient) ≤
      stepMagnitudeEnvelope accumulatorBound pointBound coefficientBound := by
  have product := (RFAP.NormalizedGaussian.componentMagnitude_mul_le
    accumulator point).trans
      (RFAP.NormalizedGaussian.mulMagnitudeEnvelope_mono
        accumulatorLe pointLe)
  have added := (RFAP.NormalizedGaussian.componentMagnitude_add_le
    (RFAP.NormalizedGaussian.mul accumulator point)
    (RFAP.NormalizedGaussian.ofGaussian coefficient)).trans
      (RFAP.NormalizedGaussian.addMagnitudeEnvelope_mono product coefficientLe)
  exact added.trans (le_max_right _ _)

theorem step_steps_le
    {point accumulator : WorkingGaussian} {coefficient : SemanticGaussian}
    {pointBound accumulatorBound coefficientBound : Nat}
    (pointLe : RFAP.NormalizedGaussian.componentMagnitude point ≤ pointBound)
    (accumulatorLe :
      RFAP.NormalizedGaussian.componentMagnitude accumulator ≤ accumulatorBound)
    (coefficientLe : semanticMagnitude coefficient ≤ coefficientBound) :
    RFAP.NormalizedGaussian.mulSteps accumulator point +
        RFAP.NormalizedGaussian.addSteps
          (RFAP.NormalizedGaussian.mul accumulator point)
          (RFAP.NormalizedGaussian.ofGaussian coefficient) ≤
      stepEnvelope accumulatorBound pointBound coefficientBound := by
  have productMagnitude := (RFAP.NormalizedGaussian.componentMagnitude_mul_le
    accumulator point).trans
      (RFAP.NormalizedGaussian.mulMagnitudeEnvelope_mono
        accumulatorLe pointLe)
  have multiplication := (RFAP.NormalizedGaussian.mulSteps_le_envelope
    accumulator point).trans
      (RFAP.NormalizedGaussian.mulStepEnvelope_mono accumulatorLe pointLe)
  have addition := (RFAP.NormalizedGaussian.addSteps_le_envelope
    (RFAP.NormalizedGaussian.mul accumulator point)
    (RFAP.NormalizedGaussian.ofGaussian coefficient)).trans
      (RFAP.NormalizedGaussian.addStepEnvelope_mono
        productMagnitude coefficientLe)
  unfold stepEnvelope
  exact Nat.add_le_add multiplication addition

theorem evalCoeffsFrom_magnitude_le
    {point accumulator : WorkingGaussian} {coefficients : List SemanticGaussian}
    {pointBound currentBound : Nat}
    (pointLe : RFAP.NormalizedGaussian.componentMagnitude point ≤ pointBound)
    (currentLe :
      RFAP.NormalizedGaussian.componentMagnitude accumulator ≤ currentBound) :
    RFAP.NormalizedGaussian.componentMagnitude
        (evalCoeffsFrom point accumulator coefficients) ≤
      magnitudeEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil => exact currentLe
  | cons coefficient remaining inductionHypothesis =>
      rw [evalCoeffsFrom, magnitudeEnvelopeFrom]
      exact inductionHypothesis
        (step_magnitude_le (coefficient := coefficient)
          pointLe currentLe (le_refl _))

theorem traceFrom_magnitude_le
    {point accumulator : WorkingGaussian} {coefficients : List SemanticGaussian}
    {pointBound currentBound : Nat}
    (pointLe : RFAP.NormalizedGaussian.componentMagnitude point ≤ pointBound)
    (currentLe :
      RFAP.NormalizedGaussian.componentMagnitude accumulator ≤ currentBound)
    {candidate : WorkingGaussian}
    (member : candidate ∈ traceFrom point accumulator coefficients) :
    RFAP.NormalizedGaussian.componentMagnitude candidate ≤
      magnitudeEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil =>
      simp only [traceFrom, List.mem_singleton] at member
      rw [member]
      exact currentLe
  | cons coefficient remaining inductionHypothesis =>
      simp only [traceFrom, List.mem_cons] at member
      rw [magnitudeEnvelopeFrom]
      rcases member with head | tail
      · rw [head]
        exact currentLe.trans
          (current_le_magnitudeEnvelopeFrom pointBound currentBound
            (coefficient :: remaining))
      · exact inductionHypothesis
          (step_magnitude_le (coefficient := coefficient)
            pointLe currentLe (le_refl _)) tail

theorem stepsFrom_le_envelope
    {point accumulator : WorkingGaussian} {coefficients : List SemanticGaussian}
    {pointBound currentBound : Nat}
    (pointLe : RFAP.NormalizedGaussian.componentMagnitude point ≤ pointBound)
    (currentLe :
      RFAP.NormalizedGaussian.componentMagnitude accumulator ≤ currentBound) :
    stepsFrom point accumulator coefficients ≤
      arithmeticEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil => exact le_refl 0
  | cons coefficient remaining inductionHypothesis =>
      rw [stepsFrom, arithmeticEnvelopeFrom]
      have clause := step_steps_le (coefficient := coefficient)
        pointLe currentLe (le_refl _)
      have nextMagnitude := step_magnitude_le (coefficient := coefficient)
        pointLe currentLe (le_refl _)
      exact Nat.add_le_add clause
        (inductionHypothesis nextMagnitude)

theorem eval_magnitude_le_envelope (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    RFAP.NormalizedGaussian.componentMagnitude (eval polynomial point) ≤
      magnitudeEnvelope point polynomial.coeffs := by
  exact evalCoeffsFrom_magnitude_le (le_refl _) (le_refl _)

theorem trace_magnitude_le_envelope (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) {candidate : WorkingGaussian}
    (member : candidate ∈ trace point coefficients) :
    RFAP.NormalizedGaussian.componentMagnitude candidate ≤
      magnitudeEnvelope point coefficients :=
  traceFrom_magnitude_le (le_refl _) (le_refl _) member

theorem steps_le_envelope (point : SemanticGaussian)
    (coefficients : List SemanticGaussian) :
    steps point coefficients ≤ arithmeticEnvelope point coefficients :=
  stepsFrom_le_envelope (le_refl _) (le_refl _)

/-! ## Composed normalized Newton calculation -/

def newtonMagnitudeEnvelope (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : Nat :=
  let sourceBound := magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := magnitudeEnvelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  let quotientBound := RFAP.NormalizedGaussian.divMagnitudeEnvelope
    sourceBound derivativeBound
  RFAP.NormalizedGaussian.addMagnitudeEnvelope
    (semanticMagnitude point) quotientBound

def newtonSteps (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : Nat :=
  let sourceValue := eval polynomial point
  let derivativeValue := derivativeEval polynomial point
  let quotient := RFAP.NormalizedGaussian.div sourceValue derivativeValue
  steps point polynomial.coeffs +
    steps point (RFAP.ComputableDerivative.derivative polynomial).coeffs +
    RFAP.NormalizedGaussian.divSteps sourceValue derivativeValue +
    RFAP.NormalizedGaussian.subSteps
      (RFAP.NormalizedGaussian.ofGaussian point) quotient

def newtonStepEnvelope (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) : Nat :=
  let sourceBound := magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := magnitudeEnvelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  let quotientBound := RFAP.NormalizedGaussian.divMagnitudeEnvelope
    sourceBound derivativeBound
  arithmeticEnvelope point polynomial.coeffs +
    arithmeticEnvelope point
      (RFAP.ComputableDerivative.derivative polynomial).coeffs +
    RFAP.NormalizedGaussian.divStepEnvelope sourceBound derivativeBound +
    RFAP.NormalizedGaussian.subStepEnvelope
      (semanticMagnitude point) quotientBound

theorem newtonCenter_magnitude_le (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    RFAP.NormalizedGaussian.componentMagnitude
        (newtonCenter polynomial point) ≤
      newtonMagnitudeEnvelope polynomial point := by
  let sourceBound := magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := magnitudeEnvelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  let quotientBound := RFAP.NormalizedGaussian.divMagnitudeEnvelope
    sourceBound derivativeBound
  have sourceMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      (eval polynomial point) ≤ sourceBound :=
    eval_magnitude_le_envelope polynomial point
  have derivativeMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      (derivativeEval polynomial point) ≤ derivativeBound :=
    eval_magnitude_le_envelope
      (RFAP.ComputableDerivative.derivative polynomial) point
  have quotientMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      (RFAP.NormalizedGaussian.div (eval polynomial point)
        (derivativeEval polynomial point)) ≤ quotientBound :=
    (RFAP.NormalizedGaussian.componentMagnitude_div_le _ _).trans
      (RFAP.NormalizedGaussian.divMagnitudeEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have result := (RFAP.NormalizedGaussian.componentMagnitude_sub_le
    (RFAP.NormalizedGaussian.ofGaussian point)
    (RFAP.NormalizedGaussian.div (eval polynomial point)
      (derivativeEval polynomial point))).trans
        (RFAP.NormalizedGaussian.addMagnitudeEnvelope_mono
          (le_refl _) quotientMagnitude)
  simpa only [newtonCenter, newtonMagnitudeEnvelope, semanticMagnitude, sourceBound,
    derivativeBound, quotientBound] using result

theorem newtonSteps_le_envelope (polynomial : GaussianPolynomial)
    (point : SemanticGaussian) :
    newtonSteps polynomial point ≤ newtonStepEnvelope polynomial point := by
  let sourceValue := eval polynomial point
  let derivativeValue := derivativeEval polynomial point
  let quotient := RFAP.NormalizedGaussian.div sourceValue derivativeValue
  let sourceBound := magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := magnitudeEnvelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  let quotientBound := RFAP.NormalizedGaussian.divMagnitudeEnvelope
    sourceBound derivativeBound
  have sourceMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      sourceValue ≤ sourceBound := eval_magnitude_le_envelope polynomial point
  have derivativeMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      derivativeValue ≤ derivativeBound :=
    eval_magnitude_le_envelope
      (RFAP.ComputableDerivative.derivative polynomial) point
  have quotientMagnitude : RFAP.NormalizedGaussian.componentMagnitude
      quotient ≤ quotientBound :=
    (RFAP.NormalizedGaussian.componentMagnitude_div_le _ _).trans
      (RFAP.NormalizedGaussian.divMagnitudeEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have sourceSteps := steps_le_envelope point polynomial.coeffs
  have derivativeSteps := steps_le_envelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  have divisionSteps := (RFAP.NormalizedGaussian.divSteps_le_envelope
    sourceValue derivativeValue).trans
      (RFAP.NormalizedGaussian.divStepEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have subtractionSteps := (RFAP.NormalizedGaussian.subSteps_le_envelope
    (RFAP.NormalizedGaussian.ofGaussian point) quotient).trans
      (RFAP.NormalizedGaussian.subStepEnvelope_mono
        (le_refl _) quotientMagnitude)
  have combined := Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add sourceSteps derivativeSteps)
      divisionSteps) subtractionSteps
  simpa only [newtonSteps, newtonStepEnvelope, semanticMagnitude, sourceValue, derivativeValue,
    quotient, sourceBound, derivativeBound, quotientBound] using combined

end RFAP.NormalizedEvaluation
