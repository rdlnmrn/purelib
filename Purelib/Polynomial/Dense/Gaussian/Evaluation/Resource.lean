module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Resource
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Nat.BitWidth
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field

open Purelib.Data

open Purelib

open Purelib.Polynomial

/-!
# Magnitude and arithmetic envelopes for normalized Gaussian Horner evaluation

Finite coefficient recursion computes a bound for the returned value, every
retained accumulator and every arithmetic clause. The original coefficient
order, normalized working records and initial accumulator are retained.
-/

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- An arithmetic-clause upper bound for one normalized Gaussian Horner step.

It combines the multiplication bound with the addition bound at the intermediate product magnitude. -/
@[expose] def stepEnvelope (current point coefficient : Nat) : Nat :=
  let product := Gaussian.Resource.mulMagnitudeEnvelope current point
  Gaussian.Resource.mulStepEnvelope current point +
    Gaussian.Resource.addStepEnvelope product coefficient
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- A Horner-clause envelope which also retains the preceding accumulator
bound, making the final recurrence a bound for every earlier state. -/
@[expose] def stepMagnitudeEnvelope (current point coefficient : Nat) : Nat :=
  max current
    (Gaussian.Resource.addMagnitudeEnvelope
      (Gaussian.Resource.mulMagnitudeEnvelope current point)
      coefficient)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Propagate an arithmetic-clause bound over a finite Horner coefficient list.

The point and current accumulator are supplied as magnitude bounds; each recursive step advances the accumulator bound
before charging the tail. -/
@[expose] def arithmeticEnvelopeFrom (point current : Nat) :
    List Gaussian.Basic.Canonical → Nat
  | [] => 0
  | coefficient :: remaining =>
      stepEnvelope current point (Gaussian.Resource.componentMagnitude coefficient) +
        Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource.arithmeticEnvelopeFrom point
          (stepMagnitudeEnvelope current point
            (Gaussian.Resource.componentMagnitude coefficient)) remaining
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The coefficient-computed arithmetic bound for Horner evaluation from zero. -/
@[expose] def arithmeticEnvelope (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : Nat :=
  arithmeticEnvelopeFrom (Gaussian.Resource.componentMagnitude point) (Gaussian.Resource.componentMagnitude 0)
    coefficients
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Source recurrence bounding all arithmetic clauses in normalized Horner
evaluation. -/
@[expose] def normalizedEvaluationStepBudget (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  arithmeticEnvelope point polynomial.coeffs
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Propagate a bound for all normalized Horner accumulators over the coefficient list.

Each step keeps the preceding magnitude bound as well as bounding the new accumulator. -/
@[expose] def magnitudeEnvelopeFrom (point current : Nat) :
    List Gaussian.Basic.Canonical → Nat
  | [] => current
  | coefficient :: remaining =>
      Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource.magnitudeEnvelopeFrom point
        (stepMagnitudeEnvelope current point (Gaussian.Resource.componentMagnitude coefficient))
        remaining
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The final propagated magnitude bound includes the original accumulator bound. -/
theorem current_le_magnitudeEnvelopeFrom (point current : Nat)
    (coefficients : List Gaussian.Basic.Canonical) :
    current ≤ magnitudeEnvelopeFrom point current coefficients := by
  induction coefficients generalizing current with
  | nil => exact le_refl _
  | cons coefficient remaining inductionHypothesis =>
      exact (Data.Nat.Order.le_max_left _ _).trans
        (inductionHypothesis
          (stepMagnitudeEnvelope current point
            (Gaussian.Resource.componentMagnitude coefficient)))
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- A coefficient-computed bound for every Horner accumulator starting from zero. -/
@[expose] def magnitudeEnvelope (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) : Nat :=
  magnitudeEnvelopeFrom (Gaussian.Resource.componentMagnitude point) (Gaussian.Resource.componentMagnitude 0)
    coefficients
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Source recurrence bounding every normalized Horner accumulator. -/
@[expose] def normalizedEvaluationBitBudget (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  Data.Nat.BitWidth.natWidth (magnitudeEnvelope point
    polynomial.coeffs)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The computed single-step envelope bounds the normalized Horner output magnitude.

The displayed point, accumulator and coefficient magnitudes must lie within their supplied bounds. -/
theorem step_magnitude_le
    {point accumulator : Gaussian.Basic.Number} {coefficient : Gaussian.Basic.Canonical}
    {pointBound accumulatorBound coefficientBound : Nat}
    (pointLe : Gaussian.Resource.GaussianNormalized.componentMagnitude point ≤ pointBound)
    (accumulatorLe :
      Gaussian.Resource.GaussianNormalized.componentMagnitude accumulator ≤ accumulatorBound)
    (coefficientLe : Gaussian.Resource.componentMagnitude coefficient ≤ coefficientBound) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude
        (Dense.Evaluation.step point accumulator coefficient) ≤
      stepMagnitudeEnvelope accumulatorBound pointBound coefficientBound := by
  have product := (Gaussian.Resource.componentMagnitude_mul_le
    accumulator point).trans
      (Gaussian.Resource.mulMagnitudeEnvelope_mono
        accumulatorLe pointLe)
  have added := (Gaussian.Resource.componentMagnitude_add_le
    (Gaussian.Basic.mul accumulator point)
    (Gaussian.Basic.ofGaussian coefficient)).trans
      (Gaussian.Resource.addMagnitudeEnvelope_mono product coefficientLe)
  exact added.trans (Data.Nat.Order.le_max_right _ _)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The final Horner value lies within the propagated magnitude envelope.

The point and starting accumulator must satisfy the retained source bounds. -/
theorem evalCoeffsFrom_magnitude_le
    {point accumulator : Gaussian.Basic.Number} {coefficients : List Gaussian.Basic.Canonical}
    {pointBound currentBound : Nat}
    (pointLe : Gaussian.Resource.GaussianNormalized.componentMagnitude point ≤ pointBound)
    (currentLe :
      Gaussian.Resource.GaussianNormalized.componentMagnitude accumulator ≤ currentBound) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude
        (Dense.Evaluation.evalCoeffsFrom point accumulator coefficients) ≤
      magnitudeEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil => exact currentLe
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.Evaluation.evalCoeffsFrom, List.foldl_cons, magnitudeEnvelopeFrom]
      exact inductionHypothesis
        (step_magnitude_le (coefficient := coefficient)
          pointLe currentLe (le_refl _))
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Polynomial evaluation lies within its coefficient-computed magnitude envelope. -/
theorem eval_magnitude_le_envelope (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude (Dense.Basic.DensePolynomial.eval polynomial point) ≤
      magnitudeEnvelope point polynomial.coeffs := by
  exact evalCoeffsFrom_magnitude_le (le_refl _) (le_refl _)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The final normalized polynomial value fits within the computed bit-width budget. -/
theorem normalizedEvaluation_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Gaussian.Resource.workingGaussianWidth (Dense.Basic.DensePolynomial.eval polynomial point) ≤
      normalizedEvaluationBitBudget polynomial point :=
  Data.Nat.BitWidth.natWidth_mono (eval_magnitude_le_envelope
    polynomial point)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The executed multiplication and addition clauses fit within the one-step arithmetic envelope. -/
theorem step_steps_le
    {point accumulator : Gaussian.Basic.Number} {coefficient : Gaussian.Basic.Canonical}
    {pointBound accumulatorBound coefficientBound : Nat}
    (pointLe : Gaussian.Resource.GaussianNormalized.componentMagnitude point ≤ pointBound)
    (accumulatorLe :
      Gaussian.Resource.GaussianNormalized.componentMagnitude accumulator ≤ accumulatorBound)
    (coefficientLe : Gaussian.Resource.componentMagnitude coefficient ≤ coefficientBound) :
    Gaussian.Resource.mulSteps accumulator point +
        Gaussian.Resource.addSteps
          (Gaussian.Basic.mul accumulator point)
          (Gaussian.Basic.ofGaussian coefficient) ≤
      stepEnvelope accumulatorBound pointBound coefficientBound := by
  have productMagnitude := (Gaussian.Resource.componentMagnitude_mul_le
    accumulator point).trans
      (Gaussian.Resource.mulMagnitudeEnvelope_mono
        accumulatorLe pointLe)
  have multiplication := (Gaussian.Resource.mulSteps_le_envelope
    accumulator point).trans
      (Gaussian.Resource.mulStepEnvelope_mono accumulatorLe pointLe)
  have addition := (Gaussian.Resource.addSteps_le_envelope
    (Gaussian.Basic.mul accumulator point)
    (Gaussian.Basic.ofGaussian coefficient)).trans
      (Gaussian.Resource.addStepEnvelope_mono
        productMagnitude coefficientLe)
  unfold stepEnvelope
  exact Nat.add_le_add multiplication addition
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The executed Horner clause count fits within the recursive arithmetic envelope.

The source point and initial accumulator must satisfy the supplied magnitude bounds. -/
theorem stepsFrom_le_envelope
    {point accumulator : Gaussian.Basic.Number} {coefficients : List Gaussian.Basic.Canonical}
    {pointBound currentBound : Nat}
    (pointLe : Gaussian.Resource.GaussianNormalized.componentMagnitude point ≤ pointBound)
    (currentLe :
      Gaussian.Resource.GaussianNormalized.componentMagnitude accumulator ≤ currentBound) :
    Dense.Gaussian.Evaluation.Trace.stepsFrom point accumulator coefficients ≤
      arithmeticEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil => exact le_refl 0
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.Gaussian.Evaluation.Trace.stepsFrom, arithmeticEnvelopeFrom]
      have clause := step_steps_le (coefficient := coefficient)
        pointLe currentLe (le_refl _)
      have nextMagnitude := step_magnitude_le (coefficient := coefficient)
        pointLe currentLe (le_refl _)
      exact Nat.add_le_add clause
        (inductionHypothesis nextMagnitude)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- The executed Horner count from zero is bounded by the coefficient-computed envelope. -/
theorem steps_le_envelope (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.Trace.steps point coefficients ≤ arithmeticEnvelope point coefficients :=
  stepsFrom_le_envelope (le_refl _) (le_refl _)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Normalized polynomial evaluation satisfies its declared arithmetic-step budget. -/
theorem normalizedEvaluation_steps_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.Trace.steps point polynomial.coeffs ≤
      normalizedEvaluationStepBudget polynomial point :=
  steps_le_envelope point polynomial.coeffs
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Every retained accumulator in a Horner trace fits within the final magnitude envelope.

The proof includes the initial accumulator and every later state, under the supplied point and initial magnitude bounds.
-/
theorem traceFrom_magnitude_le
    {point accumulator : Gaussian.Basic.Number} {coefficients : List Gaussian.Basic.Canonical}
    {pointBound currentBound : Nat}
    (pointLe : Gaussian.Resource.GaussianNormalized.componentMagnitude point ≤ pointBound)
    (currentLe :
      Gaussian.Resource.GaussianNormalized.componentMagnitude accumulator ≤ currentBound)
    {candidate : Gaussian.Basic.Number}
    (member : candidate ∈ Dense.Gaussian.Evaluation.Trace.traceFrom point accumulator coefficients) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude candidate ≤
      magnitudeEnvelopeFrom pointBound currentBound coefficients := by
  induction coefficients generalizing accumulator currentBound with
  | nil =>
      change candidate ∈ [accumulator] at member
      have originalAccumulator := Data.List.Membership.mem_singleton.mp member
      cases originalAccumulator
      exact currentLe
  | cons coefficient remaining inductionHypothesis =>
      change candidate ∈ accumulator ::
        Dense.Gaussian.Evaluation.Trace.traceFrom point
          (Dense.Evaluation.step point accumulator coefficient) remaining at member
      have originalOccurrence := Data.List.Membership.mem_cons.mp member
      rewrite [magnitudeEnvelopeFrom]
      rcases originalOccurrence with head | tail
      · rewrite [head]
        exact currentLe.trans
          (current_le_magnitudeEnvelopeFrom pointBound currentBound
            (coefficient :: remaining))
      · exact inductionHypothesis
          (step_magnitude_le (coefficient := coefficient)
            pointLe currentLe (le_refl _)) tail
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Every accumulator in the zero-start Horner trace satisfies the computed magnitude envelope. -/
theorem trace_magnitude_le_envelope (point : Gaussian.Basic.Canonical)
    (coefficients : List Gaussian.Basic.Canonical) {candidate : Gaussian.Basic.Number}
    (member : candidate ∈ Dense.Gaussian.Evaluation.Trace.trace point coefficients) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude candidate ≤
      magnitudeEnvelope point coefficients :=
  traceFrom_magnitude_le (le_refl _) (le_refl _) member
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

/-- Every accumulator in the normalized polynomial trace satisfies the computed bit-width budget. -/
theorem normalizedEvaluation_trace_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
    {candidate : Gaussian.Basic.Number}
    (member : candidate ∈
      Dense.Gaussian.Evaluation.Trace.trace point polynomial.coeffs) :
    Gaussian.Resource.workingGaussianWidth candidate ≤
      normalizedEvaluationBitBudget polynomial point :=
  Data.Nat.BitWidth.natWidth_mono (trace_magnitude_le_envelope
    point polynomial.coeffs member)
end Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource

end
