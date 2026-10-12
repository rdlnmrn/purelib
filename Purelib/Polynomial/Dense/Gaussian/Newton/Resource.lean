module
import Purelib.Data.Nat.Order

import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Resource
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Nat.BitWidth
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
public import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Polynomial

/-!
# Working envelopes for a normalized Gaussian Newton update

Source and derivative Horner budgets combine with the exact quotient and
center subtraction. The resulting envelopes bound the retained source and
derivative traces, quotient and returned center without changing those
working computations.
-/

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- Normalized quotient occurring inside the Newton update. -/
@[expose] def normalizedNewtonQuotient (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Number :=
  Gaussian.Field.div
    (Dense.Basic.DensePolynomial.eval polynomial point)
    (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point)
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- A natural magnitude envelope for one exact Gaussian Newton update.

It combines the source and derivative evaluation envelopes, their quotient envelope and the subtraction from the
retained point. -/
@[expose] def newtonMagnitudeEnvelope (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  let sourceBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    (Dense.Derivative.derivative polynomial).coeffs
  let quotientBound := Gaussian.Resource.divMagnitudeEnvelope
    sourceBound derivativeBound
  Gaussian.Resource.addMagnitudeEnvelope
    (Gaussian.Resource.componentMagnitude point) quotientBound
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- A common component envelope for the polynomial trace, derivative trace,
quotient, and returned Newton centre. -/
@[expose] def normalizedNewtonWorkingEnvelope (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  let source := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    polynomial.coeffs
  let derivative := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    (Dense.Derivative.derivative polynomial).coeffs
  let quotient := Gaussian.Resource.divMagnitudeEnvelope source derivative
  max source (max derivative
    (max quotient
      (newtonMagnitudeEnvelope polynomial point)))
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The natural bit width of the combined Newton working magnitude envelope. -/
@[expose] def normalizedNewtonBitBudget (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  Data.Nat.BitWidth.natWidth (normalizedNewtonWorkingEnvelope polynomial point)
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The exact normalized Newton quotient fits the retained working bit budget. -/
theorem normalizedNewtonQuotient_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Gaussian.Resource.workingGaussianWidth (normalizedNewtonQuotient polynomial point) ≤
      normalizedNewtonBitBudget polynomial point := by
  apply Data.Nat.BitWidth.natWidth_mono
  have source := Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope
    polynomial point
  have derivative := Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope
    (Dense.Derivative.derivative polynomial) point
  refine (Gaussian.Resource.componentMagnitude_div_le _ _).trans
    ((Gaussian.Resource.divMagnitudeEnvelope_mono source derivative).trans
      ?_)
  unfold normalizedNewtonWorkingEnvelope
  exact (Data.Nat.Order.le_max_left _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- Every derivative Horner trace entry fits the retained Newton working bit budget. -/
theorem normalizedNewton_derivativeTrace_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
    {candidate : Gaussian.Basic.Number}
    (member : candidate ∈ Dense.Gaussian.Evaluation.Trace.trace point
      (Dense.Derivative.derivative polynomial).coeffs) :
    Gaussian.Resource.workingGaussianWidth candidate ≤
      normalizedNewtonBitBudget polynomial point := by
  apply Data.Nat.BitWidth.natWidth_mono
  refine (Dense.Gaussian.Evaluation.Resource.trace_magnitude_le_envelope point
    (Dense.Derivative.derivative polynomial).coeffs member).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- Every source Horner trace entry fits the retained Newton working bit budget. -/
theorem normalizedNewton_sourceTrace_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
    {candidate : Gaussian.Basic.Number}
    (member : candidate ∈
      Dense.Gaussian.Evaluation.Trace.trace point polynomial.coeffs) :
    Gaussian.Resource.workingGaussianWidth candidate ≤
      normalizedNewtonBitBudget polynomial point := by
  apply Data.Nat.BitWidth.natWidth_mono
  refine (Dense.Gaussian.Evaluation.Resource.trace_magnitude_le_envelope
    point polynomial.coeffs member).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact Data.Nat.Order.le_max_left _ _
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The exact Newton center is bounded by the computed Newton magnitude envelope. -/
theorem newtonCenter_magnitude_le (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    Gaussian.Resource.GaussianNormalized.componentMagnitude
        (Dense.Gaussian.Newton.Basic.newtonCenter polynomial point) ≤
      newtonMagnitudeEnvelope polynomial point := by
  let sourceBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    (Dense.Derivative.derivative polynomial).coeffs
  let quotientBound := Gaussian.Resource.divMagnitudeEnvelope
    sourceBound derivativeBound
  have sourceMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      (Dense.Basic.DensePolynomial.eval polynomial point) ≤ sourceBound :=
    Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope polynomial point
  have derivativeMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point) ≤ derivativeBound :=
    Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope
      (Dense.Derivative.derivative polynomial) point
  have quotientMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      (Gaussian.Field.div (Dense.Basic.DensePolynomial.eval polynomial point)
        (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point)) ≤ quotientBound :=
    (Gaussian.Resource.componentMagnitude_div_le _ _).trans
      (Gaussian.Resource.divMagnitudeEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have result := (Gaussian.Resource.componentMagnitude_sub_le
    (Gaussian.Basic.ofGaussian point)
    (Gaussian.Field.div (Dense.Basic.DensePolynomial.eval polynomial point)
      (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point))).trans
        (Gaussian.Resource.addMagnitudeEnvelope_mono
          (le_refl _) quotientMagnitude)
  simpa only [Dense.Gaussian.Newton.Basic.newtonCenter, newtonMagnitudeEnvelope, Gaussian.Resource.componentMagnitude,
    sourceBound,
    derivativeBound, quotientBound] using result
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The exact Newton center fits the retained working bit budget. -/
theorem normalizedNewtonCenter_width_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Gaussian.Resource.workingGaussianWidth
        (Dense.Gaussian.Newton.Basic.newtonCenter polynomial point) ≤
      normalizedNewtonBitBudget polynomial point := by
  apply Data.Nat.BitWidth.natWidth_mono
  refine (newtonCenter_magnitude_le
    polynomial point).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact (Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- An arithmetic-step envelope for source evaluation, derivative evaluation, quotient and Newton subtraction. -/
@[expose] def newtonStepEnvelope (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  let sourceBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    (Dense.Derivative.derivative polynomial).coeffs
  let quotientBound := Gaussian.Resource.divMagnitudeEnvelope
    sourceBound derivativeBound
  Dense.Gaussian.Evaluation.Resource.arithmeticEnvelope point polynomial.coeffs +
    Dense.Gaussian.Evaluation.Resource.arithmeticEnvelope point
      (Dense.Derivative.derivative polynomial).coeffs +
    Gaussian.Resource.divStepEnvelope sourceBound derivativeBound +
    Gaussian.Resource.subStepEnvelope
      (Gaussian.Resource.componentMagnitude point) quotientBound
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The retained Newton step budget, equal to the computed arithmetic-step envelope. -/
@[expose] def normalizedNewtonStepBudget (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  newtonStepEnvelope polynomial point
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- Count the exact source and derivative Horner traces, Gaussian division and center subtraction.

The quotient and subtraction costs use the actual evaluated source and derivative values. -/
@[expose] def newtonSteps (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  let sourceValue := Dense.Basic.DensePolynomial.eval polynomial point
  let derivativeValue := Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point
  let quotient := Gaussian.Field.div sourceValue derivativeValue
  Dense.Gaussian.Evaluation.Trace.steps point polynomial.coeffs +
    Dense.Gaussian.Evaluation.Trace.steps point (Dense.Derivative.derivative polynomial).coeffs +
    Gaussian.Resource.divSteps sourceValue derivativeValue +
    Gaussian.Resource.subSteps
      (Gaussian.Basic.ofGaussian point) quotient
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The exact Newton arithmetic-step count is bounded by its computed envelope. -/
theorem newtonSteps_le_envelope (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) :
    newtonSteps polynomial point ≤ newtonStepEnvelope polynomial point := by
  let sourceValue := Dense.Basic.DensePolynomial.eval polynomial point
  let derivativeValue := Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial point
  let quotient := Gaussian.Field.div sourceValue derivativeValue
  let sourceBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point polynomial.coeffs
  let derivativeBound := Dense.Gaussian.Evaluation.Resource.magnitudeEnvelope point
    (Dense.Derivative.derivative polynomial).coeffs
  let quotientBound := Gaussian.Resource.divMagnitudeEnvelope
    sourceBound derivativeBound
  have sourceMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      sourceValue ≤ sourceBound := Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope polynomial point
  have derivativeMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      derivativeValue ≤ derivativeBound :=
    Dense.Gaussian.Evaluation.Resource.eval_magnitude_le_envelope
      (Dense.Derivative.derivative polynomial) point
  have quotientMagnitude : Gaussian.Resource.GaussianNormalized.componentMagnitude
      quotient ≤ quotientBound :=
    (Gaussian.Resource.componentMagnitude_div_le _ _).trans
      (Gaussian.Resource.divMagnitudeEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have sourceSteps := Dense.Gaussian.Evaluation.Resource.steps_le_envelope point polynomial.coeffs
  have derivativeSteps := Dense.Gaussian.Evaluation.Resource.steps_le_envelope point
    (Dense.Derivative.derivative polynomial).coeffs
  have divisionSteps := (Gaussian.Resource.divSteps_le_envelope
    sourceValue derivativeValue).trans
      (Gaussian.Resource.divStepEnvelope_mono
        sourceMagnitude derivativeMagnitude)
  have subtractionSteps := (Gaussian.Resource.subSteps_le_envelope
    (Gaussian.Basic.ofGaussian point) quotient).trans
      (Gaussian.Resource.subStepEnvelope_mono
        (le_refl _) quotientMagnitude)
  have combined := Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add sourceSteps derivativeSteps)
      divisionSteps) subtractionSteps
  simpa only [newtonSteps, newtonStepEnvelope, Gaussian.Resource.componentMagnitude, sourceValue, derivativeValue,
    quotient, sourceBound, derivativeBound, quotientBound] using combined

end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end

section
public section

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Resource

/-- The normalized Newton arithmetic-step count fits the retained step budget. -/
theorem normalizedNewton_steps_le_budget
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    newtonSteps polynomial point ≤
      normalizedNewtonStepBudget polynomial point :=
  newtonSteps_le_envelope polynomial point
end Purelib.Polynomial.Dense.Gaussian.Newton.Resource

end
