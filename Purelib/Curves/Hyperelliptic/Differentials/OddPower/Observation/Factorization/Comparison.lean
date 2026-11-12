module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization
public import Purelib.Approximation.Gaussian.Equivalence.Observation

/-!
# Original arithmetic observation views of factored odd-power readings

The complete factorization Reading remains the owner of both independently
selected arithmetic observations. Its generic observation view keeps the
same original evaluator state and selected witness, and caches that state's
actual ball radius. Constructing this view makes no new sample selection.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization.Reading

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {radicand : Coefficients} {differential : OddPowerDifferential radicand}
variable {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
variable {state : sheet.name.process.State} {rootObservation : RootObservation}
variable {factor velocity : Canonical} {original factored : CoherentNamed}
variable {accuracy : AccuracyRequest} {floor : Fraction.Rational}

/-- The retained original arithmetic witness is possible at its unchanged selected process state. -/
theorem reading_possible (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    original.name.process.Possible retained.originalState retained.reading := by
  have possible : retained.originalObservation.Possible retained.reading :=
    retained.originalObservation.witness_possible
  rewrite [retained.original_eq] at possible
  exact possible

/-- Cache the original state, selected value and its actual radius in the existing generic observation owner. -/
@[expose] def asObservation (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) : Equivalence.Observation.Reading original :=
  Equivalence.Observation.Reading.retain original retained.originalState retained.reading retained.reading_possible

/-- The generic observation view retains the literal original selected process state. -/
theorem asObservation_state (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    retained.asObservation.state = retained.originalState := rfl

/-- The generic observation view retains the original arithmetic observation's actual witness. -/
theorem asObservation_value (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    retained.asObservation.value = retained.originalObservation.witness := rfl

/-- The view's cached radius belongs to that same original process state. -/
theorem asObservation_radius (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    retained.asObservation.radius = (original.name.process.ball retained.originalState).radiusSq := rfl

/-- The original complete arithmetic observation is still the observation of the generic view's exact state. -/
theorem asObservation_original (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    retained.originalObservation = original.name.process.observation retained.asObservation.state :=
  retained.original_eq

/-- The unchanged original arithmetic state meets the retained factorization request's sixteenth-radius target. -/
theorem asObservation_radius_lt (retained : Reading differential point sheet apart state rootObservation
    factor velocity original factored accuracy floor) :
    retained.asObservation.radius < (radiusRequest accuracy).tolerance := by
  change (original.name.process.ball retained.originalState).radiusSq < _
  rewrite [retained.originalState_eq]
  exact radius_lt original accuracy retained.comparison.left_ge

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization.Reading

end
