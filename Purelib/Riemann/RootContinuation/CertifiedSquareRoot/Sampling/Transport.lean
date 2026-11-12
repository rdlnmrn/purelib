module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

/-!
# Exact request-index transport of paid square-root observations

Equality of the original accuracy requests transports the entire retained
observation. The comparison, process state, witness, minimum and both actual
comparison indices are preserved. This operation performs no request,
refinement, comparison selection or root isolation.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation

open Purelib.Approximation
open Purelib.Data.Gaussian.Basic (Canonical)

variable {parameter : Canonical} {root : Certificate parameter} {first last : AccuracyRequest}

/-- Transport the whole original paid observation along an exact equality of its accuracy request. -/
@[expose] def castAccuracy (equal : first = last) (sample : ResidualObservation root first) :
    ResidualObservation root last := by
  cases equal
  exact sample

/-- Request-index transport preserves every original cache field and proof in the complete observation. -/
theorem castAccuracy_heq (equal : first = last) (sample : ResidualObservation root first) :
    HEq (castAccuracy equal sample) sample := by
  cases equal
  rfl

/-- Request-index transport preserves the exact original process state selected by the square comparison. -/
theorem castAccuracy_state (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).state = sample.state := by
  cases equal
  rfl

/-- Request-index transport preserves the whole original observation, including its predicate, witness and spread. -/
theorem castAccuracy_observation (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).observation = sample.observation := by
  cases equal
  rfl

/-- Request-index transport preserves the identical already selected original root witness. -/
theorem castAccuracy_reading (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).reading = sample.reading := by
  cases equal
  rfl

/-- Request-index transport preserves the entire original square comparison and both retained approximation starts. -/
theorem castAccuracy_comparison (equal : first = last) (sample : ResidualObservation root first) :
    HEq (castAccuracy equal sample).comparison sample.comparison := by
  cases equal
  rfl

/-- Request-index transport preserves the minimum index that paid spread before the original square comparison. -/
theorem castAccuracy_minimumIndex (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).minimumIndex = sample.minimumIndex := by
  cases equal
  rfl

/-- Request-index transport preserves the actual comparison index selecting the original root process state. -/
theorem castAccuracy_leftIndex (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).comparison.leftIndex = sample.comparison.leftIndex := by
  cases equal
  rfl

/-- Request-index transport preserves the actual selected index of the original exact-radicand comparison owner. -/
theorem castAccuracy_rightIndex (equal : first = last) (sample : ResidualObservation root first) :
    (castAccuracy equal sample).comparison.rightIndex = sample.comparison.rightIndex := by
  cases equal
  rfl

/-- An already paid lower sampling stage remains paid after exact request-index transport. -/
theorem castAccuracy_index_ge (equal : first = last) (sample : ResidualObservation root first)
    {stage : Nat} (paid : stage ≤ sample.comparison.leftIndex) :
    stage ≤ (castAccuracy equal sample).comparison.leftIndex := by
  rewrite [castAccuracy_leftIndex]
  exact paid

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation

end
