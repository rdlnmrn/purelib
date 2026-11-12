module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Approximation.Gaussian.Process.Multiplication

/-! # Actual product readings of retained root observations

The original paired multiplication state consumes the two supplied paid
factor observations directly. Equality of the complete retained product
reindexes that same state and its possibility witness; neither operand is
sampled again and no arithmetic process is replaced.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)

variable {firstParameter lastParameter : Canonical}
variable {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
variable {firstAccuracy lastAccuracy : Approximation.AccuracyRequest}

/-- The same original multiplication state on both supplied retained factor-observation states. -/
@[expose] def productState (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) : value.name.process.State :=
  castState retained.symm (first.state, last.state)

/-- The product of the two actual retained witnesses is possible at that identical original paired state. -/
theorem product_possible (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) :
    value.name.process.Possible (productState first last value retained) (first.reading * last.reading) :=
  possible_castState retained.symm (first.state, last.state)
    ⟨first.reading, last.reading, first.reading_possible, last.reading_possible, rfl⟩

/-- Retain one actual full-product reading using the same original paid factor states and complete product equality.

The original observation Reading stores the transported paired state, actual
product witness, its possibility proof and the radius computed on that same
state. Both independent factor residual observations remain the inputs.
-/
@[expose] def productReading (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) : Equivalence.Observation.Reading value :=
  Equivalence.Observation.Reading.retain value (productState first last value retained)
    (first.reading * last.reading) (product_possible first last value retained)

/-- The original retained product reading is exactly the product of the same two cached factor witnesses. -/
theorem productReading_value (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) :
    (productReading first last value retained).value = first.reading * last.reading := rfl

/-- The retained product reading uses the identical transported paired state, without another refinement request. -/
theorem productReading_state (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) :
    (productReading first last value retained).state = productState first last value retained := rfl

/-- Every retained product candidate keeps actual possible readings of both original factor states. -/
theorem product_components (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (value : CoherentNamed)
    (retained : value = firstRoot.value.mul lastRoot.value) {candidate : Canonical}
    (possible : value.name.process.Possible (productState first last value retained) candidate) :
    ∃ firstCandidate lastCandidate : Canonical,
      firstRoot.value.name.process.Possible first.state firstCandidate ∧
        lastRoot.value.name.process.Possible last.state lastCandidate ∧ candidate = firstCandidate * lastCandidate := by
  cases retained
  exact possible

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation
