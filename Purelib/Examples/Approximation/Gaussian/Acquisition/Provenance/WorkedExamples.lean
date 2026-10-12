module
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero

public import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation
public import Test.RootIsolation.SquareRoot.Sidecar
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws

@[expose] public section

/-! # Regression clients through the public finite-acquisition interface -/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.Provenance.WorkedExamples

open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples (oneInput tinyInput zeroInput)
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Examples.Approximation.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division

/-- Rational acquisition provenance for the retained switching-input cancellation. -/
def rationalCancellation :=
  Approximation.Gaussian.Acquisition.Provenance.rational
  Provenance.Rational.Cancellation.cancellationSidecar

/-- Square-root acquisition provenance for the same cancellation channel. -/
def algebraicCancellation :=
  Approximation.Gaussian.Acquisition.Provenance.squareRoot
  Test.RootIsolation.SquareRoot.Sidecar.cancellationSidecar

/-- Rational and square-root provenance agree on exact denominator readiness.

Uses the original channel identity to compare the two retained provenance routes. -/
theorem exact_cross_provenance :
    (Provenance.exact rationalCancellation).isPrepared = (Provenance.exact
      algebraicCancellation).isPrepared :=
  Provenance.exact_respects rationalCancellation
    algebraicCancellation
    (Equivalence.NamedEquivalent.refl _)

/-- The retained cancellation is zero exactly when it is not prepared.

Instantiates completeness of the exact provenance decision for the original coherent name. -/
theorem exact_cancellation_complete
  :
    Equivalence.Zero.IsZero Provenance.Rational.Cancellation.cancellation ↔
      ¬ Prepared.Equivalence.IsPrepared Provenance.Rational.Cancellation.cancellation :=
  (Provenance.exact_complete algebraicCancellation).1

end Purelib.Examples.Approximation.Gaussian.Acquisition.Provenance.WorkedExamples

end
