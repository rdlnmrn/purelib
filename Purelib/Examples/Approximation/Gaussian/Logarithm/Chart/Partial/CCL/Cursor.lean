module
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Cursor
import Purelib.Data.Rat.Fraction
public import Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.WorkedExamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState

@[expose] public section

/-!
# Executable examples for retryable anchored-logarithm preflight

The target reuses the deliberately delayed exact-one process from division
preflight.  Its initial ball is too coarse for complex-log chart safety.  One
finite refinement exposes an exact safe ball, after which the generic builder
blocks on the precise semantic overlap witness.  Supplying that witness
transports the separately packaged exact-one anchor to a genuinely different
based process state type.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Cursor

open Purelib.Examples.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian
open Purelib.Data.Rat
open Purelib.Examples.Approximation.Gaussian

/-- A ready logarithm cursor request emits exactly the requested number of additional bits.

For every positive squared-error tolerance, retains the original ready chart's emitted prefix and adds the supplied
finite count. -/
theorem ready_request_length
  (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((Logarithm.Chart.Partial.CCL.Cursor.readyCursor Partial.WorkedExamples.refinedReady).request
      epsilonSq positive count).machine.emitted.length =
      (Logarithm.Chart.Partial.CCL.Cursor.readyCursor
        Partial.WorkedExamples.refinedReady).machine.emitted.length + count :=
  Logarithm.Chart.Partial.CCL.Cursor.readyCursor_request_length Partial.WorkedExamples.refinedReady
    epsilonSq positive count

end Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Cursor

end
