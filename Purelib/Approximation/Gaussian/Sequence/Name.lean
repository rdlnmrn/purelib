module
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Process
public import Purelib.Approximation.Gaussian.Name.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation

section
@[expose] public section

/-!
# Limit-free progressive rational approximations

A transcendental computation in the constructive CCL layer must not first
manufacture a completed non-rational point.  `ApproximationData` instead records
only a sequence of displayed Gaussian-rational samples, a rational
squared-error allowance at each finite index, and a terminating refinement
operation which reaches any requested positive rational allowance.

The possibility predicate used below has an explicit natural-number witness:
`value` is one particular later finite sample.  It is a predicate, not a set
of all samples, and it does not assert that the samples have a limit.
-/

namespace Purelib.Approximation.Gaussian.Sequence
namespace ApproximationData

/-- Package the original finite approximation as its sequence-backed process at index zero.

The initial state retains the first sample and its original squared-error certificate. -/
def toNamed (approximation :
  Gaussian.Sequence.ApproximationData) : Gaussian.Name.Basic.Named :=
  { process := approximation.toProcess
    state := by
      change Nat
      exact 0 }
end ApproximationData

end Purelib.Approximation.Gaussian.Sequence

end
