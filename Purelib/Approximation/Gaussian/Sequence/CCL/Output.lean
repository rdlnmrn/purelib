module
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Data.CCL.Transducer.Machine

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

/-- Every limit-free progressive approximation produces exactly the requested number of raw CCL bits while preserving
its old prefix. -/
theorem output_productive (approximation :
  Gaussian.Sequence.ApproximationData) (count : Nat) :
    approximation.toNamed.machine.emitted.IsPrefix
        (Advance.advance
          approximation.toNamed.machine count).emitted ∧
      (Advance.advance
          approximation.toNamed.machine count).emitted.length = count :=
  approximation.toNamed.productive count

end ApproximationData

end Purelib.Approximation.Gaussian.Sequence

end
