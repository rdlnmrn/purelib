module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Positive.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Positive

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Computing exponential and logarithm as CCL names

The purpose of this module is not merely to expose Horner approximants.  It
proves that exponential and certified logarithm are computable operations on
the repository's arithmetic CCL representation: a productive raw CCL cursor
together with its finite rational accuracy sidechannel.

Each request first refines the constructed output process to one displayed
rational ball whose squared radius is below the requested positive rational
target.  The ordinary productive CCL cursor is then started at that same
finite state and returns exactly the requested number of bits.  Its
exact-cursor certificate ties every admitted parser tail back to an explicitly
possible rational value at that same refined state.  Thus the enclosure and
the CCL word are two synchronized observations of one output name.  The bare
raw word alone is intentionally not claimed to carry enough accuracy data.
The construction returns only finite rational data; it does not name a
completed transcendental value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Positive.CCL.Output

/-- End-to-end CCL computation of positive-real logarithm. The finite positive-real certificate lets the implementation
construct its dyadic chart automatically; `logOutput input positive` is another arithmetic CCL name. Every observation
synchronizes a certified rational logarithm enclosure with exactly the requested raw CCL bits and exact parser semantics
at the same output state. -/
theorem log_bitstream_and_error (input :
  Gaussian.Name.Basic.Named)
    (positive : Name.PositiveReal input)
    (target : Fraction.Rational) (targetPositive : 0 < target) (count : Nat) :
    ((Name.logRequest input positive target targetPositive).process.ball
        (Name.logRequest input positive target targetPositive).state).radiusSq <
          target ∧
      (Name.logRequest input positive target targetPositive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count).emitted ∧
      (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (Name.logRequest input positive target targetPositive).process
        (Name.logRequest input positive target targetPositive).state
        (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count) :=
  CCL.Contract.refined_bitstream_and_error (Name.logOutput input positive) target targetPositive count

/-- Every positive accuracy and finite bit request for the certified positive-real logarithm satisfies the enclosure,
prefix, length and exact-parser contract. -/
theorem log_ccl_computable (input :
  Gaussian.Name.Basic.Named)
    (positive : Name.PositiveReal input)
    (target : Fraction.Rational) (targetPositive : 0 < target) (count : Nat) :
    ((Name.logRequest input positive target targetPositive).process.ball
        (Name.logRequest input positive target targetPositive).state).radiusSq <
          target ∧
      (Name.logRequest input positive target targetPositive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count).emitted ∧
      (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (Name.logRequest input positive target targetPositive).process
        (Name.logRequest input positive target targetPositive).state
        (Advance.advance
          (Name.logRequest input positive target targetPositive).machine count) :=
  log_bitstream_and_error input positive target
    targetPositive count
end Purelib.Approximation.Gaussian.Logarithm.Positive.CCL.Output

end
