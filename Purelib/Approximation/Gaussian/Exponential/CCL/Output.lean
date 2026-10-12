module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Contract
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

open Purelib.Approximation.Gaussian.Exponential

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

namespace Purelib.Approximation.Gaussian.Exponential.CCL.Output

/-- End-to-end CCL computation of exponential. From any arithmetic CCL name `input`, `expOutput input` is another
arithmetic CCL name. Every finite observation returns both a certified rational exponential enclosure and exactly the
requested number of raw CCL bits, with exact parser semantics for the same output state. This is the formal
computability claim; the finite Horner and range-reduction modules construct the output sidechannel consumed by the
productive CCL controller. -/
theorem exp_bitstream_and_error (input :
  Gaussian.Name.Basic.Named) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    ((Name.expRequest input target positive).process.ball
        (Name.expRequest input target positive).state).radiusSq < target ∧
      (Name.expRequest input target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.expRequest input target positive).machine count).emitted ∧
      (Advance.advance
          (Name.expRequest input target positive).machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        (Name.expRequest input target positive).process
        (Name.expRequest input target positive).state
        (Advance.advance
          (Name.expRequest input target positive).machine count) :=
  CCL.Contract.refined_bitstream_and_error (Name.expOutput input) target positive count

/-- Every positive accuracy and finite bit request for the total exponential satisfies the enclosure, prefix, length and
exact-parser contract. -/
theorem exp_ccl_computable (input :
  Gaussian.Name.Basic.Named) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    ((Name.expRequest input target positive).process.ball
        (Name.expRequest input target positive).state).radiusSq < target ∧
      (Name.expRequest input target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.expRequest input target positive).machine count).emitted ∧
      (Advance.advance
          (Name.expRequest input target positive).machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        (Name.expRequest input target positive).process
        (Name.expRequest input target positive).state
        (Advance.advance
          (Name.expRequest input target positive).machine count) :=
  exp_bitstream_and_error input target positive count
end Purelib.Approximation.Gaussian.Exponential.CCL.Output

end
