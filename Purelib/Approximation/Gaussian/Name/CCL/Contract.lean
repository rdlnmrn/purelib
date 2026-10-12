module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

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

namespace Purelib.Approximation.Gaussian.Name.CCL.Contract

/-- The complete finite-request contract shared by every output process: strict rational squared error, exact visible
bit count, prefix preservation, and exact ordinary raw-parser semantics for the same refined state. -/
theorem refined_bitstream_and_error (output :
  Gaussian.Name.Basic.Named) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    ((Refinement.refined output target positive).process.ball
        (Refinement.refined output target positive).state).radiusSq < target ∧
      (Refinement.refined output target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Refinement.refined output target positive).machine count).emitted ∧
      (Advance.advance
          (Refinement.refined output target positive).machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        (Refinement.refined output target positive).process
        (Refinement.refined output target positive).state
        (Advance.advance
          (Refinement.refined output target positive).machine count) :=
  ⟨Refinement.refined_error output target positive,
    (CCL.Output.refined_productive output target positive count).1,
    (CCL.Output.refined_productive output target positive count).2,
    CCL.Semantics.Named.advance_exact
      (Refinement.refined output target positive) count⟩
end Purelib.Approximation.Gaussian.Name.CCL.Contract

end
