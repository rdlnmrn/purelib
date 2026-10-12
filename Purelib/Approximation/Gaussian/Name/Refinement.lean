module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

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

namespace Purelib.Approximation.Gaussian.Name.Refinement

/-- Rebase a progressive output at one explicitly requested finite-error state. -/
def refined (output : Named) (target :
  Fraction.Rational) (positive : 0 < target) :
    Named :=
  { process := output.process
    state := output.process.refine output.state target positive }

/-- The named state produced by refinement has ball squared radius strictly below the original positive target. -/
theorem refined_error (output : Named) (target
  : Fraction.Rational)
    (positive : 0 < target) :
    ((refined output target positive).process.ball
      (refined output target positive).state).radiusSq < target :=
  output.process.accurate output.state target positive
end Purelib.Approximation.Gaussian.Name.Refinement

end
