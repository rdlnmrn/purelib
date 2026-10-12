module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
public import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive

open Purelib.Approximation.Gaussian.Name

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

namespace Purelib.Approximation.Gaussian.Logarithm.Positive.Name

/-- Compute the productive real-logarithm output from the original name and its positive-real lower-bound certificate.
-/
def logOutput (input : Named)
    (positive : Approximation.Gaussian.Name.PositiveReal input) :
    Named :=
  Name.named input positive

/-- Refine the certified positive-real logarithm output to the displayed positive rational squared-radius target. -/
def logRequest (input : Named)
    (positive : Approximation.Gaussian.Name.PositiveReal input)
    (target : Fraction.Rational) (targetPositive : 0 < target) : Named :=
  Refinement.refined (logOutput input positive) target targetPositive
end Purelib.Approximation.Gaussian.Logarithm.Positive.Name

end
