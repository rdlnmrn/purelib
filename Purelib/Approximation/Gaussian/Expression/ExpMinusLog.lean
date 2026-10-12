module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
public import Purelib.Approximation.Gaussian.Logarithm.Positive.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Positive

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Expression.ExpMinusLog

/-- One certified application of the proposed transcendental generator `g(x,y) = ExpName(x) - LogName(y)`. Further
applications may be nested, but every value used as a logarithm argument must carry its own finite branch certificate.
-/
def gOutput (x y : Gaussian.Name.Basic.Named)
    (positiveY : Approximation.Gaussian.Name.PositiveReal y) :
    Gaussian.Name.Basic.Named :=
  Named.sub
    (Name.expOutput x) (Name.logOutput y positiveY)

/-- Refine the exponential-minus-positive-real-logarithm output to the displayed positive squared-radius target. -/
def gRequest (x y : Gaussian.Name.Basic.Named)
    (positiveY : Approximation.Gaussian.Name.PositiveReal y)
    (target : Fraction.Rational) (targetPositive : 0 < target) : Gaussian.Name.Basic.Named :=
  Refinement.refined (gOutput x y positiveY) target targetPositive

/-- The charted complex extension of `g(x,y) = ExpName(x) - LogName(y)`. -/
def complexGOutput (x y : Gaussian.Name.Basic.Named)
    (chartY : Approximation.Gaussian.Logarithm.Chart y) : Gaussian.Name.Basic.Named :=
  Named.sub
    (Name.expOutput x) (Name.complexLogOutput y chartY)

/-- Refine the exponential-minus-charted-logarithm output to the displayed positive squared-radius target. -/
def complexGRequest (x y : Gaussian.Name.Basic.Named)
    (chartY : Approximation.Gaussian.Logarithm.Chart y)
    (target : Fraction.Rational) (positive : 0 < target) : Gaussian.Name.Basic.Named :=
  Refinement.refined (complexGOutput x y chartY) target positive
end Purelib.Approximation.Gaussian.Expression.ExpMinusLog

end
