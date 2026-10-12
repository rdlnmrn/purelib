module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Name

/-- Turn the second-relative exponential approximation of a displayed unit-disk Gaussian input into a productive process
name. -/
def expSecondRelNamed (z :
  Data.Gaussian.Basic.Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) :
  Gaussian.Name.Basic.Named :=
  (Sequence.expSecondRelApproximation z unitInput).toNamed
end Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Name

end
