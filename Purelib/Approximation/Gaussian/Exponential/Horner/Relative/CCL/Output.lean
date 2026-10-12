module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Name
import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sequence
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner.Relative

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Relative.CCL.Output

/-- The relative exponential name on the retained unit disk emits exactly the requested finite bit count and preserves
its initial prefix. -/
theorem expRelNamed_productive (z :
  Data.Gaussian.Basic.Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1)
    (count : Nat) :
    (Name.expRelNamed z unitInput).machine.emitted.IsPrefix
        (Advance.advance
          (Name.expRelNamed z unitInput).machine count).emitted ∧
      (Advance.advance
          (Name.expRelNamed z unitInput).machine count).emitted.length = count :=
  (Sequence.expRelApproximation z unitInput).output_productive count
end Purelib.Approximation.Gaussian.Exponential.Horner.Relative.CCL.Output

end
