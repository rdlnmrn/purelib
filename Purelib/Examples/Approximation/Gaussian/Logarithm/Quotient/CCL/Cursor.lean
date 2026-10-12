module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.CCL.Cursor
public import Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.WorkedExamples
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
# Executable schedules for `log(1 + z) / z`

The concrete input is the exact rational `z = 1/2`, while the logarithm source
anchor is built independently at `3/2`.  One schedule acquires logarithm
overlap first and denominator apartness second; another supplies denominator
apartness first.  Both finish with ordinary operationally equivalent quotient
CCLs.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.CCL.Cursor

open Purelib.Examples.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian
open Purelib.Data.Rat
open Purelib.Examples.Approximation.Gaussian

/-- A ready logarithm-quotient cursor emits exactly the requested additional bits.

For every positive squared-error tolerance, retains the original completed client's cursor prefix and adds the supplied
finite count. -/
theorem final_request_length (epsilonSq :
  Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((Logarithm.Quotient.CCL.Cursor.readyCursor Quotient.WorkedExamples.finalReady).request epsilonSq positive
      count).machine.emitted.length =
      (Logarithm.Quotient.CCL.Cursor.readyCursor Quotient.WorkedExamples.finalReady).machine.emitted.length +
        count :=
  Logarithm.Quotient.CCL.Cursor.readyCursor_request_length Quotient.WorkedExamples.finalReady epsilonSq
    positive count

end Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.CCL.Cursor

end
