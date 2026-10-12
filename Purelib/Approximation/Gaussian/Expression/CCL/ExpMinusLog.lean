module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Expression.ExpMinusLog
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
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

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Expression

open Purelib.Approximation.Gaussian.Logarithm

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

namespace Purelib.Approximation.Gaussian.Expression.CCL.ExpMinusLog

/-- Every certified finite application of `g` has the same combined bitstream, squared-error, and exact-parser contract
as exponential and positive-real logarithm. -/
theorem g_bitstream_and_error (x y :
  Gaussian.Name.Basic.Named)
    (positiveY : Approximation.Gaussian.Name.PositiveReal y)
    (target : Fraction.Rational) (targetPositive : 0 < target) (count : Nat) :
    ((ExpMinusLog.gRequest x y positiveY target targetPositive).process.ball
        (ExpMinusLog.gRequest x y positiveY target targetPositive).state).radiusSq < target ∧
      (ExpMinusLog.gRequest x y positiveY target targetPositive).machine.emitted.IsPrefix
        (Advance.advance
          (ExpMinusLog.gRequest x y positiveY target targetPositive).machine count).emitted ∧
      (Advance.advance
          (ExpMinusLog.gRequest x y positiveY target targetPositive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (ExpMinusLog.gRequest x y positiveY target targetPositive).process
        (ExpMinusLog.gRequest x y positiveY target targetPositive).state
        (Advance.advance
          (ExpMinusLog.gRequest x y positiveY target targetPositive).machine count) :=
  CCL.Contract.refined_bitstream_and_error (ExpMinusLog.gOutput x y positiveY) target targetPositive count

/-- Every finite application of the charted complex `g` has a requested rational enclosure, exactly the requested number
of CCL bits, and exact ordinary raw-parser semantics at the same refined state. -/
theorem complex_g_bitstream_and_error (x y :
  Gaussian.Name.Basic.Named)
    (chartY : Approximation.Gaussian.Logarithm.Chart y)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    ((ExpMinusLog.complexGRequest x y chartY target positive).process.ball
        (ExpMinusLog.complexGRequest x y chartY target positive).state).radiusSq < target ∧
      (ExpMinusLog.complexGRequest x y chartY target positive).machine.emitted.IsPrefix
        (Advance.advance
          (ExpMinusLog.complexGRequest x y chartY target positive).machine count).emitted ∧
      (Advance.advance
          (ExpMinusLog.complexGRequest x y chartY target positive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (ExpMinusLog.complexGRequest x y chartY target positive).process
        (ExpMinusLog.complexGRequest x y chartY target positive).state
        (Advance.advance
          (ExpMinusLog.complexGRequest x y chartY target positive).machine count) :=
  CCL.Contract.refined_bitstream_and_error (ExpMinusLog.complexGOutput x y chartY) target positive count

end Purelib.Approximation.Gaussian.Expression.CCL.ExpMinusLog

end
