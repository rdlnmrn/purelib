module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.CCL.Output
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

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# One certified complex logarithm branch chart

A chart scales the input by one displayed Gaussian rational `factor`, forms
the exact progressive quotient

`(factor * input - 1) / (factor * input + 1)`,

and requires finite certificates that every possible denominator has a fixed
positive lower quadrance and that every possible quotient lies in the local
disk of the finite complex-log recurrence.  One finite preparation step turns
the first certificate into whole-ball apartness before division.  A separate
progressive correction name selects the desired additive branch normalization.

This is deliberately a one-chart interface.  It is not a total complex
logarithm and it does not hide a branch choice or a completed complex value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Output

/-- The chart's local logarithm output emits exactly the requested finite bit count and preserves its initial prefix. -/
theorem local_productive (input :
  Named) (chart : Chart input) (count : Nat) :
    (Name.localOutput input chart).machine.emitted.IsPrefix
        (Advance.advance
          (Name.localOutput input chart).machine count).emitted ∧
      (Advance.advance
          (Name.localOutput input chart).machine count).emitted.length = count :=
  Local.CCL.Output.productive
    (Reduction.reduced input chart.factor chart.denominatorApart)
    chart.reducedDisk count

/-- The charted logarithm output emits exactly the requested finite bit count and preserves its initial prefix. -/
theorem productive (input : Named)
  (chart : Chart input) (count : Nat) :
    (Name.named input chart).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named input chart).machine count).emitted ∧
      (Advance.advance
          (Name.named input chart).machine count).emitted.length = count :=
  (Name.named input chart).productive count

end Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Output

end

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Output

/-- A caller-supplied branch-safe complex chart produces the same finite squared-error, productive-bitstream, and
exact-parser contract as the positive-real logarithm. The chart exposes rather than guesses the branch normalization. -/
theorem complex_log_bitstream_and_error (input :
  Named)
    (chart : Chart input)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    ((Name.complexLogRequest input chart target positive).process.ball
        (Name.complexLogRequest input chart target positive).state).radiusSq < target ∧
      (Name.complexLogRequest input chart target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count).emitted ∧
      (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (Name.complexLogRequest input chart target positive).process
        (Name.complexLogRequest input chart target positive).state
        (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count) :=
  CCL.Contract.refined_bitstream_and_error (Name.complexLogOutput input chart) target positive count

/-- Every positive accuracy and finite bit request for the supplied complex-logarithm chart satisfies the enclosure,
prefix, length and exact-parser contract. -/
theorem complex_log_ccl_computable (input :
  Named)
    (chart : Chart input)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    ((Name.complexLogRequest input chart target positive).process.ball
        (Name.complexLogRequest input chart target positive).state).radiusSq < target ∧
      (Name.complexLogRequest input chart target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count).emitted ∧
      (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count).emitted.length =
        count ∧
      Semantics.Basic.ExactCursor
        (Name.complexLogRequest input chart target positive).process
        (Name.complexLogRequest input chart target positive).state
        (Advance.advance
          (Name.complexLogRequest input chart target positive).machine count) :=
  complex_log_bitstream_and_error input chart target positive
    count
end Purelib.Approximation.Gaussian.Logarithm.Chart.CCL.Output

end
