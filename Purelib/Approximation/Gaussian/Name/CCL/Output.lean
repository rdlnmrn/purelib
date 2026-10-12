module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Refinement
public import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.CCL.Transducer (Machine)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.CCL.Transducer

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Approximation.Gaussian.Name.Basic
namespace Named

/-- Begin the pure raw output bitstream cursor for an arithmetic name. -/
def machine (name : Gaussian.Name.Basic.Named) :
  Machine := Machine.initial name.process name.state

/-- Unconditional finite-request productivity for any progressive arithmetic name, including exact zero and opaque exact
rational results. -/
theorem productive (name : Gaussian.Name.Basic.Named) (count :
  Nat) :
    (name.machine).emitted.IsPrefix
        (Advance.advance name.machine count).emitted ∧
      (Advance.advance name.machine count).emitted.length = count := by
  have result := Advance.productive
    name.machine count
  simpa only [machine, Machine.initial, List.length_nil,
    Nat.zero_add]
    using result

/-- Every finite output request for the sum name returns exactly the requested number of bits and extends its initial
prefix. -/
theorem add_productive (left right : Gaussian.Name.Basic.Named)
  (count : Nat) :
    ((left.add right).machine).emitted.IsPrefix
        (Advance.advance (left.add right).machine count).emitted ∧
      (Advance.advance (left.add right).machine count).emitted.length = count :=
  (left.add right).productive count

/-- Every finite output request for the difference name returns exactly the requested number of bits and extends its
initial prefix. -/
theorem sub_productive (left right : Gaussian.Name.Basic.Named)
  (count : Nat) :
    ((left.sub right).machine).emitted.IsPrefix
        (Advance.advance (left.sub right).machine count).emitted ∧
      (Advance.advance (left.sub right).machine count).emitted.length = count :=
  (left.sub right).productive count

/-- Every finite output request for the product name returns exactly the requested number of bits and extends its
initial prefix. -/
theorem mul_productive (left right : Gaussian.Name.Basic.Named)
  (count : Nat) :
    ((left.mul right).machine).emitted.IsPrefix
        (Advance.advance (left.mul right).machine count).emitted ∧
      (Advance.advance (left.mul right).machine count).emitted.length = count :=
  (left.mul right).productive count

/-- Every finite output request for division with retained denominator apartness returns exactly the requested number of
bits and extends its initial prefix. -/
theorem div_productive (left right : Gaussian.Name.Basic.Named)
  (apart : Named.Apart right)
    (count : Nat) :
    ((left.div right apart).machine).emitted.IsPrefix
        (Advance.advance (left.div right apart).machine count).emitted ∧
      (Advance.advance (left.div right apart).machine count).emitted.length = count :=
  (left.div right apart).productive count

end Named

end Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Name.CCL.Output

/-- Refining an output name to a positive rational accuracy target preserves productivity for every subsequent finite
bit request. -/
theorem refined_productive (output : Gaussian.Name.Basic.Named)
  (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    (Refinement.refined output target positive).machine.emitted.IsPrefix
        (Advance.advance
          (Refinement.refined output target positive).machine count).emitted ∧
      (Advance.advance
          (Refinement.refined output target positive).machine count).emitted.length = count :=
  (Refinement.refined output target positive).productive count
end Purelib.Approximation.Gaussian.Name.CCL.Output

end
