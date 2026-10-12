module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Automatic finite range reduction for the progressive exponential

This module makes the local construction a total exponential operator on
arithmetic CCL names.  One finite input ball from the CCL accuracy sidechannel
supplies a rational norm bound.  A logarithmic bounded scan chooses a
displayed natural exponent `k` for which division by `2^k` puts every
candidate in the unit disk.  The local exponential CCL name is then squared
exactly `k` times by the already proved CCL arithmetic operation.  The result
is again a productive CCL name.  No magnitude limit, completed input value,
or infinite functional equation is used; the bare raw bitstream is not asked
to provide quantitative accuracy by itself.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.CCL.Output

/-- The automatically range-reduced exponential name emits exactly the requested finite bit count and preserves its
initial prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (count : Nat) :
    (Exponential.Progressive.Range.Name.named input).machine.emitted.IsPrefix
        (Advance.advance
          (Exponential.Progressive.Range.Name.named input).machine count).emitted ∧
      (Advance.advance
          (Exponential.Progressive.Range.Name.named input).machine count).emitted.length = count :=
  (Exponential.Progressive.Range.Name.named input).productive count

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.CCL.Output

end
