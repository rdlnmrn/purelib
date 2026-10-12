module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.DyadicReduction

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Arithmetic

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name

/-- Total CCL exponential entry point: an arbitrary arithmetic CCL name is mapped to a productive arithmetic CCL name
for its finite exponential recurrence. -/
def named (input : Gaussian.Name.Basic.Named) :
  Gaussian.Name.Basic.Named :=
  Power.squareIterate (DyadicReduction.rangeExponent input)
    (Local.Name.named (DyadicReduction.scaledInput input)
      (DyadicReduction.scaledDomain input))
end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name

end
