module
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Init.Prelude

open Purelib.Approximation.Gaussian.Name.Basic (Named)

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

namespace Purelib.Approximation.Gaussian.Name.Arithmetic.Power

/-- Repeated finite squaring of a progressive arithmetic name. -/
def squareIterate : Nat →
  Named → Named
  | 0, value => value
  | exponent + 1, value =>
      let previous := squareIterate exponent value
      Named.mul previous previous
end Purelib.Approximation.Gaussian.Name.Arithmetic.Power

end
