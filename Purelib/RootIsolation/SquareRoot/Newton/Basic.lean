module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Data

/-!
# Rounded, checked finite square-root proposals

Round each speculative Newton point to a dyadic grid before checking it and
before computing the next point.  This avoids carrying the exact Newton
orbit's rapidly growing denominators into an accepted root sample.

The predicate, not Newton convergence or a rounding estimate, certifies the
returned point.  A finite unsuccessful search returns `none`; callers retain
their independently proved total fallback.  No floating-point arithmetic or
external certificate producer is involved.
-/

@[expose] public section

namespace Purelib.RootIsolation.SquareRoot.Newton.Basic

/-- Compute one Gaussian rational square-root Newton proposal.

The update averages the current point with the parameter divided by that point; acceptance is supplied separately by a
checker. -/
def step (parameter point : Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  let sum := point + parameter * point⁻¹
  ⟨sum.re / 2, sum.im / 2⟩
end Purelib.RootIsolation.SquareRoot.Newton.Basic

end
