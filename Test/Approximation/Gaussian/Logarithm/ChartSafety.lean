module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Gaussian.Logarithm.Chart

section
@[expose] public section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace Test.Approximation.Gaussian.Logarithm.ChartSafety

/-- The exact unit ball passes the executable safety test immediately. -/
theorem exactOne_certificate : Safety.Certificate 1
  (point 1) 0 := by
  decide

/-- A nontrivial exact point strictly inside the unit-factor local chart also passes immediately. The reduced argument
is `1/5`, not zero. -/
theorem exactThreeHalves_certificate :
    Safety.Certificate 1 (point (3 / 2)) 0 := by
  decide
end Test.Approximation.Gaussian.Logarithm.ChartSafety

end
