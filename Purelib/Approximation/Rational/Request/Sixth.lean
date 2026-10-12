module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Requested-precision denominator acquisition

One prescribed source refinement followed by the audited small-or-apart
decision returns either candidate apartness or a persistent squared-norm
upper bound. Smallness is relative to a supplied threshold, not a zero test.
The ordinary canonical retry index is preserved: this is a requested-target
refinement, not a falsely labelled canonical `Progress` transition.
-/

namespace Purelib.Approximation.Rational.Request.Sixth

/-- Dividing a positive rational threshold by six gives a positive request target. -/
theorem requestTarget_positive {threshold : Fraction.Rational}
  (positive : 0 < threshold) :
    0 < threshold / 6 := Fraction.Order.Field.div_pos_direct positive (by decide)
end Purelib.Approximation.Rational.Request.Sixth

end
