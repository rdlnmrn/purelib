module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Lp.L1
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.EssentialBound.Lp
import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.EssentialBound.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

open Purelib.Data.Rat
/-- An essential magnitude ceiling bounds the normalized expectation of the observable's magnitude. -/
theorem poweredL1_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (ceiling : Fraction.Rational)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredL1 value ≤ ceiling := by
  have estimate := distribution.toContent.poweredL1_le_of_essentialBound
    value ceiling bounded
  rw [distribution.toContent_total, one_mul] at estimate
  exact estimate

/-- An essential magnitude ceiling bounds every natural-powered magnitude expectation by the matching power of that
ceiling. -/
theorem poweredLp_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredLp exponent value ≤ ceiling ^ exponent := by
  have estimate := distribution.toContent.poweredLp_le_of_essentialBound
    exponent value ceiling bounded
  rw [distribution.toContent_total, one_mul] at estimate
  exact estimate

end Distribution

end Purelib.Measure

end
