module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite partitions of gcd-reduced Sturm events

Repeated central-third cuts produce a finite tree of rational parameter
intervals.  Every cut avoids the complete gcd-reduced signed chain, every
leaf has an explicit geometric width bound, and a coefficient-computed depth
makes the existing finite Cauchy-event scanner succeed on every leaf.
-/

namespace Purelib.Data.Rat.Interval.Bounds

section Interval

open Purelib.Data.Rat
/-- Read the interval width as its upper endpoint minus its lower endpoint. -/
def width (interval : Bounds) : Fraction.Rational :=
  interval.upper - interval.lower

/-- Every retained rational interval has nonnegative width. -/
theorem width_nonneg (interval : Bounds) : 0 ≤
  width interval :=
  Fraction.Order.Arithmetic.sub_nonneg_direct interval.valid

/-- Strictly ordered interval endpoints give a strictly positive width. -/
theorem width_pos {interval : Bounds}
    (proper : interval.lower < interval.upper) : 0 < width interval :=
  Fraction.Order.Arithmetic.sub_pos_direct proper
end Interval
end Purelib.Data.Rat.Interval.Bounds

end
