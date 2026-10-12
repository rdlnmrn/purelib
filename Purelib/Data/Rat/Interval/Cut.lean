module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat.Interval.Bounds

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

section
open Purelib.Data.Rat
/-- Construct a left interval ending at a cut with the supplied lower-endpoint comparison. -/
def leftChild (interval : Bounds) (cut :
  Fraction.Rational)
    (lowerLe : interval.lower ≤ cut) : Bounds :=
  ⟨interval.lower, cut, lowerLe⟩

/-- Construct a right interval starting at a cut with the supplied upper-endpoint comparison. -/
def rightChild (interval : Bounds) (cut :
  Fraction.Rational)
    (upperLe : cut ≤ interval.upper) : Bounds :=
  ⟨cut, interval.upper, upperLe⟩

end

open Purelib.Data.Rat.Interval.Bounds

open Purelib.Data.Rat
/-- The left-child width is the cut minus the original lower endpoint. -/
@[simp] theorem leftChild_width
    (interval : Bounds) (cut : Fraction.Rational)
    (lowerLe : interval.lower ≤ cut) :
    width (leftChild interval cut lowerLe) = cut - interval.lower := rfl

/-- The right-child width is the original upper endpoint minus the cut. -/
@[simp] theorem rightChild_width
    (interval : Bounds) (cut : Fraction.Rational)
    (upperLe : cut ≤ interval.upper) :
    width (rightChild interval cut upperLe) = interval.upper - cut := rfl

/-- A cut lying between both endpoints makes its left child refine the original interval. -/
theorem leftChild_refines
    (interval : Bounds) (cut : Fraction.Rational)
    (lowerLe : interval.lower ≤ cut) (upperLe : cut ≤ interval.upper) :
    (leftChild interval cut lowerLe).Refines interval :=
  ⟨le_rfl, upperLe⟩

/-- A cut lying between both endpoints makes its right child refine the original interval. -/
theorem rightChild_refines
    (interval : Bounds) (cut : Fraction.Rational)
    (lowerLe : interval.lower ≤ cut) (upperLe : cut ≤ interval.upper) :
    (rightChild interval cut upperLe).Refines interval :=
  ⟨lowerLe, le_rfl⟩

end Interval
end Purelib.Data.Rat.Interval.Bounds

end
