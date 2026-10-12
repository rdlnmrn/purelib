module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Cut
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Data.Rat.Interval.Proper

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a nominal basic interval together with strict separation of its endpoints.

The strict endpoint witness supplements the original basic interval validity field. Child constructors retain that same
nominal interval type and the supplied strict cut comparison. -/
structure Cell where
  /-- The original nominal basic interval carried by this proper cell. -/ interval : Data.Rat.Interval.Bounds
  /-- Evidence that the retained lower endpoint is strictly below its upper endpoint. -/ proper : interval.lower <
    interval.upper

constructive_injectivity Cell

namespace Cell

open Purelib.Data.Rat
/-- Construct a proper left cell using a cut strictly above the original lower endpoint. -/
def left (cell : Cell) (cut : Fraction.Rational)
    (lowerLt : cell.interval.lower < cut) : Cell :=
  { interval := Data.Rat.Interval.Bounds.leftChild cell.interval cut lowerLt.le
    proper := lowerLt }

/-- Construct a proper right cell using a cut strictly below the original upper endpoint. -/
def right (cell : Cell) (cut : Fraction.Rational)
    (upperLt : cut < cell.interval.upper) : Cell :=
  { interval := Data.Rat.Interval.Bounds.rightChild cell.interval cut upperLt.le
    proper := upperLt }

end Cell
end Purelib.Data.Rat.Interval.Proper

end

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Data.Rat.Interval.Proper

open Purelib.Data.Rat
/-- Construct the proper rational cell from negative one to one. -/
def unitCell : Cell where
  interval := ⟨-1, 1, by decide⟩
  proper := by decide

/-- Construct the proper symmetric rational cell from a supplied positive radius. -/
def symmetricCell (radius : Fraction.Rational) (positive : 0 < radius) :
  Cell where
  interval := ⟨-radius, radius,
    (Fraction.Order.Arithmetic.neg_le_neg_direct positive.le).trans
      positive.le⟩
  proper := by
    have negative : -radius < 0 := by
      simpa only [neg_zero] using
        (Fraction.Order.Arithmetic.neg_lt_neg_direct positive)
    exact negative.trans positive
end Purelib.Data.Rat.Interval.Proper

end
