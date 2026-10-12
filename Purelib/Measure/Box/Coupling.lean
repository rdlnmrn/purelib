module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Box.Distribution
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Normalized finite distributions on RFAP box partitions

A displayed positive-area box partition can be normalized to an exact
rational distribution over its finitely many child boxes.  This is a law on
the partition cells themselves, not a completed uniform point measure.
-/

namespace Purelib.Measure.Box.Coupling

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Measure
/-- Couple the exact vertical child distribution with the point mass at its original parent box.

The retained joint law collapses every original child occurrence to the same parent and certifies both exact marginal
laws. -/
def verticalSplitParentLawCoupling (box : Box) (cut :
  Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < Box.Content.boxContent box) :
    Measure.LawCoupling
      (Box.Distribution.verticalSplitDistribution box cut inside positive)
      (Distribution.pure box) :=
  LawCoupling.collapse
    (Box.Distribution.verticalSplitDistribution box cut inside positive) box

/-- Couple the exact horizontal child distribution with the point mass at its original parent box.

The retained joint law collapses every original child occurrence to the same parent and certifies both exact marginal
laws. -/
def horizontalSplitParentLawCoupling (box : Box) (cut :
  Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < Box.Content.boxContent box) :
    Measure.LawCoupling
      (Box.Distribution.horizontalSplitDistribution box cut inside positive)
      (Distribution.pure box) :=
  LawCoupling.collapse
    (Box.Distribution.horizontalSplitDistribution box cut inside positive) box

end Purelib.Measure.Box.Coupling

end
