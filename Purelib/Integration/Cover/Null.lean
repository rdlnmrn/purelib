module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Cell.Basic
public import Purelib.Measure.Box.Null

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Integration.Box.Cell
public import Purelib.Integration.Cover.Cells
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Measure.Box.Cover
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

/-!
# Finite rational box integration

Displayed RFAP boxes supply exact nonnegative cell weights for the generic
finite integration layer.  Vertical and horizontal rational cuts become
certified integration subdivisions by exact finite area conservation.
-/

@[expose] public section

namespace Purelib.Integration.Cover.Null
namespace BoxIntegrationCell
end BoxIntegrationCell
namespace BoxIntegrationSplit
end BoxIntegrationSplit
namespace EffectiveNull

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Measure in
/-- Request the exact effective-null cover at target divided by the positive integrand ceiling.

Each retained cover box becomes an integration cell with range from zero to the original ceiling, preserving the cover
returned by the original null-set request. -/
def requestedBoundedCells {predicate : Basic.Canonical → Prop}
    (null : Box.Null.EffectiveNull predicate) (ceiling : Fraction.Rational)
    (ceilingPositive : 0 < ceiling) (target : Fraction.Rational)
    (targetPositive : 0 < target) : List Box.Cell.BoxIntegrationCell :=
  let coverTarget := target / ceiling
  let coverTargetPositive := Fraction.Order.Field.div_pos_direct
    targetPositive ceilingPositive
  Cover.Cells.coverRangeCells (null.request coverTarget coverTargetPositive)
    0 ceiling (Fraction.Order.Arithmetic.le_of_lt_direct ceilingPositive)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The exact cover used for the bounded integration cells covers the original predicate. -/
theorem requestedBoundedCells_cover {predicate : Basic.Canonical →
  Prop}
    (null : Box.Null.EffectiveNull predicate) (ceiling : Fraction.Rational)
    (ceilingPositive : 0 < ceiling) (target : Fraction.Rational)
    (targetPositive : 0 < target) :
    (null.request (target / ceiling)
      (Fraction.Order.Field.div_pos_direct targetPositive
        ceilingPositive)).Covers predicate :=
  null.covers _ _

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Measure in
/-- The requested bounded cells have upper integral strictly below the original positive target.

The null-cover content bound is multiplied by the retained positive ceiling, cancelling the same denominator used in the
cover request. -/
theorem requestedBoundedCells_upper_lt {predicate : Basic.Canonical
  → Prop}
    (null : Box.Null.EffectiveNull predicate) (ceiling : Fraction.Rational)
    (ceilingPositive : 0 < ceiling) (target : Fraction.Rational)
    (targetPositive : 0 < target) :
    Integration.upperIntegral
        (Box.Cell.boxIntegrationCells
          (requestedBoundedCells null ceiling ceilingPositive
            target targetPositive)) < target := by
  let coverTarget := target / ceiling
  have coverTargetPositive : (0 : Fraction.Rational) < coverTarget :=
    Fraction.Order.Field.div_pos_direct targetPositive ceilingPositive
  let cover := null.request coverTarget coverTargetPositive
  change Integration.upperIntegral
      (Box.Cell.boxIntegrationCells
        (Cover.Cells.coverRangeCells cover 0 ceiling
          (Fraction.Order.Arithmetic.le_of_lt_direct ceilingPositive))) < target
  rw [Cover.Cells.upperIntegral_coverRangeCells]
  have small := null.small coverTarget coverTargetPositive
  have scaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      small ceilingPositive
  calc
    cover.content * ceiling < coverTarget * ceiling := scaled
    _ = target :=
      Fraction.Field.div_mul_cancel_of_ne target ceiling
        ceilingPositive.ne'

end EffectiveNull

end Purelib.Integration.Cover.Null

end
