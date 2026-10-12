module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Integration.Cell.Basic
public import Purelib.Integration.Cell.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Finite rational interval integration

Certified rational bounds also serve as finite closed intervals, with exact
width as content.  A displayed rational cut therefore gives a two-cell
integration subdivision by exact width additivity.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib in
open Purelib.Data.Rat in
/-- An interval domain together with an ordered rational range enclosure.

The domain width supplies the integration weight; the separate lower and upper values enclose the integrand on that
domain. -/
structure IntervalIntegrationCell where
  /-- The rational interval forming this cell's integration domain. -/ interval : Data.Rat.Interval
  /-- The retained lower endpoint of the integrand range enclosure. -/ lower : Fraction.Rational
  /-- The retained upper endpoint of the integrand range enclosure. -/ upper : Fraction.Rational
  /-- The lower range endpoint does not exceed the upper endpoint. -/ range_valid : lower ≤ upper

constructive_injectivity IntervalIntegrationCell

namespace IntervalIntegrationCell

open Purelib
/-- Use the exact domain width as integration weight while retaining the cell's interval and range bounds. -/
def toIntegrationCell (cell : IntervalIntegrationCell) :
    Integration.IntegrationCell Data.Rat.Interval where
  item := cell.interval
  weight := cell.interval.width
  weight_nonnegative := cell.interval.width_nonneg
  lower := cell.lower
  upper := cell.upper
  range_valid := cell.range_valid

/-- Replace the domain interval while retaining both range endpoints and their ordering certificate. -/
def sameRange (parent : IntervalIntegrationCell) (interval : Data.Rat.Interval) :
    IntervalIntegrationCell :=
  ⟨interval, parent.lower, parent.upper, parent.range_valid⟩

end IntervalIntegrationCell

open Purelib
open Purelib.Data.Rat
/-- Split an interval integration cell at a retained interior cut.

The ordered left and right children keep the parent's exact range bounds, and their domain widths sum to the original
weight. -/
def intervalCutSameRangeSplit (parent : IntervalIntegrationCell)
    (cut : Fraction.Rational) (inside : parent.interval.Contains cut) :
    Integration.IntegrationSplit parent.toIntegrationCell where
  children :=
    [(parent.sameRange
      (parent.interval.cutLeft cut inside)).toIntegrationCell,
     (parent.sameRange
      (parent.interval.cutRight cut inside)).toIntegrationCell]
  weight_conserved := by
    simp only [Integration.integrationWeight, IntervalIntegrationCell.toIntegrationCell,
      IntervalIntegrationCell.sameRange, add_zero]
    exact parent.interval.cut_width_add cut inside
  lower_refines := by
    intro child member
    rcases Data.List.Membership.mem_cons.mp member with rfl | tail
    · exact le_rfl
    · rcases Data.List.Membership.mem_cons.mp tail with rfl | impossible
      · exact le_rfl
      · cases impossible
  upper_refines := by
    intro child member
    rcases Data.List.Membership.mem_cons.mp member with rfl | tail
    · exact le_rfl
    · rcases Data.List.Membership.mem_cons.mp tail with rfl | impossible
      · exact le_rfl
      · cases impossible

/-- Cutting a cell into two children with the same range enclosure refines its integral bound. -/
theorem intervalCutSameRange_integralBound_refines
    (parent : IntervalIntegrationCell) (cut : Fraction.Rational)
    (inside : parent.interval.Contains cut) :
    Interval.Refines
      (Integration.integralBound
        (intervalCutSameRangeSplit parent cut inside).children)
      (Integration.integralBound [parent.toIntegrationCell]) :=
  (intervalCutSameRangeSplit parent cut inside).integralBound_refines

end Purelib.Measure
