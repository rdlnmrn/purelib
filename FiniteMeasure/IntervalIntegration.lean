import FiniteMeasure.Integration

/-!
# Finite rational interval integration

Certified rational bounds also serve as finite closed intervals, with exact
width as content.  A displayed rational cut therefore gives a two-cell
integration subdivision by exact width additivity.
-/

namespace FiniteMeasure

/-- One rational interval carrying a certified rational integrand range. -/
structure IntervalIntegrationCell where
  interval : Bound
  lower : Coordinate
  upper : Coordinate
  range_valid : lower ≤ upper

namespace IntervalIntegrationCell

/-- Exact interval width becomes the neutral integration weight. -/
def toIntegrationCell (cell : IntervalIntegrationCell) :
    IntegrationCell Bound where
  item := cell.interval
  weight := cell.interval.width
  weight_nonnegative := cell.interval.width_nonneg
  lower := cell.lower
  upper := cell.upper
  range_valid := cell.range_valid

/-- Reuse the displayed integrand range on a child interval. -/
def sameRange (parent : IntervalIntegrationCell) (interval : Bound) :
    IntervalIntegrationCell :=
  ⟨interval, parent.lower, parent.upper, parent.range_valid⟩

end IntervalIntegrationCell

/-- Two-child integration split at one displayed rational interval cut. -/
def intervalCutSameRangeSplit (parent : IntervalIntegrationCell)
    (cut : Coordinate) (inside : parent.interval.Contains cut) :
    IntegrationSplit parent.toIntegrationCell where
  children :=
    [(parent.sameRange
      (parent.interval.cutLeft cut inside)).toIntegrationCell,
     (parent.sameRange
      (parent.interval.cutRight cut inside)).toIntegrationCell]
  weight_conserved := by
    simp only [integrationWeight, IntervalIntegrationCell.toIntegrationCell,
      IntervalIntegrationCell.sameRange, add_zero]
    exact parent.interval.cut_width_add cut inside
  lower_refines := by
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact le_rfl
  upper_refines := by
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact le_rfl

/-- Exact interval cutting is a certified finite Darboux refinement. -/
theorem intervalCutSameRange_integralBound_refines
    (parent : IntervalIntegrationCell) (cut : Coordinate)
    (inside : parent.interval.Contains cut) :
    Bound.Refines
      (integralBound
        (intervalCutSameRangeSplit parent cut inside).children)
      (integralBound [parent.toIntegrationCell]) :=
  (intervalCutSameRangeSplit parent cut inside).integralBound_refines

end FiniteMeasure
