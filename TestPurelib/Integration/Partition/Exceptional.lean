module
import Purelib.Integration.Partition.Exceptional
import Purelib.Integration.Partition.Uniform.Grid

/-! Exact finite accounting for exceptional points and closed grid cells. -/

namespace TestPurelib.Integration.Partition.Exceptional

open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- The actual four-cell grid computed for a third-unit mesh request. -/
private def quarters : Unit.Normalized := Uniform.Grid.forWidth (1 / 3)

/-- No exceptions mark any retained cell. -/
example : quarters.markedLength [] = 0 := by decide +kernel

/-- An endpoint marks only its one adjacent closed cell. -/
example : quarters.touchLength 0 = (1 / 4 : Fraction.Rational) ∧
    quarters.touchLength 1 = (1 / 4 : Fraction.Rational) := by decide +kernel

/-- A partition cut marks both closed adjacent cells, while an exterior point marks none. -/
example : quarters.touchLength (1 / 2) = (1 / 2 : Fraction.Rational) ∧ quarters.touchLength 2 = 0 := by decide +kernel

/-- Repeated and overlapping exceptional points do not count any cell more than once. -/
example : quarters.markedLength [0, 1 / 2, 1 / 2, 1] = 1 := by decide +kernel

/-- The retained finite union obeys the general explicit radius budget. -/
example : quarters.markedLength [0, 1 / 2, 1 / 2, 1] ≤ (4 : Fraction.Rational) * (1 / 3 + 1 / 3) :=
  quarters.markedLength_le [0, 1 / 2, 1 / 2, 1] (1 / 3) (by decide)
    (fun interval member => Uniform.Grid.forWidth_interval_lt (by decide) interval member)

end TestPurelib.Integration.Partition.Exceptional
