module

import Purelib.Approximation.Rational.Grid.Unit
import Purelib.Data.Rat.Interval.Basic

/-! # Bounded nearest nodes and closed-unit coverage -/

namespace TestPurelib.Approximation.Rational.Grid.Unit

open Purelib.Approximation.Rational.Grid
open Purelib.Data.Rat

/-- Upward midpoint ties select the upper bounded index of the same original grid. -/
example : (Unit.nearestIndex (1 / 8) (denominator := 4) (by decide) (by constructor <;> decide)).val = 1 := by
  decide +kernel

/-- The first unit endpoint is retained as the first bounded grid index. -/
example : (Unit.nearestIndex 0 (denominator := 4) (by decide) (by constructor <;> decide)).val = 0 := by
  decide +kernel

/-- The last unit endpoint is retained as the last bounded grid index. -/
example : (Unit.nearestIndex 1 (denominator := 4) (by decide) (by constructor <;> decide)).val = 4 := by
  decide +kernel

/-- A midpoint tie near the last endpoint retains that actual last endpoint. -/
example : Unit.node 4 (Unit.nearestIndex (7 / 8) (by decide) (by constructor <;> decide)) = 1 := by
  decide +kernel

/-- Every original unit parameter has a constructive bounded nearest-node coverage witness. -/
example (parameter : Fraction.Rational) (denominator : Nat) (positive : 0 < denominator)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Unit.node denominator (Unit.nearestIndex parameter positive inside) - (1 / 2 : Fraction.Rational) /
        denominator ≤ parameter ∧
      parameter ≤ Unit.node denominator (Unit.nearestIndex parameter positive inside) +
        (1 / 2 : Fraction.Rational) / denominator := Unit.nearestIndex_covers parameter positive inside

/-- The bounded nearest node keeps the original unclipped nearest-grid coordinate exactly. -/
example (parameter : Fraction.Rational) (denominator : Nat) (positive : 0 < denominator)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Unit.node denominator (Unit.nearestIndex parameter positive inside) = Basic.gridCoordinate parameter denominator :=
  Unit.nearestIndex_node parameter positive inside

/-- Consecutive grid nodes retain their common midpoint, including intervals touching either unit endpoint. -/
example (denominator : Nat) (positive : 0 < denominator) (index : Fin denominator) :
    Unit.midpoint denominator index = Unit.node denominator index.succ -
      (1 / 2 : Fraction.Rational) / denominator := Unit.midpoint_eq_right positive index

/-- The first unit-grid cell retains the original endpoint and its adjacent half-mesh cut. -/
example : (Unit.cell (denominator := 4) (by decide) 0).lower = 0 ∧
    (Unit.cell (denominator := 4) (by decide) 0).upper = 1 / 8 := by constructor <;> decide +kernel

/-- An interior unit-grid cell is cut at the two actual adjacent midpoints. -/
example : (Unit.cell (denominator := 4) (by decide) 1).lower = 1 / 8 ∧
    (Unit.cell (denominator := 4) (by decide) 1).upper = 3 / 8 := by constructor <;> decide +kernel

/-- The last unit-grid cell retains its adjacent half-mesh cut and original endpoint one. -/
example : (Unit.cell (denominator := 4) (by decide) 4).lower = 7 / 8 ∧
    (Unit.cell (denominator := 4) (by decide) 4).upper = 1 := by constructor <;> decide +kernel

/-- Every original positive unit-grid cell is proper and lies in the same unit interval. -/
example (denominator : Nat) (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    0 ≤ (Unit.cell positive index).lower ∧ (Unit.cell positive index).lower < (Unit.cell positive index).upper ∧
      (Unit.cell positive index).upper ≤ 1 := Unit.cell_bounds positive index

/-- Every consecutive pair of original cells shares exactly the same retained midpoint endpoint. -/
example (denominator : Nat) (positive : 0 < denominator) (index : Fin denominator) :
    (Unit.cell positive index.castSucc).upper = (Unit.cell positive index.succ).lower :=
  Unit.cell_adjacent positive index

/-- Every original unit parameter belongs to its computed nearest cell, including midpoint ties. -/
example (parameter : Fraction.Rational) (denominator : Nat) (positive : 0 < denominator)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (Unit.cell positive (Unit.nearestIndex parameter positive inside)).Contains parameter :=
  Unit.nearestIndex_cell_contains parameter positive inside

end TestPurelib.Approximation.Rational.Grid.Unit
