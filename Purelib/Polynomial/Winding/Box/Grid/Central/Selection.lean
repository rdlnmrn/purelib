module

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Grid.Central.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Int.Order

open Purelib.Data
open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Selecting a negative complement cell

The retained eight-cell winding grid determines a fixed first-negative scan.
The first seven cells are tested in order, and the northeast cell is the
fallback. Exact winding additivity proves negativity under the stated bounds.
-/

namespace Purelib.Polynomial.Winding.Box.Grid.Central.Basic.Arrangement

/-- Select the first complement cell with negative raw winding, defaulting to the northeast cell.

The fixed order tests the first seven cells. Negativity of the returned cell requires the separate winding hypotheses in
`firstNegative_rawWinding_neg`. -/
@[expose] public def firstNegative
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (grid : Arrangement p outer center) : Clearance.Box.Grid.Central.Cell.ClearCell p outer
      center :=
  if Winding.Box.Basic.quadrupledBoxWinding p grid.southwest.box < 0 then grid.southwest
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.west.box < 0 then grid.west
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.northwest.box < 0 then grid.northwest
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.south.box < 0 then grid.south
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.north.box < 0 then grid.north
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.southeast.box < 0 then grid.southeast
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.east.box < 0 then grid.east
  else grid.northeast

/-- The selected complement cell has negative raw winding.

The outer winding must be negative and the central winding must be four.
If the first seven tests fail, their nonnegative contributions and the exact
additivity certificate force the retained northeast fallback to be negative. -/
public theorem firstNegative_rawWinding_neg
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (grid : Arrangement p outer center)
    (outerNegative : Winding.Box.Basic.quadrupledBoxWinding p outer < 0)
    (centerFour : Winding.Box.Basic.quadrupledBoxWinding p center = 4) :
    Winding.Box.Basic.quadrupledBoxWinding p grid.firstNegative.box < 0 := by
  by_cases swNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.southwest.box < 0
  · rewrite [firstNegative, if_pos swNegative]
    exact swNegative
  by_cases wNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.west.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_pos wNegative]
    exact wNegative
  by_cases nwNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.northwest.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_pos nwNegative]
    exact nwNegative
  by_cases sNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.south.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_neg nwNegative, if_pos sNegative]
    exact sNegative
  by_cases nNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.north.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_neg nwNegative, if_neg sNegative, if_pos nNegative]
    exact nNegative
  by_cases seNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.southeast.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_neg nwNegative, if_neg sNegative, if_neg nNegative,
      if_pos seNegative]
    exact seNegative
  by_cases eNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.east.box < 0
  · rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_neg nwNegative, if_neg sNegative, if_neg nNegative,
      if_neg seNegative, if_pos eNegative]
    exact eNegative
  have neNegative : Winding.Box.Basic.quadrupledBoxWinding p grid.northeast.box < 0 := by
    have swNonnegative := Int.Order.le_of_not_lt swNegative
    have wNonnegative := Int.Order.le_of_not_lt wNegative
    have nwNonnegative := Int.Order.le_of_not_lt nwNegative
    have sNonnegative := Int.Order.le_of_not_lt sNegative
    have nNonnegative := Int.Order.le_of_not_lt nNegative
    have seNonnegative := Int.Order.le_of_not_lt seNegative
    have eNonnegative := Int.Order.le_of_not_lt eNegative
    rewrite [grid.additive, centerFour] at outerNegative
    omega
  rewrite [firstNegative, if_neg swNegative, if_neg wNegative, if_neg nwNegative, if_neg sNegative, if_neg nNegative,
    if_neg seNegative, if_neg eNegative]
  exact neNegative

end Purelib.Polynomial.Winding.Box.Grid.Central.Basic.Arrangement
