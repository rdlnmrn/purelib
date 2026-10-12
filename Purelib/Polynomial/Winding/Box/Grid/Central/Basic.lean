module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation
public import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free eight-cell complement of a central band

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the selected Newton band; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace Purelib.Polynomial.Winding.Box.Grid.Central.Basic

set_option genInjectivity false in
/-- The eight clear complement cells and exact raw additivity. -/
structure Arrangement
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (outer center : Box) where
  /-- Both coordinate intervals of the central box have positive width. -/ centerProper : center.Proper
  /-- The central box lies strictly inside the outer box. -/ centerInterior : center.StrictInterior outer
  /-- The southwest complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/
    southwest : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The west complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/ west :
    Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The northwest complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/
    northwest : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The south complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/ south
    : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The north complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/ north
    : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The southeast complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/
    southeast : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The east complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/ east :
    Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The northeast complement cell, retaining its boundary clearance and relation to the outer and central boxes. -/
    northeast : Clearance.Box.Grid.Central.Cell.ClearCell p outer center
  /-- The outer raw winding equals the central raw winding plus the eight complement contributions. -/ additive :
    Winding.Box.Basic.quadrupledBoxWinding p outer =
    Winding.Box.Basic.quadrupledBoxWinding p center +
      Winding.Box.Basic.quadrupledBoxWinding p southwest.box +
      Winding.Box.Basic.quadrupledBoxWinding p west.box +
      Winding.Box.Basic.quadrupledBoxWinding p northwest.box +
      Winding.Box.Basic.quadrupledBoxWinding p south.box +
      Winding.Box.Basic.quadrupledBoxWinding p north.box +
      Winding.Box.Basic.quadrupledBoxWinding p southeast.box +
      Winding.Box.Basic.quadrupledBoxWinding p east.box +
      Winding.Box.Basic.quadrupledBoxWinding p northeast.box
  /-- Distinct displayed complement cells have separated interiors. -/ complementsPairwise :
    [southwest, west, northwest, south, north, southeast, east,
      northeast].Pairwise
        (fun left right => left.box.InteriorSeparated right.box)
  /-- Every point of the outer box belongs to the center or one of the eight displayed complement cells. -/ covers : ∀
    {z}, outer.Contains z →
    center.Contains z ∨
      ∃ cell ∈ [southwest, west, northwest, south, north, southeast, east,
        northeast], cell.box.Contains z

constructive_injectivity Arrangement

namespace Arrangement.mk

end Arrangement.mk

namespace Arrangement.mk

end Arrangement.mk

namespace Arrangement

/-- The fixed finite complement order used by isolation and deterministic
negative-cell selection. -/
def complements
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (grid : Arrangement p outer center) : List (Clearance.Box.Grid.Central.Cell.ClearCell p
      outer center) :=
  [grid.southwest, grid.west, grid.northwest, grid.south, grid.north,
    grid.southeast, grid.east, grid.northeast]

end Arrangement

namespace Arrangement

/-- The ordered complement list inherits the grid certificate's pairwise interior separation. -/
theorem complements_pairwise
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (grid : Arrangement p outer center) :
    grid.complements.Pairwise
      (fun left right => left.box.InteriorSeparated right.box) :=
  grid.complementsPairwise

end Arrangement

end Purelib.Polynomial.Winding.Box.Grid.Central.Basic

end
