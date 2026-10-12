module
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Order.Basic

open Purelib.Geometry

section
@[expose] public section

/-!
# Choice-free eight-cell complement of a central band

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the selected Newton band; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace Purelib.Geometry.Rational.Box.Grid.Central

/-- The outer-grid rectangle below and to the left of the strictly interior central box. -/
def southwest (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := strict.left.le
  y_valid := strict.bottom.le

/-- The outer-grid rectangle to the left of the strictly interior central box. -/
def west (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := center.yLower
  yUpper := center.yUpper
  x_valid := strict.left.le
  y_valid := center.y_valid

/-- The outer-grid rectangle above and to the left of the strictly interior central box. -/
def northwest (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := outer.xLower
  xUpper := center.xLower
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := strict.left.le
  y_valid := strict.top.le

/-- The outer-grid rectangle below of the strictly interior central box. -/
def south (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := center.xLower
  xUpper := center.xUpper
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := center.x_valid
  y_valid := strict.bottom.le

/-- The outer-grid rectangle above of the strictly interior central box. -/
def north (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := center.xLower
  xUpper := center.xUpper
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := center.x_valid
  y_valid := strict.top.le

/-- The outer-grid rectangle below and to the right of the strictly interior central box. -/
def southeast (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := outer.yLower
  yUpper := center.yLower
  x_valid := strict.right.le
  y_valid := strict.bottom.le

/-- The outer-grid rectangle to the right of the strictly interior central box. -/
def east (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := center.yLower
  yUpper := center.yUpper
  x_valid := strict.right.le
  y_valid := center.y_valid

/-- The outer-grid rectangle above and to the right of the strictly interior central box. -/
def northeast (outer center : Rational.Box)
    (strict : center.StrictInterior outer) : Rational.Box where
  xLower := center.xUpper
  xUpper := outer.xUpper
  yLower := center.yUpper
  yUpper := outer.yUpper
  x_valid := strict.right.le
  y_valid := strict.top.le
end Purelib.Geometry.Rational.Box.Grid.Central

end
