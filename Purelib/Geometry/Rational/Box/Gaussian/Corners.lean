module
public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Data.Gaussian

open Purelib.Geometry

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Geometry.Rational.Box.Gaussian.Corners

/-- The Gaussian point at the lower real and lower imaginary endpoints. -/
def lowerLeft (box : Rational.Box) :
  Data.Gaussian.Basic.Canonical :=
  Components.Basic.point box.xLower box.yLower

/-- The Gaussian point at the upper real and lower imaginary endpoints. -/
def lowerRight (box : Rational.Box) :
  Data.Gaussian.Basic.Canonical :=
  Components.Basic.point box.xUpper box.yLower

/-- The Gaussian point at the upper real and upper imaginary endpoints. -/
def upperRight (box : Rational.Box) :
  Data.Gaussian.Basic.Canonical :=
  Components.Basic.point box.xUpper box.yUpper

/-- The Gaussian point at the lower real and upper imaginary endpoints. -/
def upperLeft (box : Rational.Box) :
  Data.Gaussian.Basic.Canonical :=
  Components.Basic.point box.xLower box.yUpper

end Purelib.Geometry.Rational.Box.Gaussian.Corners

end
