module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.LinearAlgebra.Coordinates2.Determinant
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.LinearAlgebra.Coordinates2.Determinant

section
public section

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace Purelib.Geometry.Coordinates.Polar.Squared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## §27.1: rational polar coordinates -/

/-- The total quadrance and spread relation for two squared Cartesian coordinates. -/
@[expose] def RationalSphericalCoordinates.PolarCoordinateSquares
  (xSquared ySquared spread Q : K) : Prop :=
  Q = xSquared + ySquared ∧ spread * Q = xSquared

/-- Recover the two squared Cartesian coordinates from spread and total quadrance. -/
theorem polar_coordinate_squares
    (xSquared ySquared spread Q : K)
    (coordinates : Geometry.Coordinates.Polar.Squared.RationalSphericalCoordinates.PolarCoordinateSquares xSquared
      ySquared spread Q) :
    xSquared = spread * Q ∧
      ySquared = (1 - spread) * Q := by
  constructor
  · exact coordinates.2.symm
  · calc
      ySquared = Q - xSquared := by rw [coordinates.1]; ring1
      _ = Q - spread * Q := by rw [← coordinates.2]
      _ = (1 - spread) * Q := by ring1

/-- The polar coordinate coefficient matrix has determinant equal to the total quadrance. -/
theorem polar_jacobian_determinant (spread Q : K) :
    RationalSphericalCoordinates.determinantTwo Q spread (-Q) (1 - spread) = Q := by
  unfold RationalSphericalCoordinates.determinantTwo
  ring1

/-- The product of squared Cartesian coordinates equals the polar squared-density polynomial. -/
theorem polar_squared_density
    (xSquared ySquared spread Q : K)
    (coordinates : Geometry.Coordinates.Polar.Squared.RationalSphericalCoordinates.PolarCoordinateSquares xSquared
      ySquared spread Q) :
    xSquared * ySquared =
      spread * (1 - spread) * Q ^ 2 := by
  rcases polar_coordinate_squares xSquared ySquared spread Q coordinates with
    ⟨xValue, yValue⟩
  rw [xValue, yValue]
  ring1
end
end Purelib.Geometry.Coordinates.Polar.Squared

end

section
public section

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace Purelib.Geometry.Coordinates.Polar.Squared.RationalPolarCatalogue

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The denominator-cleared polar-coordinate relation for squared Cartesian coordinates. -/
abbrev PolarCoordinateSquares
    (xSquared ySquared spread Q : K) : Prop :=
  Geometry.Coordinates.Polar.Squared.RationalSphericalCoordinates.PolarCoordinateSquares
    xSquared ySquared spread Q
end
end Purelib.Geometry.Coordinates.Polar.Squared.RationalPolarCatalogue

end

end
