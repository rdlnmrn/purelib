module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Plane.Sector.Spread.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Exercise 25.2: a direct finite-candidate solution -/

/-- The numerator of the spread between the two displayed rays based at `base`, without constructing line quotients or
dividing by their norms. -/
def sectorSpreadNumerator
    (base first second : Geometry.Plane.Point K) : K :=
  ((first.x - base.x) * (second.y - base.y) -
      (first.y - base.y) * (second.x - base.x)) ^ 2

/-- A denominator-cleared check that a displayed sector has spread `numerator/denominator`. -/
def MatchesSectorSpread
    (base first second : Geometry.Plane.Point K) (numerator denominator : K) : Prop :=
  denominator * sectorSpreadNumerator base first second =
    numerator * Quadrance.quadrance base first * Quadrance.quadrance base second
end
end Purelib.Geometry.Plane.Sector.Spread.Cleared

end
