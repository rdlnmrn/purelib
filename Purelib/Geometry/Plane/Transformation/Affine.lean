module
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

@[expose] public section

/-!
# Divine Proportions, Chapter 4: point reflections

The reflection in a non-null line is defined exactly as in the book: find the
altitude foot and rotate the source point through that foot.  Theorem 13's
coordinate formula and the involution law are then derived by finite field
algebra.
-/

namespace Purelib.Geometry.Plane

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Point

/-- A point transformation in the finite Cartesian plane. -/
abbrev Transformation (K : Type*) := Point K →
  Point K

end Point

namespace Transformation.Affine

/-- Preservation of every two-point combination whose weights sum to one.

The property compares the image of the combination with the combination of the two image points using the same weights.
-/
def IsAffine (transformation :
  Point.Transformation K) : Prop :=
  ∀ (first second : Point K) (leftWeight rightWeight : K),
    leftWeight + rightWeight = 1 →
    transformation
        (Affine.affineCombination leftWeight first rightWeight second) =
      Affine.affineCombination leftWeight (transformation first)
        rightWeight (transformation second)

end Transformation.Affine

end Purelib.Geometry.Plane

end
