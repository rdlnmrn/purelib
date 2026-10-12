module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.Face.Altitude.Gram

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A denominator-free altitude to a shared edge. Scaling by `L` avoids introducing the projection quotient `D/L`. -/
def scaledFaceAltitude
    (shared other : Coordinates3.Vector K) (L D : K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.scale L other) (Coordinates3.Vector.neg (Coordinates3.Vector.scale D
    shared))

/-- Gram calculation for the two scaled altitudes used to measure a dihedral spread. -/
theorem scaledFaceAltitude_metrics
    (shared first second : Coordinates3.Vector K) (L D E : K)
    (sharedQuadrance : Coordinates3.Vector.quadrance shared = L)
    (firstQuadrance : Coordinates3.Vector.quadrance first = L)
    (secondQuadrance : Coordinates3.Vector.quadrance second = L)
    (sharedFirst : Coordinates3.Vector.dot shared first = D)
    (sharedSecond : Coordinates3.Vector.dot shared second = D)
    (firstSecond : Coordinates3.Vector.dot first second = E) :
    Coordinates3.Vector.quadrance (scaledFaceAltitude shared first L D) =
        L * (L ^ 2 - D ^ 2) ∧
      Coordinates3.Vector.quadrance (scaledFaceAltitude shared second L D) =
        L * (L ^ 2 - D ^ 2) ∧
      Coordinates3.Vector.dot (scaledFaceAltitude shared first L D)
          (scaledFaceAltitude shared second L D) =
        L * (E * L - D ^ 2) := by
  have firstShared : Coordinates3.Vector.dot first shared = D := by
    rw [Coordinates3.Vector.dot_comm]
    exact sharedFirst
  have secondShared : Coordinates3.Vector.dot second shared = D := by
    rw [Coordinates3.Vector.dot_comm]
    exact sharedSecond
  change Coordinates3.Vector.dot shared shared = L at sharedQuadrance
  change Coordinates3.Vector.dot first first = L at firstQuadrance
  change Coordinates3.Vector.dot second second = L at secondQuadrance
  unfold scaledFaceAltitude Coordinates3.Vector.quadrance
  simp only [Coordinates3.Vector.dot_add_left, Coordinates3.Vector.dot_add_right,
    Coordinates3.Vector.dot_neg_left, Coordinates3.Vector.dot_neg_right,
    Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right]
  rw [sharedQuadrance, firstQuadrance, secondQuadrance,
    sharedFirst, sharedSecond, firstShared, secondShared, firstSecond]
  constructor
  · ring1
  constructor <;> ring1
end
end Purelib.Geometry.Space.Face.Altitude.Gram

end
