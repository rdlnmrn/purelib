module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.LinearAlgebra

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A displayed affine plane `n·x+c=0`. -/
structure Plane3 (K : Type*) where
  /-- The retained normal vector in the affine plane equation. -/ normal : Coordinates3.Vector K
  /-- The constant term of the affine plane equation. -/ constant : K

constructive_injectivity Plane3

end Purelib.Geometry.Space.Metric

end

section
public section
namespace Purelib.Geometry.Space.Metric.Plane3
variable {K : Type*} [ExplicitField K]
section

/-- The displayed plane normal has zero quadrance. -/
@[expose] def IsNull (plane : Plane3 K) : Prop :=
  Coordinates3.Vector.quadrance plane.normal = 0

end
end Purelib.Geometry.Space.Metric.Plane3

end

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

/-- A spatial point represented by its three field coordinates. -/
abbrev Point3 (K : Type*) := Coordinates3.Vector K
end Purelib.Geometry.Space.Metric

end

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A displayed affine line with one point and one direction. -/
structure Line3 (K : Type*) where
  /-- A retained point on the displayed line. -/ point : Point3 K
  /-- The retained direction of the displayed line. -/ direction : Coordinates3.Vector K

constructive_injectivity Line3

end Purelib.Geometry.Space.Metric

end

section
public section
namespace Purelib.Geometry.Space.Metric.Line3
variable {K : Type*} [ExplicitField K]
section

/-- A point lies on the displayed affine line for some field parameter. -/
@[expose] def Contains (line : Line3 K) (point :
  Point3 K) : Prop :=
  ∃ scalar : K,
    point = Coordinates3.Vector.add line.point (Coordinates3.Vector.scale scalar line.direction)
end
end Purelib.Geometry.Space.Metric.Line3

end

section
public section
namespace Purelib.Geometry.Space.Metric.Line3
variable {K : Type*} [ExplicitField K]
section

/-- The displayed line direction has zero quadrance. -/
@[expose] def IsNull (line : Line3 K) : Prop :=
  Coordinates3.Vector.quadrance line.direction = 0
end
end Purelib.Geometry.Space.Metric.Line3

end

section
public section
namespace Purelib.Geometry.Space.Metric.Line3
variable {K : Type*} [ExplicitField K]
section

/-- A line is perpendicular to a plane when its displayed direction is a nonzero scalar multiple of the displayed
normal. -/
@[expose] def Perpendicular (line : Line3 K) (plane :
  Plane3 K) : Prop :=
  Coordinates3.Vector.Parallel line.direction plane.normal

end
end Purelib.Geometry.Space.Metric.Line3

end

section
public section
namespace Purelib.Geometry.Space.Metric.Plane3
variable {K : Type*} [ExplicitField K]
section

/-- The point satisfies the displayed affine plane equation. -/
@[expose] def Contains (plane : Plane3 K) (point :
  Point3 K) : Prop :=
  Coordinates3.Vector.dot plane.normal point + plane.constant = 0
end
end Purelib.Geometry.Space.Metric.Plane3

end

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

/-- Chapter 22.1's spread between a line and a plane. It is the complement of the spread between the line direction and
the plane normal. -/
@[expose] def linePlaneSpread (line : Line3 K) (plane :
  Plane3 K)
    (_lineNonNull : ¬ line.IsNull) (_planeNonNull : ¬ plane.IsNull) : K :=
  Coordinates3.Vector.dot line.direction plane.normal ^ 2 /
    (Coordinates3.Vector.quadrance line.direction *
      Coordinates3.Vector.quadrance plane.normal)
end Purelib.Geometry.Space.Metric

end

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

/-- The two spatial spread definitions are complementary by construction. -/
theorem linePlaneSpread_add_directionSpread
    (line : Line3 K) (plane : Plane3 K)
    (_lineNonNull : ¬ line.IsNull) (_planeNonNull : ¬ plane.IsNull) :
    linePlaneSpread line plane _lineNonNull _planeNonNull +
        Coordinates3.Vector.spread line.direction plane.normal
          _lineNonNull _planeNonNull = 1 := by
  unfold linePlaneSpread Coordinates3.Vector.spread
  ring1

end Purelib.Geometry.Space.Metric

end

section
public section
namespace Purelib.Geometry.Space.Metric
variable {K : Type*} [ExplicitField K]

/-- Chapter 22.1's spread between two planes, computed from their normals. -/
@[expose] def planeSpread (first second : Plane3 K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) : K :=
  Coordinates3.Vector.spread first.normal second.normal firstNonNull secondNonNull
end Purelib.Geometry.Space.Metric

end
