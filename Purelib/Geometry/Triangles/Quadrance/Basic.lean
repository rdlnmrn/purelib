module
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Algebra.Field.ExplicitField

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Triangles.Quadrance.Basic
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The three side quadrances, indexed by their opposite vertices. -/
def triangleQuadrances (first second third : Plane.Point
  K) : Coordinates3.Vector K :=
  ⟨Quadrance.quadrance second third, Quadrance.quadrance first third, Quadrance.quadrance first second⟩

end Purelib.Geometry.Triangles.Quadrance.Basic

end
