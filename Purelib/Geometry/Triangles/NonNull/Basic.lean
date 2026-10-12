module

public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrance.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic
variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A noncollinear triangle with distinct vertices and three certified non-null side lines.

These retained endpoint inequalities and non-nullness proofs determine all three vertex spreads without reconstructing
side data. -/
structure NonNullTriangle (K : Type*) [Algebra.Field.ExplicitField K]
    [DecidableEq K] where
  /-- The first vertex. -/ first : Plane.Point K
  /-- The second vertex. -/ second : Plane.Point K
  /-- The third vertex. -/ third : Plane.Point K
  /-- The three vertices are not collinear. -/ notCollinear : ¬ Incidence.Collinear first second third
  /-- The first two vertices are distinct. -/ firstSecondDistinct : first ≠ second
  /-- The first and third vertices are distinct. -/ firstThirdDistinct : first ≠ third
  /-- The last two vertices are distinct. -/ secondThirdDistinct : second ≠ third
  /-- The side through the first two vertices is non-null. -/ firstSecondNonNull :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull
  /-- The side through the first and third vertices is non-null. -/ firstThirdNonNull :
    ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull
  /-- The side through the last two vertices is non-null. -/ secondThirdNonNull :
    ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull

constructive_injectivity NonNullTriangle

end Purelib.Geometry.Triangles.NonNull.Basic

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The three side quadrances of a non-null triangle. -/
def quadrances (triangle :
  NonNullTriangle K) : Coordinates3.Vector K :=
  Quadrance.Basic.triangleQuadrances triangle.first triangle.second triangle.third
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The quadrance opposite the first vertex is nonzero. -/
theorem firstQuadranceNonzero (triangle :
  NonNullTriangle K) :
    triangle.quadrances.t ≠ 0 := by
  intro quadranceZero
  apply triangle.secondThirdNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.second triangle.third
    triangle.secondThirdDistinct).2
  exact quadranceZero
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Reversing the first-to-second side preserves its non-nullness. -/
theorem firstSecondReversedNonNull (triangle :
  NonNullTriangle K) :
    ¬ (Incidence.lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.firstSecondNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.first triangle.second
    triangle.firstSecondDistinct).2
  calc
    Quadrance.quadrance triangle.first triangle.second =
        Quadrance.quadrance triangle.second triangle.first :=
      Quadrance.quadrance_symm triangle.first triangle.second
    _ = 0 :=
      (Quadrance.null_line_iff_quadrance_zero triangle.second triangle.first
        triangle.firstSecondDistinct.symm).1 reversedNull
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Reversing the first-to-third side preserves its non-nullness. -/
theorem firstThirdReversedNonNull (triangle :
  NonNullTriangle K) :
    ¬ (Incidence.lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.firstThirdNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.first triangle.third
    triangle.firstThirdDistinct).2
  calc
    Quadrance.quadrance triangle.first triangle.third =
        Quadrance.quadrance triangle.third triangle.first :=
      Quadrance.quadrance_symm triangle.first triangle.third
    _ = 0 :=
      (Quadrance.null_line_iff_quadrance_zero triangle.third triangle.first
        triangle.firstThirdDistinct.symm).1 reversedNull
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The quadrance opposite the second vertex is nonzero. -/
theorem secondQuadranceNonzero (triangle :
  NonNullTriangle K) :
    triangle.quadrances.r ≠ 0 := by
  intro quadranceZero
  apply triangle.firstThirdNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.first triangle.third
    triangle.firstThirdDistinct).2
  exact quadranceZero
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Reversing the second-to-third side preserves its non-nullness. -/
theorem secondThirdReversedNonNull (triangle :
  NonNullTriangle K) :
    ¬ (Incidence.lineThrough triangle.third triangle.second
      triangle.secondThirdDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.secondThirdNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.second triangle.third
    triangle.secondThirdDistinct).2
  calc
    Quadrance.quadrance triangle.second triangle.third =
        Quadrance.quadrance triangle.third triangle.second :=
      Quadrance.quadrance_symm triangle.second triangle.third
    _ = 0 :=
      (Quadrance.null_line_iff_quadrance_zero triangle.third triangle.second
        triangle.secondThirdDistinct.symm).1 reversedNull
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The quadrance opposite the third vertex is nonzero. -/
theorem thirdQuadranceNonzero (triangle :
  NonNullTriangle K) :
    triangle.quadrances.s ≠ 0 := by
  intro quadranceZero
  apply triangle.firstSecondNonNull
  apply (Quadrance.null_line_iff_quadrance_zero triangle.first triangle.second
    triangle.firstSecondDistinct).2
  exact quadranceZero
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end
