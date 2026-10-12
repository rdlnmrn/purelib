module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Iteration.Point
public import Purelib.Geometry.Polygons.Regular.Construction
import Purelib.Geometry.Stars.Regular.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Polygons.Regular

open Purelib.Geometry.Stars

section
@[expose] public section

/-!
# Divine Proportions, regular polygon construction

The source uses a doubly infinite reflection sequence.  Here every line and
point is obtained from the already executable natural-number iterator.  A
request for vertex `k` computes exactly the first `k` reflection steps.

The point-reflection product identity below is the finite natural-index form
of Exercise 14.1.  It is then used to prove that the closed formula
`A₂ₖ = σ_{lₖ}(A₀)` agrees with the source's successive construction through
the intervening mirrors `l₂ₖ₊₁`.
-/

namespace Purelib.Geometry.Polygons.Regular.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- The finite data certifying that the source construction gives a regular `order`-gon. Its vertices are the executable
points `A₀,A₂,...`; all other regularity properties are consequences of the generic construction lemmas. -/
structure ConstructedRegularPolygon (K : Type*)
  [Algebra.Field.ExplicitField K]
    [Nontrivial K] [DecidableEq K] (order : Nat) where
  /-- The retained regular star controlling the reflection sequence. -/ star : Regular.Basic.RegularStar K order
  /-- The initial polygon vertex. -/ initialPoint : Plane.Point K
  /-- The initial vertex lies on the first reflection line. -/ initialContains : star.initial.previous.Contains
    initialPoint
  /-- The initial vertex differs from the common center. -/ initialDistinct : initialPoint ≠ star.center
  /-- Distinct indices below the order give distinct reflected vertices. -/ pairwiseVertices :
    ∀ first second : Fin order, first ≠ second →
      Construction.regularPolygonVertexAt star initialPoint first.val ≠
        Construction.regularPolygonVertexAt star initialPoint second.val

constructive_injectivity ConstructedRegularPolygon

namespace ConstructedRegularPolygon

variable [Nontrivial K] [DecidableEq K] {order : Nat}

/-- The vertex `A₂ₖ` of the finite polygon. -/
def vertex (polygon :
  ConstructedRegularPolygon K order)
    (index : Fin order) : Plane.Point K :=
  Construction.regularPolygonVertexAt polygon.star polygon.initialPoint index.val

/-- Distinct finite vertex indices give distinct constructed polygon vertices. -/
theorem vertex_injective (polygon :
  ConstructedRegularPolygon K order) :
    Function.Injective polygon.vertex := by
  intro first second verticesEqual
  by_cases same : first = second
  · exact same
  · exact False.elim ((polygon.pairwiseVertices first second same)
      verticesEqual)

/-- Each constructed vertex lies on its corresponding even-indexed radial line. -/
theorem vertex_on_radial_line (polygon :
  ConstructedRegularPolygon K order)
    (index : Fin order) :
    (Iteration.reflectionLineAt polygon.star.initial (2 * index.val)).Contains
      (polygon.vertex index) :=
  Construction.regularPolygonVertexAt_on_radial_line polygon.star polygon.initialPoint
    polygon.initialContains index.val

/-- Every constructed vertex has the initial point's quadrance from the center. -/
theorem vertex_radius (polygon :
  ConstructedRegularPolygon K order)
    (index : Fin order) :
    Quadrance.quadrance polygon.star.center (polygon.vertex index) =
      Quadrance.quadrance polygon.star.center polygon.initialPoint :=
  Construction.regularPolygonVertexAt_radius polygon.star polygon.initialPoint index.val

/-- The next vertex is obtained by reflection in the intervening odd-indexed mirror. -/
theorem successive_step (polygon :
  ConstructedRegularPolygon K order)
    (index : Nat) :
    Construction.regularPolygonVertexAt polygon.star polygon.initialPoint (index + 1) =
      Iteration.Point.reflectionPointAt polygon.star.initial (2 * index + 1)
        (Construction.regularPolygonVertexAt polygon.star polygon.initialPoint index) :=
  Construction.regularPolygonVertexAt_succ polygon.star polygon.initialPoint
    polygon.initialContains index

/-- The reflection construction returns to its initial point at the polygon order. -/
theorem closes (polygon :
  ConstructedRegularPolygon K order) :
    Construction.regularPolygonVertexAt polygon.star polygon.initialPoint order =
      polygon.initialPoint :=
  Construction.regularPolygonVertexAt_closes polygon.star polygon.initialPoint
    polygon.initialContains

end ConstructedRegularPolygon

end Purelib.Geometry.Polygons.Regular.Basic

end
