module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Plane.Reflection.Iteration
public import Purelib.Geometry.Plane.Reflection.Iteration.Point
import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Point
public import Purelib.Geometry.Stars.Regular.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Point

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

namespace Purelib.Geometry.Polygons.Regular.Construction

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The source's closed finite formula for the point labelled `A₂ₖ`. -/
def regularPolygonVertexAt [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (index : Nat) : Plane.Point K :=
  Iteration.Point.reflectionPointAt star.initial index initialPoint

/-- The closed formula starts at the supplied point on `l₀`. -/
theorem regularPolygonVertexAt_zero [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint) :
    regularPolygonVertexAt star initialPoint 0 = initialPoint := by
  exact RegularConstruction.reflectPoint_fixed_of_contains_direct star.initial.previous
    star.initial.previousNonNull initialPoint initialContains

/-- Exercise 14.1 identifies the closed formula with the source's successive construction: the mirror between `A₂ₖ` and
`A₂₍ₖ₊₁₎` is `l₂ₖ₊₁`. -/
theorem regularPolygonVertexAt_succ [Nontrivial K] [DecidableEq K]
    {order : Nat} (star : Regular.Basic.RegularStar K order)
    (initialPoint : Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (index : Nat) :
    regularPolygonVertexAt star initialPoint (index + 1) =
      Iteration.Point.reflectionPointAt star.initial (2 * index + 1)
        (regularPolygonVertexAt star initialPoint index) := by
  have shifted := Iteration.Point.exercise_14_1 star.initial (index + 1) 0 index initialPoint
  have initialFixed := regularPolygonVertexAt_zero star initialPoint
    initialContains
  unfold regularPolygonVertexAt at initialFixed ⊢
  rw [initialFixed] at shifted
  simpa only [Nat.zero_add,
    show index + 1 + index = 2 * index + 1 by omega0] using shifted.symm

/-- The constructed point `A₂ₖ` lies on its radial line `l₂ₖ`. -/
theorem regularPolygonVertexAt_on_radial_line
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (index : Nat) :
    (Iteration.reflectionLineAt star.initial (2 * index)).Contains
      (regularPolygonVertexAt star initialPoint index) := by
  have reflectedContains := Line.reflectLine_contains_reflectPoint
    (Iteration.reflectionLineAt star.initial index)
    (Iteration.reflectionLineAt star.initial 0)
    (Iteration.reflectionLineAt_nonNull star.initial index)
    initialPoint (by simpa only [Iteration.reflectionLineAt_zero] using initialContains)
  have radialEquivalent := Iteration.cyclic_reflection_left star.initial index 0
  have transferred := Relations.line_contains_of_equivalent radialEquivalent
    (Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial index)
      (Iteration.reflectionLineAt_nonNull star.initial index) initialPoint)
    (by simpa only [Nat.zero_add] using reflectedContains)
  simpa only [Nat.zero_add, regularPolygonVertexAt,
    Iteration.Point.reflectionPointAt] using
    transferred

/-- Every constructed vertex has the same quadrance from the common center as the supplied initial point. -/
theorem regularPolygonVertexAt_radius
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (index : Nat) :
    Quadrance.quadrance star.center (regularPolygonVertexAt star initialPoint index) =
      Quadrance.quadrance star.center initialPoint := by
  have centerFixed := RegularConstruction.reflectPoint_fixed_of_contains_direct
    (Iteration.reflectionLineAt star.initial index)
    (Iteration.reflectionLineAt_nonNull star.initial index) star.center
    (star.lineAt_contains_center index)
  have preserved := Reflection.Point.reflectPoint_preserves_quadrance
    (Iteration.reflectionLineAt star.initial index)
    (Iteration.reflectionLineAt_nonNull star.initial index) initialPoint star.center
  unfold regularPolygonVertexAt Iteration.Point.reflectionPointAt
  calc
    Quadrance.quadrance star.center
        (Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial index)
          (Iteration.reflectionLineAt_nonNull star.initial index) initialPoint) =
      Quadrance.quadrance
        (Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial index)
          (Iteration.reflectionLineAt_nonNull star.initial index) initialPoint)
        star.center := Quadrance.quadrance_symm _ _
    _ = Quadrance.quadrance
        (Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial index)
          (Iteration.reflectionLineAt_nonNull star.initial index) initialPoint)
        (Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial index)
          (Iteration.reflectionLineAt_nonNull star.initial index) star.center) := by
            rw [centerFixed]
    _ = Quadrance.quadrance initialPoint star.center := preserved
    _ = Quadrance.quadrance star.center initialPoint := Quadrance.quadrance_symm _ _

/-- No constructed vertex is the center when the supplied initial point is not the center. -/
theorem regularPolygonVertexAt_ne_center
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (initialDistinct : initialPoint ≠ star.center) (index : Nat) :
    regularPolygonVertexAt star initialPoint index ≠ star.center := by
  intro vertexCenter
  apply initialDistinct
  have centerFixed := RegularConstruction.reflectPoint_fixed_of_contains_direct
    (Iteration.reflectionLineAt star.initial index)
    (Iteration.reflectionLineAt_nonNull star.initial index) star.center
    (star.lineAt_contains_center index)
  calc
    initialPoint = Iteration.Point.reflectionPointAt star.initial index
        (Iteration.Point.reflectionPointAt star.initial index initialPoint) :=
      (Iteration.Point.reflectionPointAt_involutive star.initial index initialPoint).symm
    _ = Iteration.Point.reflectionPointAt star.initial index star.center := by
      exact congrArg (Iteration.Point.reflectionPointAt star.initial index) vertexCenter
    _ = star.center := centerFixed

/-- The two finite closing representatives return the construction to its initial point after exactly `order` requested
vertices. -/
theorem regularPolygonVertexAt_closes
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint) :
    regularPolygonVertexAt star initialPoint order = initialPoint := by
  calc
    regularPolygonVertexAt star initialPoint order =
        Reflection.Point.reflectPoint (Iteration.reflectionLineAt star.initial order)
          (Iteration.reflectionLineAt_nonNull star.initial order) initialPoint := rfl
    _ = Reflection.Point.reflectPoint star.initial.previous star.initial.previousNonNull
        initialPoint := Reflection.Point.reflectPoint_eq_of_equivalent
          (Iteration.reflectionLineAt star.initial order) star.initial.previous
          (Iteration.reflectionLineAt_nonNull star.initial order)
          star.initial.previousNonNull star.closesAtOrder initialPoint
    _ = initialPoint := RegularConstruction.reflectPoint_fixed_of_contains_direct
      star.initial.previous star.initial.previousNonNull initialPoint
      initialContains

/-- Distinct nonparallel radial lines force their constructed vertices to be distinct, since their only common point is
the center. -/
theorem regularPolygonVertices_ne_of_radial_nonparallel
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : Regular.Basic.RegularStar K order) (initialPoint : Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (first second : Nat)
    (radialNonparallel :
      ¬ (Iteration.reflectionLineAt star.initial (2 * first)).Parallel
        (Iteration.reflectionLineAt star.initial (2 * second))) :
    regularPolygonVertexAt star initialPoint first ≠
      regularPolygonVertexAt star initialPoint second := by
  intro verticesEqual
  have firstContains := regularPolygonVertexAt_on_radial_line star initialPoint
    initialContains first
  have secondContains := regularPolygonVertexAt_on_radial_line star initialPoint
    initialContains second
  rw [← verticesEqual] at secondContains
  have vertexIntersection := Intersection.lineIntersection_unique
    (Iteration.reflectionLineAt star.initial (2 * first))
    (Iteration.reflectionLineAt star.initial (2 * second)) radialNonparallel
    (regularPolygonVertexAt star initialPoint first)
    firstContains secondContains
  have centerIntersection := Intersection.lineIntersection_unique
    (Iteration.reflectionLineAt star.initial (2 * first))
    (Iteration.reflectionLineAt star.initial (2 * second)) radialNonparallel star.center
    (star.lineAt_contains_center (2 * first))
    (star.lineAt_contains_center (2 * second))
  exact (regularPolygonVertexAt_ne_center star initialPoint initialDistinct
    first)
    (vertexIntersection.trans centerIntersection.symm)

end Purelib.Geometry.Polygons.Regular.Construction

end
