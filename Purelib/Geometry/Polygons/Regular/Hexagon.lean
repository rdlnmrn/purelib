module
public import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.HalfTurn.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Parallel
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Composition
import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Iteration.Point
import Purelib.Geometry.Plane.Reflection.Line
public import Purelib.Geometry.Polygons.Regular.Basic
import Purelib.Geometry.Polygons.Regular.Construction
import Purelib.Geometry.Stars.Regular.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Polygons

open Purelib.Geometry.Polygons.Regular

open Purelib.Geometry.Stars

section
@[expose] public section

/-!
# Divine Proportions, Examples 14.11 and 14.12

The pentagon and hexagon are represented by five and six executable vertices.
The generic construction proves their radial incidences, equal radii,
successive-reflection equations, and closure.  This file supplies the two
finite distinctness arguments from the source: doubling permutes the five
radial lines, while the three opposite hexagon pairs use perpendicular
mirrors and central rotation.
-/

namespace Purelib.Geometry.Polygons.Regular.Hexagon

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- The six radial line labels are `0,2,4,0,2,4`. -/
def hexagonRadialIndex : Fin 6 → Fin 6 :=
  Data.Fin.casesByRecursion 0
    (Data.Fin.casesByRecursion 2
      (Data.Fin.casesByRecursion 4
        (Data.Fin.casesByRecursion 0 (Data.Fin.casesByRecursion 2 (fun _ => 4)))))

/-- Normalize the six displayed radial lines into the finite star prefix. -/
theorem hexagon_radial_line_equivalent
    (star : Regular.Basic.RegularStar K 6) (index : Fin 6) :
    (Iteration.reflectionLineAt star.initial (2 * index.val)).Equivalent
      (Iteration.reflectionLineAt star.initial (hexagonRadialIndex index).val) := by
  rcases Data.Fin.Cases.finSix_cases index with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geometry.Plane.Line.equivalent_refl _
  · exact Geometry.Plane.Line.equivalent_refl _
  · exact Geometry.Plane.Line.equivalent_refl _
  · change (Iteration.reflectionLineAt star.initial 6).Equivalent
      (Iteration.reflectionLineAt star.initial 0)
    simpa only [Iteration.reflectionLineAt_zero] using star.closesAtOrder
  · change (Iteration.reflectionLineAt star.initial 8).Equivalent
      (Iteration.reflectionLineAt star.initial 2)
    exact star.lineAt_add_order_equivalent 2
  · change (Iteration.reflectionLineAt star.initial 10).Equivalent
      (Iteration.reflectionLineAt star.initial 4)
    exact star.lineAt_add_order_equivalent 4

/-- Distinct normalized radial labels give nonparallel hexagon radial lines. -/
theorem hexagon_radial_lines_nonparallel_of_normalized_ne
    (star : Regular.Basic.RegularStar K 6) (first second : Fin 6)
    (normalizedDifferent : hexagonRadialIndex first ≠
      hexagonRadialIndex second) :
    ¬ (Iteration.reflectionLineAt star.initial (2 * first.val)).Parallel
      (Iteration.reflectionLineAt star.initial (2 * second.val)) := by
  exact Parallel.nonparallel_of_equivalent_pairs
    (Iteration.reflectionLineAt star.initial (2 * first.val))
    (Iteration.reflectionLineAt star.initial (hexagonRadialIndex first).val)
    (Iteration.reflectionLineAt star.initial (2 * second.val))
    (Iteration.reflectionLineAt star.initial (hexagonRadialIndex second).val)
    (hexagon_radial_line_equivalent star first)
    (hexagon_radial_line_equivalent star second)
    (star.pairwiseNonparallel (hexagonRadialIndex first)
      (hexagonRadialIndex second) normalizedDifferent)

/-- In an order-six star, `lₖ` and `lₖ₊₃` are perpendicular for each of the three requested values `k=0,1,2`. -/
theorem hexagon_opposite_lines_perpendicular
    (star : Regular.Basic.RegularStar K 6) (twoNonzero : (2 : K) ≠ 0)
    (first : Nat) (firstBelowThree : first < 3) :
    (Iteration.reflectionLineAt star.initial first).Perpendicular
      (Iteration.reflectionLineAt star.initial (first + 3)) := by
  have reflectedEquivalent := Iteration.cyclic_reflection_left star.initial 3 first
  have periodicEquivalent := star.lineAt_add_order_equivalent first
  have fixedEquivalent :
      (Line.reflectLine (Iteration.reflectionLineAt star.initial (first + 3))
        (Iteration.reflectionLineAt star.initial first)
        (Iteration.reflectionLineAt_nonNull star.initial (first + 3))).Equivalent
          (Iteration.reflectionLineAt star.initial first) := by
    exact Relations.line_equivalent_trans (by
      simpa only [show first + 2 * 3 = first + 6 by omega0] using
        reflectedEquivalent) periodicEquivalent
  have fixedDirection :
      (Iteration.reflectionLineAt star.initial first).Parallel
        (Line.reflectLine (Iteration.reflectionLineAt star.initial (first + 3))
          (Iteration.reflectionLineAt star.initial first)
          (Iteration.reflectionLineAt_nonNull star.initial (first + 3))) :=
    Geometry.Plane.Line.parallel_symm (Relations.line_parallel_of_equivalent fixedEquivalent)
  have alternatives := Line.parallel_or_perpendicular_of_parallel_reflectLine
    (Iteration.reflectionLineAt star.initial (first + 3))
    (Iteration.reflectionLineAt star.initial first)
    (Iteration.reflectionLineAt_nonNull star.initial (first + 3))
    twoNonzero fixedDirection
  rcases alternatives with parallel | perpendicular
  · let firstIndex : Fin 6 := ⟨first, by omega0⟩
    let oppositeIndex : Fin 6 := ⟨first + 3, by omega0⟩
    have different : firstIndex ≠ oppositeIndex := by
      intro same
      have values : first = first + 3 := by
        simpa only [firstIndex, oppositeIndex] using congrArg Fin.val same
      omega0
    exact False.elim ((star.pairwiseNonparallel firstIndex oppositeIndex
      different) (by simpa only [firstIndex, oppositeIndex] using parallel))
  · exact perpendicular

/-- Opposite constructed hexagon vertices are distinct: equality would make the noncentral initial point fixed by
rotation in the star center. -/
theorem hexagon_opposite_vertices_ne
    (star : Regular.Basic.RegularStar K 6) (initialPoint : Geometry.Plane.Point K)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0)
    (first : Nat) (firstBelowThree : first < 3) :
    Construction.regularPolygonVertexAt star initialPoint first ≠
      Construction.regularPolygonVertexAt star initialPoint (first + 3) := by
  intro verticesEqual
  have composedFixed :
      Iteration.Point.reflectionPointAt star.initial (first + 3)
          (Iteration.Point.reflectionPointAt star.initial first initialPoint) = initialPoint := by
    calc
      Iteration.Point.reflectionPointAt star.initial (first + 3)
          (Iteration.Point.reflectionPointAt star.initial first initialPoint) =
        Iteration.Point.reflectionPointAt star.initial (first + 3)
          (Iteration.Point.reflectionPointAt star.initial (first + 3) initialPoint) := by
            exact congrArg (Iteration.Point.reflectionPointAt star.initial (first + 3))
              verticesEqual
      _ = initialPoint := Iteration.Point.reflectionPointAt_involutive star.initial
        (first + 3) initialPoint
  have compositionIsRotation := Composition.reflectPoint_perpendicular_comp_eq_rotate
    (Iteration.reflectionLineAt star.initial first)
    (Iteration.reflectionLineAt star.initial (first + 3))
    (Iteration.reflectionLineAt_nonNull star.initial first)
    (Iteration.reflectionLineAt_nonNull star.initial (first + 3))
    (hexagon_opposite_lines_perpendicular star twoNonzero first
      firstBelowThree)
    star.center (star.lineAt_contains_center first)
    (star.lineAt_contains_center (first + 3)) initialPoint
  have rotationFixed : HalfTurn.Basic.rotateInPoint star.center initialPoint = initialPoint :=
    compositionIsRotation.symm.trans composedFixed
  exact initialDistinct
    ((HalfTurn.Basic.rotateInPoint_fixed_iff_center star.center initialPoint twoNonzero).1
      rotationFixed)

/-- Complete finite classification of two hexagon indices: they are equal, their radial labels differ, or they form one
of the three opposite pairs. -/
private theorem hexagon_index_classification (first second : Fin 6) :
    first = second ∨
      hexagonRadialIndex first ≠ hexagonRadialIndex
        second ∨
      (first = 0 ∧ second = 3) ∨ (first = 3 ∧ second = 0) ∨
      (first = 1 ∧ second = 4) ∨ (first = 4 ∧ second = 1) ∨
      (first = 2 ∧ second = 5) ∨ (first = 5 ∧ second = 2) := by
  rcases Data.Fin.Cases.finSix_cases first with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases Data.Fin.Cases.finSix_cases second with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- All six vertices in the order-six construction are pairwise distinct. -/
theorem hexagon_vertices_pairwise_ne
    (star : Regular.Basic.RegularStar K 6) (initialPoint : Geometry.Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Fin 6) (different : first ≠ second) :
    Construction.regularPolygonVertexAt star initialPoint first.val ≠
      Construction.regularPolygonVertexAt star initialPoint second.val := by
  rcases hexagon_index_classification first second with same | radial | opposite
  · exact False.elim (different same)
  · exact Construction.regularPolygonVertices_ne_of_radial_nonparallel star initialPoint
      initialContains initialDistinct first.val second.val
      (hexagon_radial_lines_nonparallel_of_normalized_ne star first second radial)
  · rcases opposite with zeroThree | threeZero | oneFour | fourOne |
      twoFive | fiveTwo
    · rcases zeroThree with ⟨rfl, rfl⟩
      exact hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 0 (by decide)
    · rcases threeZero with ⟨rfl, rfl⟩
      exact (hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 0 (by decide)).symm
    · rcases oneFour with ⟨rfl, rfl⟩
      exact hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 1 (by decide)
    · rcases fourOne with ⟨rfl, rfl⟩
      exact (hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 1 (by decide)).symm
    · rcases twoFive with ⟨rfl, rfl⟩
      exact hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 2 (by decide)
    · rcases fiveTwo with ⟨rfl, rfl⟩
      exact (hexagon_opposite_vertices_ne star initialPoint initialDistinct
        twoNonzero 2 (by decide)).symm

section

/-- Example 14.12: a finite order-six star constructs the regular hexagon `A₀ A₂ A₄ A₆ A₈ A₁₀`. -/
def example_14_12 (star : Regular.Basic.RegularStar K 6)
    (initialPoint : Geometry.Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0) :
    Regular.Basic.ConstructedRegularPolygon K 6 where
  star := star
  initialPoint := initialPoint
  initialContains := initialContains
  initialDistinct := initialDistinct
  pairwiseVertices := hexagon_vertices_pairwise_ne star initialPoint
    initialContains initialDistinct twoNonzero

end

end Purelib.Geometry.Polygons.Regular.Hexagon

end
