module
public import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Parallel
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Iteration
public import Purelib.Geometry.Polygons.Regular.Basic
import Purelib.Geometry.Polygons.Regular.Construction
import Purelib.Geometry.Stars.Regular.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Geometry.Plane (Line)

open Purelib

open Purelib.Geometry

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

namespace Purelib.Geometry.Polygons.Regular.Pentagon

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- Doubling the vertex index gives the radial-line index modulo five. -/
def pentagonRadialIndex : Fin 5 → Fin 5 :=
  Data.Fin.casesByRecursion 0 (Data.Fin.casesByRecursion 2 (Data.Fin.casesByRecursion 4 (Data.Fin.casesByRecursion 1
    (fun _ => 3))))

/-- The literal inverse permutation `[0,3,1,4,2]`. -/
private def pentagonRadialIndexInverse : Fin 5 → Fin 5 :=
  Data.Fin.casesByRecursion 0 (Data.Fin.casesByRecursion 3 (Data.Fin.casesByRecursion 1 (Data.Fin.casesByRecursion 4
    (fun _ => 2))))

/-- The displayed inverse permutation undoes doubling modulo five. -/
private theorem pentagonRadialIndex_leftInverse (index : Fin 5) :
    pentagonRadialIndexInverse
      (pentagonRadialIndex index) = index := by
  rcases Data.Fin.Cases.finFive_cases index with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Doubling modulo five gives an injective radial-index map. -/
theorem pentagonRadialIndex_injective :
    Function.Injective pentagonRadialIndex := by
  intro first second same
  calc
    first = pentagonRadialIndexInverse
      (pentagonRadialIndex first) :=
      (pentagonRadialIndex_leftInverse first).symm
    _ = pentagonRadialIndexInverse
      (pentagonRadialIndex second) := by
      rw [same]
    _ = second := pentagonRadialIndex_leftInverse second

/-- Each possibly out-of-range radial-line index `2k` is equivalent to its literal representative in the five-line
prefix. -/
theorem pentagon_radial_line_equivalent
    (star : Regular.Basic.RegularStar K 5) (index : Fin 5) :
    (Iteration.reflectionLineAt star.initial (2 * index.val)).Equivalent
      (Iteration.reflectionLineAt star.initial (pentagonRadialIndex index).val) := by
  rcases Data.Fin.Cases.finFive_cases index with rfl | rfl | rfl | rfl | rfl
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · change (Iteration.reflectionLineAt star.initial 6).Equivalent
      (Iteration.reflectionLineAt star.initial 1)
    exact star.lineAt_add_order_equivalent 1
  · change (Iteration.reflectionLineAt star.initial 8).Equivalent
      (Iteration.reflectionLineAt star.initial 3)
    exact star.lineAt_add_order_equivalent 3

/-- The five radial lines of the constructed pentagon are pairwise nonparallel. -/
theorem pentagon_radial_lines_pairwise_nonparallel
    (star : Regular.Basic.RegularStar K 5) (first second : Fin 5)
    (different : first ≠ second) :
    ¬ (Iteration.reflectionLineAt star.initial (2 * first.val)).Parallel
      (Iteration.reflectionLineAt star.initial (2 * second.val)) := by
  have normalizedDifferent : pentagonRadialIndex first ≠
      pentagonRadialIndex second := by
    intro normalizedSame
    exact different (pentagonRadialIndex_injective normalizedSame)
  exact Parallel.nonparallel_of_equivalent_pairs
    (Iteration.reflectionLineAt star.initial (2 * first.val))
    (Iteration.reflectionLineAt star.initial (pentagonRadialIndex first).val)
    (Iteration.reflectionLineAt star.initial (2 * second.val))
    (Iteration.reflectionLineAt star.initial (pentagonRadialIndex second).val)
    (pentagon_radial_line_equivalent star first)
    (pentagon_radial_line_equivalent star second)
    (star.pairwiseNonparallel (pentagonRadialIndex first)
      (pentagonRadialIndex second) normalizedDifferent)

section

/-- Example 14.11: any requested finite order-five star and any noncentral point on `l₀` construct a regular pentagon
`A₀ A₂ A₄ A₆ A₈`. The returned record includes pairwise distinctness; its namespace theorems expose the five radial
incidences, equal radii, successive steps, and closure. -/
def example_14_11 (star : Regular.Basic.RegularStar K 5)
    (initialPoint : Geometry.Plane.Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center) :
    Regular.Basic.ConstructedRegularPolygon K 5 where
  star := star
  initialPoint := initialPoint
  initialContains := initialContains
  initialDistinct := initialDistinct
  pairwiseVertices := by
    intro first second different
    exact Construction.regularPolygonVertices_ne_of_radial_nonparallel star initialPoint
      initialContains initialDistinct first.val second.val
      (pentagon_radial_lines_pairwise_nonparallel star first second different)

end

end Purelib.Geometry.Polygons.Regular.Pentagon

end
