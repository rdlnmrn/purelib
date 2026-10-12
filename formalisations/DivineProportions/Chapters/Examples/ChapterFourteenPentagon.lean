module
import Purelib.Data.Fin
import Purelib.Algebra.Field.Finite.Nineteen
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Iteration.Point
import Purelib.Geometry.Plane.Reflection.Line
public import Purelib.Geometry.Polygons.Pentagon.Finite
import Purelib.Geometry.Polygons.Regular.Basic
public import Purelib.Geometry.Polygons.Regular.Pentagon
import Purelib.Geometry.Stars.Regular.Basic

import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Point
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin.Cases

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Exercise 14.5

The five printed points over `F₁₉` are presented as an actual constructed
regular pentagon.  Intersecting the five pairs of diagonals gives the next
pentagon in an explicit nineteen-row orbit.  Every one of the eighteen steps
uses two distinct endpoints and two nonparallel lines, so no division by zero
is hidden in the finite computation.  The eighteenth row is the original
pentagon with a cyclic relabelling.

Only the two regularity assertions made explicitly by the exercise are
packaged as `ConstructedRegularPolygon`s: the printed pentagon and its first
derived pentagon.  The remaining rows certify the requested repeated finite
operation, not an ambient enumeration of `F₁₉`.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFourteenPentagon

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line in
/-- The five central lines of Example 14.7, in slope order
`0,2,5,-5,-2`. -/
def radialLine (index : Fin 5) : Geometry.Plane.Line Nineteen.Element :=
  let slope : Nineteen.Element := Data.Fin.casesByRecursion 0
    (Data.Fin.casesByRecursion 2 (Data.Fin.casesByRecursion 5 (Data.Fin.casesByRecursion (-5) (fun _ => -2)))) index
  { a := slope
    b := 1
    c := 0
    direction_nonzero := Or.inr (by decide) }

/-- Advance two places in the printed five-line order. -/
def advanceTwo : Fin 5 → Fin 5 :=
  Data.Fin.casesByRecursion 2 (Data.Fin.casesByRecursion 3 (Data.Fin.casesByRecursion 4 (Data.Fin.casesByRecursion 0
    (fun _ => 1))))

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Plane.Reflection in
open formalisations.DivineProportions.Chapters.Examples in
/-- Starting at any radial line, the order `k,k+2,k+4,k+1,k+3` is again
the five-line reflection recurrence used by the printed pentagons. -/
def starInitial (start : Fin 5) : Iteration.ReflectionPair Nineteen.Element where
  previous := ChapterFourteenPentagon.radialLine start
  current := ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.advanceTwo start)
  previousNonNull := by
    unfold ChapterFourteenPentagon.radialLine Geometry.Plane.Line.IsNull
    decide +revert
  currentNonNull := by
    unfold ChapterFourteenPentagon.radialLine ChapterFourteenPentagon.advanceTwo Geometry.Plane.Line.IsNull
    decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Plane.Reflection in
open Purelib.Geometry.Plane.Reflection.Iteration in
open Purelib.Geometry.Stars.Regular in
open formalisations.DivineProportions.Chapters.Examples in
/-- The concrete finite regular star beginning at any one of the five radial
lines.  All closure and nonparallel certificates are kernel computations in
the five requested representatives. -/
def star (start : Fin 5) : Basic.RegularStar Nineteen.Element 5 where
  initial := ChapterFourteenPentagon.starInitial start
  orderAtLeastTwo := by omega0
  pairwiseNonparallel := by
    intro first second different
    unfold Geometry.Plane.Line.Parallel ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
      ChapterFourteenPentagon.advanceTwo Iteration.reflectionLineAt
      Iteration.reflectionPairAt ReflectionPair.step Line.reflectLine Line.reflectedLineA
      Line.reflectedLineB Line.reflectedLineC Basic.lineNorm
    decide +revert
  closesAtOrder := by
    unfold Geometry.Plane.Line.Equivalent ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
      ChapterFourteenPentagon.advanceTwo Iteration.reflectionLineAt
      Iteration.reflectionPairAt ReflectionPair.step Line.reflectLine Line.reflectedLineA
      Line.reflectedLineB Line.reflectedLineC Basic.lineNorm
    decide +revert
  closesAfterOrder := by
    unfold Geometry.Plane.Line.Equivalent ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
      ChapterFourteenPentagon.advanceTwo Iteration.reflectionLineAt
      Iteration.reflectionPairAt ReflectionPair.step Line.reflectLine Line.reflectedLineA
      Line.reflectedLineB Line.reflectedLineC Basic.lineNorm
    decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Basic in
open Purelib.Geometry.Stars.Regular.Basic in
open formalisations.DivineProportions.Chapters.Examples in
/-- Every one of these five shifted stars has the printed center `O=[0,0]`. -/
theorem starCenter (start : Fin 5) :
    (star start).center = (⟨0, 0⟩ : Geometry.Plane.Point Nineteen.Element) := by
  apply Geometry.Plane.Point.ext <;>
    unfold RegularStar.center star ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
      ChapterFourteenPentagon.advanceTwo
      Intersection.lineIntersection <;>
    decide +revert

section
open Purelib.Geometry.Polygons.Pentagon
/-- The five points printed in Exercise 14.5. -/
def source : Geometry.Polygons.Pentagon :=
  Finite.pentagon ⟨2, -4⟩ ⟨1, 0⟩ ⟨2, 4⟩ ⟨7, -3⟩ ⟨7, 3⟩

/-- The complete finite diagonal-intersection orbit, including the source row
and the row reached after eighteen operations. -/
def orbit : Fin 19 → Geometry.Polygons.Pentagon := fun step =>
  match step.val with
  | 0 => Finite.pentagon ⟨2, 15⟩ ⟨1, 0⟩ ⟨2, 4⟩ ⟨7, 16⟩ ⟨7, 3⟩
  | 1 => Finite.pentagon ⟨2, 9⟩ ⟨6, 7⟩ ⟨3, 0⟩ ⟨6, 12⟩ ⟨2, 10⟩
  | 2 => Finite.pentagon ⟨6, 11⟩ ⟨6, 8⟩ ⟨18, 2⟩ ⟨9, 0⟩ ⟨18, 17⟩
  | 3 => Finite.pentagon ⟨16, 13⟩ ⟨18, 14⟩ ⟨18, 5⟩ ⟨16, 6⟩ ⟨8, 0⟩
  | 4 => Finite.pentagon ⟨5, 0⟩ ⟨10, 1⟩ ⟨16, 4⟩ ⟨16, 15⟩ ⟨10, 18⟩
  | 5 => Finite.pentagon ⟨11, 16⟩ ⟨15, 0⟩ ⟨11, 3⟩ ⟨10, 12⟩ ⟨10, 7⟩
  | 6 => Finite.pentagon ⟨11, 2⟩ ⟨14, 10⟩ ⟨7, 0⟩ ⟨14, 9⟩ ⟨11, 17⟩
  | 7 => Finite.pentagon ⟨14, 13⟩ ⟨14, 6⟩ ⟨4, 11⟩ ⟨2, 0⟩ ⟨4, 8⟩
  | 8 => Finite.pentagon ⟨12, 5⟩ ⟨4, 1⟩ ⟨4, 18⟩ ⟨12, 14⟩ ⟨6, 0⟩
  | 9 => Finite.pentagon ⟨18, 0⟩ ⟨17, 15⟩ ⟨12, 3⟩ ⟨12, 16⟩ ⟨17, 4⟩
  | 10 => Finite.pentagon ⟨13, 12⟩ ⟨16, 0⟩ ⟨13, 7⟩ ⟨17, 9⟩ ⟨17, 10⟩
  | 11 => Finite.pentagon ⟨13, 11⟩ ⟨1, 17⟩ ⟨10, 0⟩ ⟨1, 2⟩ ⟨13, 8⟩
  | 12 => Finite.pentagon ⟨1, 5⟩ ⟨1, 14⟩ ⟨3, 13⟩ ⟨11, 0⟩ ⟨3, 6⟩
  | 13 => Finite.pentagon ⟨9, 18⟩ ⟨3, 15⟩ ⟨3, 4⟩ ⟨9, 1⟩ ⟨14, 0⟩
  | 14 => Finite.pentagon ⟨4, 0⟩ ⟨8, 16⟩ ⟨9, 7⟩ ⟨9, 12⟩ ⟨8, 3⟩
  | 15 => Finite.pentagon ⟨5, 9⟩ ⟨12, 0⟩ ⟨5, 10⟩ ⟨8, 2⟩ ⟨8, 17⟩
  | 16 => Finite.pentagon ⟨5, 13⟩ ⟨15, 8⟩ ⟨17, 0⟩ ⟨15, 11⟩ ⟨5, 6⟩
  | 17 => Finite.pentagon ⟨15, 18⟩ ⟨15, 1⟩ ⟨7, 5⟩ ⟨13, 0⟩ ⟨7, 14⟩
  | _ => Finite.pentagon ⟨2, 4⟩ ⟨7, 16⟩ ⟨7, 3⟩ ⟨2, 15⟩ ⟨1, 0⟩

end

/-- Regard one of the eighteen transition labels as its current orbit row. -/
def currentStep (step : Fin 18) : Fin 19 := ⟨step.val, by omega0⟩

/-- The orbit row immediately after a transition label. -/
def followingStep (step : Fin 18) : Fin 19 := ⟨step.val + 1, by omega0⟩

section
open Purelib.Geometry.Polygons.Pentagon
open formalisations.DivineProportions.Chapters.Examples
/-- The first diagonal in the intersection that produces vertex `index` has
two distinct endpoints at every requested step. -/
theorem firstEndpointsDistinct (step : Fin 18) (index : Fin 5) :
    ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) index ≠
      ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index 2) := by
  decide +revert

/-- The second diagonal likewise has two distinct endpoints. -/
theorem secondEndpointsDistinct (step : Fin 18) (index : Fin 5) :
    ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index 1) ≠
      ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index 3) := by
  decide +revert

end

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Polygons.Pentagon
open formalisations.DivineProportions.Chapters.Examples
/-- The diagonal through vertices `i` and `i+2`. -/
def firstDiagonal (step : Fin 18) (index : Fin 5) : Geometry.Plane.Line Nineteen.Element :=
  Incidence.lineThrough (ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) index)
    (ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index 2))
    (ChapterFourteenPentagon.firstEndpointsDistinct step index)

/-- The diagonal through vertices `i+1` and `i+3`. -/
def secondDiagonal (step : Fin 18) (index : Fin 5) : Geometry.Plane.Line Nineteen.Element :=
  Incidence.lineThrough (ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index
    1))
    (ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.currentStep step) (Finite.cyclic index 3))
    (ChapterFourteenPentagon.secondEndpointsDistinct step index)

end

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Line.Basic in
open formalisations.DivineProportions.Chapters.Examples in
/-- The two diagonals used at every orbit step are nonparallel. -/
theorem diagonalsNonparallel (step : Fin 18) (index : Fin 5) :
    ¬ (ChapterFourteenPentagon.firstDiagonal step index).Parallel (ChapterFourteenPentagon.secondDiagonal step index) :=
      by
  unfold ChapterFourteenPentagon.firstDiagonal ChapterFourteenPentagon.secondDiagonal Geometry.Plane.Line.Parallel
    Incidence.lineThrough
  decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Point in
open formalisations.DivineProportions.Chapters.Examples in
/-- The actual, denominator-certified intersection of the two diagonals. -/
def nextIntersection (step : Fin 18) (index : Fin 5) : Geometry.Plane.Point Nineteen.Element :=
  Intersection.lineIntersection (ChapterFourteenPentagon.firstDiagonal step index)
    (ChapterFourteenPentagon.secondDiagonal step index)
    (ChapterFourteenPentagon.diagonalsNonparallel step index)

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Point.Basic in
open Purelib.Geometry.Polygons.Pentagon in
open formalisations.DivineProportions.Chapters.Examples in
/-- Every entry in the next orbit row is exactly the indicated diagonal
intersection in the current row. -/
theorem diagonalStep (step : Fin 18) (index : Fin 5) :
    ChapterFourteenPentagon.nextIntersection step index = ChapterFourteenPentagon.orbit
      (ChapterFourteenPentagon.followingStep step) index := by
  apply Geometry.Plane.Point.ext <;>
    unfold ChapterFourteenPentagon.nextIntersection ChapterFourteenPentagon.firstDiagonal
      ChapterFourteenPentagon.secondDiagonal Intersection.lineIntersection
      Incidence.lineThrough ChapterFourteenPentagon.orbit ChapterFourteenPentagon.currentStep
        ChapterFourteenPentagon.followingStep Finite.cyclic Finite.pentagon <;>
    decide +revert

open Purelib.Geometry.Plane.Line in
open formalisations.DivineProportions.Chapters.Examples in
/-- The computed next vertex lies on both of its defining diagonals. -/
theorem diagonalStepIncidences (step : Fin 18) (index : Fin 5) :
    (ChapterFourteenPentagon.firstDiagonal step index).Contains (ChapterFourteenPentagon.orbit
      (ChapterFourteenPentagon.followingStep step) index) ∧
      (ChapterFourteenPentagon.secondDiagonal step index).Contains
        (ChapterFourteenPentagon.orbit (ChapterFourteenPentagon.followingStep step) index) := by
  rw [← ChapterFourteenPentagon.diagonalStep step index]
  exact ⟨Intersection.lineIntersection_on_first _ _ _, Intersection.lineIntersection_on_second _ _ _⟩

open Purelib.Geometry.Plane.Point.Basic in
open Purelib.Geometry.Polygons.Pentagon in
open formalisations.DivineProportions.Chapters.Examples in
/-- After exactly eighteen operations the source pentagon is recovered with
the cyclic relabelling `i ↦ i+2`. -/
theorem recoveredAfterEighteen (index : Fin 5) :
    ChapterFourteenPentagon.orbit 18 index = ChapterFourteenPentagon.source (Finite.cyclic index 2) := by
  apply Geometry.Plane.Point.ext <;>
    unfold ChapterFourteenPentagon.orbit ChapterFourteenPentagon.source Finite.cyclic Finite.pentagon <;>
    decide +revert

/-- The starting radial-line label for an orbit row. -/
def orbitStart (step : Fin 19) : Fin 5 :=
  ⟨(step.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Polygons.Pentagon in
open formalisations.DivineProportions.Chapters.Examples in
/-- The first point of every displayed row lies on its starting radial line. -/
theorem orbitInitialContains (step : Fin 19) :
    (star (ChapterFourteenPentagon.orbitStart step)).initial.previous.Contains (ChapterFourteenPentagon.orbit step 0) :=
      by
  unfold star ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine ChapterFourteenPentagon.orbitStart
    ChapterFourteenPentagon.orbit Finite.pentagon Geometry.Plane.Line.Contains
  decide +revert

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Polygons.Pentagon in
open Purelib.Geometry.Stars.Regular.Basic in
open formalisations.DivineProportions.Chapters.Examples in
/-- No displayed starting point is the common star center. -/
theorem orbitInitialDistinct (step : Fin 19) :
    ChapterFourteenPentagon.orbit step 0 ≠ (star (ChapterFourteenPentagon.orbitStart step)).center := by
  unfold RegularStar.center star ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
    ChapterFourteenPentagon.orbitStart
    ChapterFourteenPentagon.orbit Finite.pentagon Intersection.lineIntersection
  decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Polygons.Regular in
open formalisations.DivineProportions.Chapters.Examples in
/-- The regular-polygon package naturally associated with any orbit row. -/
def orbitPolygon (step : Fin 19) : Basic.ConstructedRegularPolygon Nineteen.Element 5 :=
  Pentagon.example_14_11
    (star (ChapterFourteenPentagon.orbitStart step)) (ChapterFourteenPentagon.orbit step 0)
    (ChapterFourteenPentagon.orbitInitialContains step) (ChapterFourteenPentagon.orbitInitialDistinct step)

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
open formalisations.DivineProportions.Chapters.Examples in
/-- Each packaged orbit polygon uses the printed origin as its center. -/
theorem orbitPolygonCenter (step : Fin 19) :
    (ChapterFourteenPentagon.orbitPolygon step).star.center = (⟨0, 0⟩ : Geometry.Plane.Point Nineteen.Element) := by
  exact ChapterFourteenPentagon.starCenter (ChapterFourteenPentagon.orbitStart step)

/-- Radial-line label `start+2 index`, modulo five. -/
def radialIndex (start index : Fin 5) : Fin 5 :=
  ⟨(start.val + 2 * index.val) % 5, Nat.mod_lt _ (by decide)⟩

open Purelib.Geometry.Plane.Line.Basic in
open formalisations.DivineProportions.Chapters.Examples in
/-- Each concrete radial line is non-null. -/
theorem radialLineNonNull (index : Fin 5) : ¬ (ChapterFourteenPentagon.radialLine index).IsNull := by
  unfold ChapterFourteenPentagon.radialLine Geometry.Plane.Line.IsNull
  decide +revert

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Plane.Reflection in
open Purelib.Geometry.Plane.Reflection.Iteration in
open formalisations.DivineProportions.Chapters.Examples in
/-- The reflection recurrence starting with `starInitial start` visits the
five displayed radial lines in the `start+2 index` order. -/
theorem starLineEquivalent (start index : Fin 5) :
    (Iteration.reflectionLineAt (ChapterFourteenPentagon.starInitial start) index.val).Equivalent
      (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex start index)) := by
  unfold Geometry.Plane.Line.Equivalent ChapterFourteenPentagon.starInitial ChapterFourteenPentagon.radialLine
    ChapterFourteenPentagon.advanceTwo ChapterFourteenPentagon.radialIndex
    Iteration.reflectionLineAt Iteration.reflectionPairAt ReflectionPair.step Line.reflectLine
    Line.reflectedLineA Line.reflectedLineB Line.reflectedLineC Basic.lineNorm
  decide +revert

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Reflection
open formalisations.DivineProportions.Chapters.Examples
open Purelib
/-- Reflecting the first source vertex in the indexed radial line gives the corresponding source vertex. -/
private theorem sourceReflectedVertex (index : Fin 5) :
    Point.reflectPoint (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex
      (ChapterFourteenPentagon.orbitStart 0) index))
        (ChapterFourteenPentagon.radialLineNonNull _) (ChapterFourteenPentagon.orbit 0 0) =
          ChapterFourteenPentagon.orbit 0 index := by
  rcases Data.Fin.Cases.finFiveCases index with rfl | rfl | rfl | rfl | rfl
  · change (⟨2, 15⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨2, 15⟩; rfl
  · change (⟨1, 0⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨1, 0⟩; rfl
  · change (⟨2, 4⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨2, 4⟩; rfl
  · change (⟨7, 16⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨7, 16⟩; rfl
  · change (⟨7, 3⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨7, 3⟩; rfl

/-- Reflecting the first derived vertex in the indexed radial line gives the corresponding derived vertex. -/
private theorem firstDerivedReflectedVertex (index : Fin 5) :
    Point.reflectPoint (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex
      (ChapterFourteenPentagon.orbitStart 1) index))
        (ChapterFourteenPentagon.radialLineNonNull _) (ChapterFourteenPentagon.orbit 1 0) =
          ChapterFourteenPentagon.orbit 1 index := by
  rcases Data.Fin.Cases.finFiveCases index with rfl | rfl | rfl | rfl | rfl
  · change (⟨2, 9⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨2, 9⟩; rfl
  · change (⟨6, 7⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨6, 7⟩; rfl
  · change (⟨3, 0⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨3, 0⟩; rfl
  · change (⟨6, 12⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨6, 12⟩; rfl
  · change (⟨2, 10⟩ : Geometry.Plane.Point Nineteen.Element) = ⟨2, 10⟩; rfl

end

open Purelib.Geometry.Plane.Point.Basic in
open Purelib.Geometry.Plane.Reflection in
open Purelib.Geometry.Plane.Reflection.Iteration in
open Purelib.Geometry.Polygons.Pentagon in
open formalisations.DivineProportions.Chapters.Examples in
/-- The source's five printed points are precisely the vertices of the first
constructed regular pentagon. -/
theorem sourcePolygonVertices (index : Fin 5) :
    (ChapterFourteenPentagon.orbitPolygon 0).vertex index = ChapterFourteenPentagon.source index := by
  have sourceOrbit : ChapterFourteenPentagon.orbit 0 index = ChapterFourteenPentagon.source index := by
    apply Geometry.Plane.Point.ext <;>
      unfold ChapterFourteenPentagon.orbit ChapterFourteenPentagon.source Finite.pentagon <;>
      decide +revert
  change Point.reflectionPointAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 0)) index.val
      (ChapterFourteenPentagon.orbit 0 0) = ChapterFourteenPentagon.source index
  calc
    Point.reflectionPointAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 0)) index.val
      (ChapterFourteenPentagon.orbit 0 0) =
      Point.reflectPoint (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex
        (ChapterFourteenPentagon.orbitStart 0) index))
        (ChapterFourteenPentagon.radialLineNonNull _) (ChapterFourteenPentagon.orbit 0 0) :=
      Point.reflectPoint_eq_of_equivalent
        (Iteration.reflectionLineAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 0))
          index.val)
        (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex (ChapterFourteenPentagon.orbitStart 0)
          index))
        (Iteration.reflectionLineAt_nonNull _ _) (ChapterFourteenPentagon.radialLineNonNull _)
        (ChapterFourteenPentagon.starLineEquivalent _ _) (ChapterFourteenPentagon.orbit 0 0)
    _ = ChapterFourteenPentagon.orbit 0 index := ChapterFourteenPentagon.sourceReflectedVertex index
    _ = ChapterFourteenPentagon.source index := sourceOrbit

open Purelib.Geometry.Plane.Reflection in
open Purelib.Geometry.Plane.Reflection.Iteration in
open formalisations.DivineProportions.Chapters.Examples in
/-- The five intersections in the first derived row are precisely the
vertices of another constructed regular pentagon. -/
theorem firstDerivedPolygonVertices (index : Fin 5) :
    (ChapterFourteenPentagon.orbitPolygon 1).vertex index = ChapterFourteenPentagon.orbit 1 index := by
  change Point.reflectionPointAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 1)) index.val
      (ChapterFourteenPentagon.orbit 1 0) = ChapterFourteenPentagon.orbit 1 index
  calc
    Point.reflectionPointAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 1)) index.val
      (ChapterFourteenPentagon.orbit 1 0) =
      Point.reflectPoint (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex
        (ChapterFourteenPentagon.orbitStart 1) index))
        (ChapterFourteenPentagon.radialLineNonNull _) (ChapterFourteenPentagon.orbit 1 0) :=
      Point.reflectPoint_eq_of_equivalent
        (Iteration.reflectionLineAt (ChapterFourteenPentagon.starInitial (ChapterFourteenPentagon.orbitStart 1))
          index.val)
        (ChapterFourteenPentagon.radialLine (ChapterFourteenPentagon.radialIndex (ChapterFourteenPentagon.orbitStart 1)
          index))
        (Iteration.reflectionLineAt_nonNull _ _) (ChapterFourteenPentagon.radialLineNonNull _)
        (ChapterFourteenPentagon.starLineEquivalent _ _) (ChapterFourteenPentagon.orbit 1 0)
    _ = ChapterFourteenPentagon.orbit 1 index := ChapterFourteenPentagon.firstDerivedReflectedVertex index

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Polygons.Pentagon in
open formalisations.DivineProportions.Chapters.Examples in
/-- Exercise 14.5: the printed points form a regular pentagon, their diagonal
intersections form another regular pentagon, eighteen certified iterations
are defined, and the last row recovers the first up to cyclic labelling. -/
theorem exercise_14_5 :
    (ChapterFourteenPentagon.orbitPolygon 0).star.center = (⟨0, 0⟩ : Geometry.Plane.Point Nineteen.Element) ∧
      (∀ index : Fin 5, (ChapterFourteenPentagon.orbitPolygon 0).vertex index = ChapterFourteenPentagon.source index) ∧
      (∀ index : Fin 5, (ChapterFourteenPentagon.orbitPolygon 1).vertex index = ChapterFourteenPentagon.orbit 1 index) ∧
      (∀ step : Fin 18, ∀ index : Fin 5,
        ChapterFourteenPentagon.nextIntersection step index = ChapterFourteenPentagon.orbit
          (ChapterFourteenPentagon.followingStep step) index) ∧
      (∀ index : Fin 5,
        ChapterFourteenPentagon.orbit 18 index = ChapterFourteenPentagon.source (Finite.cyclic index 2)) :=
  ⟨ChapterFourteenPentagon.orbitPolygonCenter 0, ChapterFourteenPentagon.sourcePolygonVertices,
    ChapterFourteenPentagon.firstDerivedPolygonVertices,
    ChapterFourteenPentagon.diagonalStep, ChapterFourteenPentagon.recoveredAfterEighteen⟩

end formalisations.DivineProportions.Chapters.Examples.ChapterFourteenPentagon

end
