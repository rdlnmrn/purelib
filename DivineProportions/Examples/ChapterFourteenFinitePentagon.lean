import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Examples.ChapterFourteenPolygons
import DivineProportions.Examples.ChapterFourteen

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

namespace DivineProportions.ChapterFourteenExamples.ExerciseFourteenFive

/-- The executable nineteen-element coefficient field. -/
abbrev F := FieldNineteen.Element

/-- A labelled finite pentagon is exactly five displayed points. -/
abbrev Pentagon := Fin 5 → Point F

private theorem finFiveCases (index : Fin 5) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
  have values : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨
      index.val = 3 ∨ index.val = 4 := by omega0
  rcases values with zero | one | two | three | four
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext two)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext three))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext four))))

/-- The five central lines of Example 14.7, in slope order
`0,2,5,-5,-2`. -/
def radialLine (index : Fin 5) : Line F :=
  let slope : F := Fin.cases 0
    (Fin.cases 2 (Fin.cases 5 (Fin.cases (-5) (fun _ => -2)))) index
  { a := slope
    b := 1
    c := 0
    direction_nonzero := Or.inr (by decide) }

/-- Advance two places in the printed five-line order. -/
def advanceTwo : Fin 5 → Fin 5 :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 0 (fun _ => 1))))

/-- Starting at any radial line, the order `k,k+2,k+4,k+1,k+3` is again
the five-line reflection recurrence used by the printed pentagons. -/
def starInitial (start : Fin 5) : ReflectionPair F where
  previous := radialLine start
  current := radialLine (advanceTwo start)
  previousNonNull := by
    unfold radialLine Line.IsNull
    decide +revert
  currentNonNull := by
    unfold radialLine advanceTwo Line.IsNull
    decide +revert

/-- The concrete finite regular star beginning at any one of the five radial
lines.  All closure and nonparallel certificates are kernel computations in
the five requested representatives. -/
def finiteStar (start : Fin 5) : FiniteRegularStar F 5 where
  initial := starInitial start
  orderAtLeastTwo := by omega0
  pairwiseNonparallel := by
    intro first second different
    unfold Line.Parallel starInitial radialLine advanceTwo reflectionLineAt
      reflectionPairAt ReflectionPair.step reflectLine reflectedLineA
      reflectedLineB reflectedLineC lineNorm
    decide +revert
  closesAtOrder := by
    unfold Line.Equivalent starInitial radialLine advanceTwo reflectionLineAt
      reflectionPairAt ReflectionPair.step reflectLine reflectedLineA
      reflectedLineB reflectedLineC lineNorm
    decide +revert
  closesAfterOrder := by
    unfold Line.Equivalent starInitial radialLine advanceTwo reflectionLineAt
      reflectionPairAt ReflectionPair.step reflectLine reflectedLineA
      reflectedLineB reflectedLineC lineNorm
    decide +revert

/-- Every one of these five shifted stars has the printed center `O=[0,0]`. -/
theorem finiteStarCenter (start : Fin 5) :
    (finiteStar start).center = (⟨0, 0⟩ : Point F) := by
  apply Point.ext <;>
    unfold FiniteRegularStar.center finiteStar starInitial radialLine advanceTwo
      lineIntersection <;>
    decide +revert

/-- Assemble five literal points without a list or an indexing default. -/
def pentagon (p₀ p₁ p₂ p₃ p₄ : Point F) : Pentagon :=
  Fin.cases p₀
    (Fin.cases p₁ (Fin.cases p₂ (Fin.cases p₃ (fun _ => p₄))))

/-- The five points printed in Exercise 14.5. -/
def source : Pentagon :=
  pentagon ⟨2, -4⟩ ⟨1, 0⟩ ⟨2, 4⟩ ⟨7, -3⟩ ⟨7, 3⟩

/-- The complete finite diagonal-intersection orbit, including the source row
and the row reached after eighteen operations. -/
def orbit : Fin 19 → Pentagon := fun step =>
  match step.val with
  | 0 => pentagon ⟨2, 15⟩ ⟨1, 0⟩ ⟨2, 4⟩ ⟨7, 16⟩ ⟨7, 3⟩
  | 1 => pentagon ⟨2, 9⟩ ⟨6, 7⟩ ⟨3, 0⟩ ⟨6, 12⟩ ⟨2, 10⟩
  | 2 => pentagon ⟨6, 11⟩ ⟨6, 8⟩ ⟨18, 2⟩ ⟨9, 0⟩ ⟨18, 17⟩
  | 3 => pentagon ⟨16, 13⟩ ⟨18, 14⟩ ⟨18, 5⟩ ⟨16, 6⟩ ⟨8, 0⟩
  | 4 => pentagon ⟨5, 0⟩ ⟨10, 1⟩ ⟨16, 4⟩ ⟨16, 15⟩ ⟨10, 18⟩
  | 5 => pentagon ⟨11, 16⟩ ⟨15, 0⟩ ⟨11, 3⟩ ⟨10, 12⟩ ⟨10, 7⟩
  | 6 => pentagon ⟨11, 2⟩ ⟨14, 10⟩ ⟨7, 0⟩ ⟨14, 9⟩ ⟨11, 17⟩
  | 7 => pentagon ⟨14, 13⟩ ⟨14, 6⟩ ⟨4, 11⟩ ⟨2, 0⟩ ⟨4, 8⟩
  | 8 => pentagon ⟨12, 5⟩ ⟨4, 1⟩ ⟨4, 18⟩ ⟨12, 14⟩ ⟨6, 0⟩
  | 9 => pentagon ⟨18, 0⟩ ⟨17, 15⟩ ⟨12, 3⟩ ⟨12, 16⟩ ⟨17, 4⟩
  | 10 => pentagon ⟨13, 12⟩ ⟨16, 0⟩ ⟨13, 7⟩ ⟨17, 9⟩ ⟨17, 10⟩
  | 11 => pentagon ⟨13, 11⟩ ⟨1, 17⟩ ⟨10, 0⟩ ⟨1, 2⟩ ⟨13, 8⟩
  | 12 => pentagon ⟨1, 5⟩ ⟨1, 14⟩ ⟨3, 13⟩ ⟨11, 0⟩ ⟨3, 6⟩
  | 13 => pentagon ⟨9, 18⟩ ⟨3, 15⟩ ⟨3, 4⟩ ⟨9, 1⟩ ⟨14, 0⟩
  | 14 => pentagon ⟨4, 0⟩ ⟨8, 16⟩ ⟨9, 7⟩ ⟨9, 12⟩ ⟨8, 3⟩
  | 15 => pentagon ⟨5, 9⟩ ⟨12, 0⟩ ⟨5, 10⟩ ⟨8, 2⟩ ⟨8, 17⟩
  | 16 => pentagon ⟨5, 13⟩ ⟨15, 8⟩ ⟨17, 0⟩ ⟨15, 11⟩ ⟨5, 6⟩
  | 17 => pentagon ⟨15, 18⟩ ⟨15, 1⟩ ⟨7, 5⟩ ⟨13, 0⟩ ⟨7, 14⟩
  | _ => pentagon ⟨2, 4⟩ ⟨7, 16⟩ ⟨7, 3⟩ ⟨2, 15⟩ ⟨1, 0⟩

/-- Add a finite offset cyclically to a pentagon label. -/
def cyclic (index : Fin 5) (offset : Nat) : Fin 5 :=
  ⟨(index.val + offset) % 5, Nat.mod_lt _ (by decide)⟩

/-- Regard one of the eighteen transition labels as its current orbit row. -/
def currentStep (step : Fin 18) : Fin 19 := ⟨step.val, by omega0⟩

/-- The orbit row immediately after a transition label. -/
def followingStep (step : Fin 18) : Fin 19 := ⟨step.val + 1, by omega0⟩

/-- The first diagonal in the intersection that produces vertex `index` has
two distinct endpoints at every requested step. -/
theorem firstEndpointsDistinct (step : Fin 18) (index : Fin 5) :
    orbit (currentStep step) index ≠
      orbit (currentStep step) (cyclic index 2) := by
  decide +revert

/-- The second diagonal likewise has two distinct endpoints. -/
theorem secondEndpointsDistinct (step : Fin 18) (index : Fin 5) :
    orbit (currentStep step) (cyclic index 1) ≠
      orbit (currentStep step) (cyclic index 3) := by
  decide +revert

/-- The diagonal through vertices `i` and `i+2`. -/
def firstDiagonal (step : Fin 18) (index : Fin 5) : Line F :=
  lineThrough (orbit (currentStep step) index)
    (orbit (currentStep step) (cyclic index 2))
    (firstEndpointsDistinct step index)

/-- The diagonal through vertices `i+1` and `i+3`. -/
def secondDiagonal (step : Fin 18) (index : Fin 5) : Line F :=
  lineThrough (orbit (currentStep step) (cyclic index 1))
    (orbit (currentStep step) (cyclic index 3))
    (secondEndpointsDistinct step index)

/-- The two diagonals used at every orbit step are nonparallel. -/
theorem diagonalsNonparallel (step : Fin 18) (index : Fin 5) :
    ¬ (firstDiagonal step index).Parallel (secondDiagonal step index) := by
  unfold firstDiagonal secondDiagonal Line.Parallel lineThrough
  decide +revert

/-- The actual, denominator-certified intersection of the two diagonals. -/
def nextIntersection (step : Fin 18) (index : Fin 5) : Point F :=
  lineIntersection (firstDiagonal step index) (secondDiagonal step index)
    (diagonalsNonparallel step index)

/-- Every entry in the next orbit row is exactly the indicated diagonal
intersection in the current row. -/
theorem diagonalStep (step : Fin 18) (index : Fin 5) :
    nextIntersection step index = orbit (followingStep step) index := by
  apply Point.ext <;>
    unfold nextIntersection firstDiagonal secondDiagonal lineIntersection
      lineThrough orbit currentStep followingStep cyclic pentagon <;>
    decide +revert

/-- The computed next vertex lies on both of its defining diagonals. -/
theorem diagonalStepIncidences (step : Fin 18) (index : Fin 5) :
    (firstDiagonal step index).Contains (orbit (followingStep step) index) ∧
      (secondDiagonal step index).Contains
        (orbit (followingStep step) index) := by
  rw [← diagonalStep step index]
  exact ⟨lineIntersection_on_first _ _ _, lineIntersection_on_second _ _ _⟩

/-- After exactly eighteen operations the source pentagon is recovered with
the cyclic relabelling `i ↦ i+2`. -/
theorem recoveredAfterEighteen (index : Fin 5) :
    orbit 18 index = source (cyclic index 2) := by
  apply Point.ext <;>
    unfold orbit source cyclic pentagon <;>
    decide +revert

/-- The starting radial-line label for an orbit row. -/
def orbitStart (step : Fin 19) : Fin 5 :=
  ⟨(step.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- The first point of every displayed row lies on its starting radial line. -/
theorem orbitInitialContains (step : Fin 19) :
    (finiteStar (orbitStart step)).initial.previous.Contains (orbit step 0) := by
  unfold finiteStar starInitial radialLine orbitStart orbit pentagon Line.Contains
  decide +revert

/-- No displayed starting point is the common star center. -/
theorem orbitInitialDistinct (step : Fin 19) :
    orbit step 0 ≠ (finiteStar (orbitStart step)).center := by
  unfold FiniteRegularStar.center finiteStar starInitial radialLine orbitStart
    orbit pentagon lineIntersection
  decide +revert

/-- The regular-polygon package naturally associated with any orbit row. -/
def orbitPolygon (step : Fin 19) : ConstructedRegularPolygon F 5 :=
  ExampleFourteenEleven.example_14_11
    (finiteStar (orbitStart step)) (orbit step 0)
    (orbitInitialContains step) (orbitInitialDistinct step)

/-- Each packaged orbit polygon uses the printed origin as its center. -/
theorem orbitPolygonCenter (step : Fin 19) :
    (orbitPolygon step).star.center = (⟨0, 0⟩ : Point F) := by
  exact finiteStarCenter (orbitStart step)

/-- Radial-line label `start+2 index`, modulo five. -/
def radialIndex (start index : Fin 5) : Fin 5 :=
  ⟨(start.val + 2 * index.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- Each concrete radial line is non-null. -/
theorem radialLineNonNull (index : Fin 5) : ¬ (radialLine index).IsNull := by
  unfold radialLine Line.IsNull
  decide +revert

/-- The reflection recurrence starting with `starInitial start` visits the
five displayed radial lines in the `start+2 index` order. -/
theorem starLineEquivalent (start index : Fin 5) :
    (reflectionLineAt (starInitial start) index.val).Equivalent
      (radialLine (radialIndex start index)) := by
  unfold Line.Equivalent starInitial radialLine advanceTwo radialIndex
    reflectionLineAt reflectionPairAt ReflectionPair.step reflectLine
    reflectedLineA reflectedLineB reflectedLineC lineNorm
  decide +revert

private theorem sourceReflectedVertex (index : Fin 5) :
    reflectPoint (radialLine (radialIndex (orbitStart 0) index))
        (radialLineNonNull _) (orbit 0 0) = orbit 0 index := by
  rcases finFiveCases index with rfl | rfl | rfl | rfl | rfl
  · change (⟨2, 15⟩ : Point F) = ⟨2, 15⟩; rfl
  · change (⟨1, 0⟩ : Point F) = ⟨1, 0⟩; rfl
  · change (⟨2, 4⟩ : Point F) = ⟨2, 4⟩; rfl
  · change (⟨7, 16⟩ : Point F) = ⟨7, 16⟩; rfl
  · change (⟨7, 3⟩ : Point F) = ⟨7, 3⟩; rfl

private theorem firstDerivedReflectedVertex (index : Fin 5) :
    reflectPoint (radialLine (radialIndex (orbitStart 1) index))
        (radialLineNonNull _) (orbit 1 0) = orbit 1 index := by
  rcases finFiveCases index with rfl | rfl | rfl | rfl | rfl
  · change (⟨2, 9⟩ : Point F) = ⟨2, 9⟩; rfl
  · change (⟨6, 7⟩ : Point F) = ⟨6, 7⟩; rfl
  · change (⟨3, 0⟩ : Point F) = ⟨3, 0⟩; rfl
  · change (⟨6, 12⟩ : Point F) = ⟨6, 12⟩; rfl
  · change (⟨2, 10⟩ : Point F) = ⟨2, 10⟩; rfl

/-- The source's five printed points are precisely the vertices of the first
constructed regular pentagon. -/
theorem sourcePolygonVertices (index : Fin 5) :
    (orbitPolygon 0).vertex index = source index := by
  have sourceOrbit : orbit 0 index = source index := by
    apply Point.ext <;>
      unfold orbit source pentagon <;>
      decide +revert
  change reflectionPointAt (starInitial (orbitStart 0)) index.val
      (orbit 0 0) = source index
  calc
    reflectionPointAt (starInitial (orbitStart 0)) index.val (orbit 0 0) =
      reflectPoint (radialLine (radialIndex (orbitStart 0) index))
        (radialLineNonNull _) (orbit 0 0) :=
      reflectPoint_eq_of_equivalent
        (reflectionLineAt (starInitial (orbitStart 0)) index.val)
        (radialLine (radialIndex (orbitStart 0) index))
        (reflectionLineAt_nonNull _ _) (radialLineNonNull _)
        (starLineEquivalent _ _) (orbit 0 0)
    _ = orbit 0 index := sourceReflectedVertex index
    _ = source index := sourceOrbit

/-- The five intersections in the first derived row are precisely the
vertices of another constructed regular pentagon. -/
theorem firstDerivedPolygonVertices (index : Fin 5) :
    (orbitPolygon 1).vertex index = orbit 1 index := by
  change reflectionPointAt (starInitial (orbitStart 1)) index.val
      (orbit 1 0) = orbit 1 index
  calc
    reflectionPointAt (starInitial (orbitStart 1)) index.val (orbit 1 0) =
      reflectPoint (radialLine (radialIndex (orbitStart 1) index))
        (radialLineNonNull _) (orbit 1 0) :=
      reflectPoint_eq_of_equivalent
        (reflectionLineAt (starInitial (orbitStart 1)) index.val)
        (radialLine (radialIndex (orbitStart 1) index))
        (reflectionLineAt_nonNull _ _) (radialLineNonNull _)
        (starLineEquivalent _ _) (orbit 1 0)
    _ = orbit 1 index := firstDerivedReflectedVertex index

/-- Exercise 14.5: the printed points form a regular pentagon, their diagonal
intersections form another regular pentagon, eighteen certified iterations
are defined, and the last row recovers the first up to cyclic labelling. -/
theorem exercise_14_5 :
    (orbitPolygon 0).star.center = (⟨0, 0⟩ : Point F) ∧
      (∀ index : Fin 5, (orbitPolygon 0).vertex index = source index) ∧
      (∀ index : Fin 5, (orbitPolygon 1).vertex index = orbit 1 index) ∧
      (∀ step : Fin 18, ∀ index : Fin 5,
        nextIntersection step index = orbit (followingStep step) index) ∧
      (∀ index : Fin 5,
        orbit 18 index = source (cyclic index 2)) :=
  ⟨orbitPolygonCenter 0, sourcePolygonVertices, firstDerivedPolygonVertices,
    diagonalStep, recoveredAfterEighteen⟩

end DivineProportions.ChapterFourteenExamples.ExerciseFourteenFive
