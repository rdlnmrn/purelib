import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Polygons.RegularConstruction

/-!
# Divine Proportions, Examples 14.11 and 14.12

The pentagon and hexagon are represented by five and six executable vertices.
The generic construction proves their radial incidences, equal radii,
successive-reflection equations, and closure.  This file supplies the two
finite distinctness arguments from the source: doubling permutes the five
radial lines, while the three opposite hexagon pairs use perpendicular
mirrors and central rotation.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] [DecidableEq K] in
private theorem nonparallel_of_equivalent_pairs
    (actualFirst displayedFirst actualSecond displayedSecond : Line K)
    (firstEquivalent : actualFirst.Equivalent displayedFirst)
    (secondEquivalent : actualSecond.Equivalent displayedSecond)
    (displayedNonparallel : ¬ displayedFirst.Parallel displayedSecond) :
    ¬ actualFirst.Parallel actualSecond := by
  intro actualParallel
  apply displayedNonparallel
  exact line_parallel_trans
    (Line.parallel_symm (line_parallel_of_equivalent firstEquivalent))
    (line_parallel_trans actualParallel
      (line_parallel_of_equivalent secondEquivalent))

private theorem finFive_cases (index : Fin 5) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
  have values : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨
      index.val = 3 ∨ index.val = 4 := by omega0
  rcases values with zero | one | two | three | four
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext two)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext three))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext four))))

/-- Doubling the vertex index gives the radial-line index modulo five. -/
def pentagonRadialIndex : Fin 5 → Fin 5 :=
  Fin.cases 0 (Fin.cases 2 (Fin.cases 4 (Fin.cases 1 (fun _ => 3))))

/-- The literal inverse permutation `[0,3,1,4,2]`. -/
private def pentagonRadialIndexInverse : Fin 5 → Fin 5 :=
  Fin.cases 0 (Fin.cases 3 (Fin.cases 1 (Fin.cases 4 (fun _ => 2))))

private theorem pentagonRadialIndex_leftInverse (index : Fin 5) :
    pentagonRadialIndexInverse (pentagonRadialIndex index) = index := by
  rcases finFive_cases index with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pentagonRadialIndex_injective :
    Function.Injective pentagonRadialIndex := by
  intro first second same
  calc
    first = pentagonRadialIndexInverse (pentagonRadialIndex first) :=
      (pentagonRadialIndex_leftInverse first).symm
    _ = pentagonRadialIndexInverse (pentagonRadialIndex second) := by rw [same]
    _ = second := pentagonRadialIndex_leftInverse second

/-- Each possibly out-of-range radial-line index `2k` is equivalent to its
literal representative in the five-line prefix. -/
theorem pentagon_radial_line_equivalent
    (star : FiniteRegularStar K 5) (index : Fin 5) :
    (reflectionLineAt star.initial (2 * index.val)).Equivalent
      (reflectionLineAt star.initial (pentagonRadialIndex index).val) := by
  rcases finFive_cases index with rfl | rfl | rfl | rfl | rfl
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · change (reflectionLineAt star.initial 6).Equivalent
      (reflectionLineAt star.initial 1)
    exact star.lineAt_add_order_equivalent 1
  · change (reflectionLineAt star.initial 8).Equivalent
      (reflectionLineAt star.initial 3)
    exact star.lineAt_add_order_equivalent 3

/-- The five radial lines of the constructed pentagon are pairwise
nonparallel. -/
theorem pentagon_radial_lines_pairwise_nonparallel
    (star : FiniteRegularStar K 5) (first second : Fin 5)
    (different : first ≠ second) :
    ¬ (reflectionLineAt star.initial (2 * first.val)).Parallel
      (reflectionLineAt star.initial (2 * second.val)) := by
  have normalizedDifferent : pentagonRadialIndex first ≠
      pentagonRadialIndex second := by
    intro normalizedSame
    exact different (pentagonRadialIndex_injective normalizedSame)
  exact nonparallel_of_equivalent_pairs
    (reflectionLineAt star.initial (2 * first.val))
    (reflectionLineAt star.initial (pentagonRadialIndex first).val)
    (reflectionLineAt star.initial (2 * second.val))
    (reflectionLineAt star.initial (pentagonRadialIndex second).val)
    (pentagon_radial_line_equivalent star first)
    (pentagon_radial_line_equivalent star second)
    (star.pairwiseNonparallel (pentagonRadialIndex first)
      (pentagonRadialIndex second) normalizedDifferent)

namespace ChapterFourteenExamples.ExampleFourteenEleven

/-- Example 14.11: any requested finite order-five star and any noncentral
point on `l₀` construct a regular pentagon `A₀ A₂ A₄ A₆ A₈`.  The returned
record includes pairwise distinctness; its namespace theorems expose the
five radial incidences, equal radii, successive steps, and closure. -/
def example_14_11 (star : FiniteRegularStar K 5)
    (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center) :
    ConstructedRegularPolygon K 5 where
  star := star
  initialPoint := initialPoint
  initialContains := initialContains
  initialDistinct := initialDistinct
  pairwiseVertices := by
    intro first second different
    exact regularPolygonVertices_ne_of_radial_nonparallel star initialPoint
      initialContains initialDistinct first.val second.val
      (pentagon_radial_lines_pairwise_nonparallel star first second different)

end ChapterFourteenExamples.ExampleFourteenEleven

private theorem finSix_cases (index : Fin 6) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 := by
  have values : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨
      index.val = 3 ∨ index.val = 4 ∨ index.val = 5 := by omega0
  rcases values with zero | one | two | three | four | five
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext two)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext three))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext four)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext five)))))

/-- The six radial line labels are `0,2,4,0,2,4`. -/
def hexagonRadialIndex : Fin 6 → Fin 6 :=
  Fin.cases 0
    (Fin.cases 2
      (Fin.cases 4
        (Fin.cases 0 (Fin.cases 2 (fun _ => 4)))))

/-- Normalize the six displayed radial lines into the finite star prefix. -/
theorem hexagon_radial_line_equivalent
    (star : FiniteRegularStar K 6) (index : Fin 6) :
    (reflectionLineAt star.initial (2 * index.val)).Equivalent
      (reflectionLineAt star.initial (hexagonRadialIndex index).val) := by
  rcases finSix_cases index with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · exact Line.equivalent_refl _
  · change (reflectionLineAt star.initial 6).Equivalent
      (reflectionLineAt star.initial 0)
    simpa only [reflectionLineAt_zero] using star.closesAtOrder
  · change (reflectionLineAt star.initial 8).Equivalent
      (reflectionLineAt star.initial 2)
    exact star.lineAt_add_order_equivalent 2
  · change (reflectionLineAt star.initial 10).Equivalent
      (reflectionLineAt star.initial 4)
    exact star.lineAt_add_order_equivalent 4

theorem hexagon_radial_lines_nonparallel_of_normalized_ne
    (star : FiniteRegularStar K 6) (first second : Fin 6)
    (normalizedDifferent : hexagonRadialIndex first ≠
      hexagonRadialIndex second) :
    ¬ (reflectionLineAt star.initial (2 * first.val)).Parallel
      (reflectionLineAt star.initial (2 * second.val)) := by
  exact nonparallel_of_equivalent_pairs
    (reflectionLineAt star.initial (2 * first.val))
    (reflectionLineAt star.initial (hexagonRadialIndex first).val)
    (reflectionLineAt star.initial (2 * second.val))
    (reflectionLineAt star.initial (hexagonRadialIndex second).val)
    (hexagon_radial_line_equivalent star first)
    (hexagon_radial_line_equivalent star second)
    (star.pairwiseNonparallel (hexagonRadialIndex first)
      (hexagonRadialIndex second) normalizedDifferent)

/-- In an order-six star, `lₖ` and `lₖ₊₃` are perpendicular for each of the
three requested values `k=0,1,2`. -/
theorem hexagon_opposite_lines_perpendicular
    (star : FiniteRegularStar K 6) (twoNonzero : (2 : K) ≠ 0)
    (first : Nat) (firstBelowThree : first < 3) :
    (reflectionLineAt star.initial first).Perpendicular
      (reflectionLineAt star.initial (first + 3)) := by
  have reflectedEquivalent := cyclic_reflection_left star.initial 3 first
  have periodicEquivalent := star.lineAt_add_order_equivalent first
  have fixedEquivalent :
      (reflectLine (reflectionLineAt star.initial (first + 3))
        (reflectionLineAt star.initial first)
        (reflectionLineAt_nonNull star.initial (first + 3))).Equivalent
          (reflectionLineAt star.initial first) := by
    exact line_equivalent_trans (by
      simpa only [show first + 2 * 3 = first + 6 by omega0] using
        reflectedEquivalent) periodicEquivalent
  have fixedDirection :
      (reflectionLineAt star.initial first).Parallel
        (reflectLine (reflectionLineAt star.initial (first + 3))
          (reflectionLineAt star.initial first)
          (reflectionLineAt_nonNull star.initial (first + 3))) :=
    Line.parallel_symm (line_parallel_of_equivalent fixedEquivalent)
  have alternatives := parallel_or_perpendicular_of_parallel_reflectLine
    (reflectionLineAt star.initial (first + 3))
    (reflectionLineAt star.initial first)
    (reflectionLineAt_nonNull star.initial (first + 3))
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

/-- Opposite constructed hexagon vertices are distinct: equality would make
the noncentral initial point fixed by rotation in the star center. -/
theorem hexagon_opposite_vertices_ne
    (star : FiniteRegularStar K 6) (initialPoint : Point K)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0)
    (first : Nat) (firstBelowThree : first < 3) :
    regularPolygonVertexAt star initialPoint first ≠
      regularPolygonVertexAt star initialPoint (first + 3) := by
  intro verticesEqual
  have composedFixed :
      reflectionPointAt star.initial (first + 3)
          (reflectionPointAt star.initial first initialPoint) = initialPoint := by
    calc
      reflectionPointAt star.initial (first + 3)
          (reflectionPointAt star.initial first initialPoint) =
        reflectionPointAt star.initial (first + 3)
          (reflectionPointAt star.initial (first + 3) initialPoint) := by
            exact congrArg (reflectionPointAt star.initial (first + 3))
              verticesEqual
      _ = initialPoint := reflectionPointAt_involutive star.initial
        (first + 3) initialPoint
  have compositionIsRotation := reflectPoint_perpendicular_comp_eq_rotate
    (reflectionLineAt star.initial first)
    (reflectionLineAt star.initial (first + 3))
    (reflectionLineAt_nonNull star.initial first)
    (reflectionLineAt_nonNull star.initial (first + 3))
    (hexagon_opposite_lines_perpendicular star twoNonzero first
      firstBelowThree)
    star.center (star.lineAt_contains_center first)
    (star.lineAt_contains_center (first + 3)) initialPoint
  have rotationFixed : rotateInPoint star.center initialPoint = initialPoint :=
    compositionIsRotation.symm.trans composedFixed
  exact initialDistinct
    ((rotateInPoint_fixed_iff_center star.center initialPoint twoNonzero).1
      rotationFixed)

/-- Complete finite classification of two hexagon indices: they are equal,
their radial labels differ, or they form one of the three opposite pairs. -/
private theorem hexagon_index_classification (first second : Fin 6) :
    first = second ∨
      hexagonRadialIndex first ≠ hexagonRadialIndex second ∨
      (first = 0 ∧ second = 3) ∨ (first = 3 ∧ second = 0) ∨
      (first = 1 ∧ second = 4) ∨ (first = 4 ∧ second = 1) ∨
      (first = 2 ∧ second = 5) ∨ (first = 5 ∧ second = 2) := by
  rcases finSix_cases first with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finSix_cases second with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- All six vertices in the order-six construction are pairwise distinct. -/
theorem hexagon_vertices_pairwise_ne
    (star : FiniteRegularStar K 6) (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Fin 6) (different : first ≠ second) :
    regularPolygonVertexAt star initialPoint first.val ≠
      regularPolygonVertexAt star initialPoint second.val := by
  rcases hexagon_index_classification first second with same | radial | opposite
  · exact False.elim (different same)
  · exact regularPolygonVertices_ne_of_radial_nonparallel star initialPoint
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

namespace ChapterFourteenExamples.ExampleFourteenTwelve

/-- Example 14.12: a finite order-six star constructs the regular hexagon
`A₀ A₂ A₄ A₆ A₈ A₁₀`. -/
def example_14_12 (star : FiniteRegularStar K 6)
    (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (twoNonzero : (2 : K) ≠ 0) :
    ConstructedRegularPolygon K 6 where
  star := star
  initialPoint := initialPoint
  initialContains := initialContains
  initialDistinct := initialDistinct
  pairwiseVertices := hexagon_vertices_pairwise_ne star initialPoint
    initialContains initialDistinct twoNonzero

end ChapterFourteenExamples.ExampleFourteenTwelve

end DivineProportions
